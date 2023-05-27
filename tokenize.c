#include "chibicc.h"

// Input file
static File *current_file;

// A list of all input files.
static File **input_files;

// True if the current position is at the beginning of a line
static bool at_bol;

// True if the current position follows a space character
static bool has_space;

// fmt:字符串流
// 功能，错误信息输出到标准错误输出，然后结束程序
void error(char *fmt, ...) {
  va_list ap;//可变参数列表
  va_start(ap, fmt);//宏定义，可以在函数内部初始化 ap 指针，使其指向可变参数列表中的第一个参数
  vfprintf(stderr, fmt, ap);//参数：输出流，字符串流，可变参数列表
  fprintf(stderr, "\n");
  exit(1);
}

// filename：文件名
// input：文件内容
// line_no：该token的行号
// loc:该token在文件中的位置
// fmt:字符串流
// ap:可变参数列表
// 功能：输出包含错误位置的报错
static void verror_at(char *filename, char *input, int line_no,
                      char *loc, char *fmt, va_list ap) {
  // STEP1:查找包含错误位置的代码行，line是错误输入的位置，end是错误所在行的行末
  char *line = loc;
  while (input < line && line[-1] != '\n')
    line--;
  char *end = loc;
  while (*end && *end != '\n')
    end++;

  // STEP2:输出所在行内容，输出的代码行长度不超过截止位置 end 减去行首位置 line 的长度
  int indent = fprintf(stderr, "%s:%d: ", filename, line_no);
  fprintf(stderr, "%.*s\n", (int)(end - line), line);

  // STEP3:输出报错信息，位置
  int pos = loc - line + indent;
  fprintf(stderr, "%*s", pos, ""); 
  fprintf(stderr, "^ ");
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\n");
}

// loc:该token在文件中的位置
// fmt:字符串流
// 功能：查找到错误位置的行号，调用verror_at函数，输出报错信息
void error_at(char *loc, char *fmt, ...) {
  int line_no = 1;
  for (char *p = current_file->contents; p < loc; p++)
    if (*p == '\n')
      line_no++;

  va_list ap;
  va_start(ap, fmt);
  verror_at(current_file->name, current_file->contents, line_no, loc, fmt, ap);
  exit(1);
}
// tok:报错的token
// fmt:字符串流
// 功能：调用verror_at函数，输出报错信息
void error_tok(Token *tok, char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  verror_at(tok->file->name, tok->file->contents, tok->line_no, tok->loc, fmt, ap);
  exit(1);
}
// // tok:警告的token
// // fmt:字符串流
// // 功能：调用verror_at函数，输出警告信息
// void warn_tok(Token *tok, char *fmt, ...) {
//   va_list ap;
//   va_start(ap, fmt);
//   verror_at(tok->file->name, tok->file->contents, tok->line_no, tok->loc, fmt, ap);
//   va_end(ap);
// }

// 功能：比较传入的token是否等于 `op`.
bool equal(Token *tok, char *op) {
  return memcmp(tok->loc, op, tok->len) == 0 && op[tok->len] == '\0';
}

// 功能：传入的token必须等于 `op`，否则报错
// 返回下一个token : tok->next
Token *skip(Token *tok, char *op) {
  if (!equal(tok, op))
    error_tok(tok, "expected '%s'", op);
  return tok->next;
}

// 功能：如果token等于 str，返回true,rest指向 tok->next
//       否则返回false,rest指向 tok
bool consume(Token **rest, Token *tok, char *str) {
  if (equal(tok, str)) {
    *rest = tok->next;
    return true;
  }
  *rest = tok;
  return false;
}

// kind:token类型
// start:token开始的地方
// end:token结尾的地方后一位
// 功能：创建一个新的token，文件为当前文件
// 返回新建的Token
static Token *new_token(TokenKind kind, char *start, char *end) {
  Token *tok = calloc(1, sizeof(Token));
  tok->kind = kind;
  tok->loc = start;
  tok->len = end - start;
  tok->file = current_file;
  tok->at_bol = at_bol;
  tok->has_space = has_space;
  at_bol = has_space = false;
  return tok;
}

// p:文件内容
// q:指定字符串
// 返回值：bool p是否以q为开头
static bool startswith(char *p, char *q) {
  return strncmp(p, q, strlen(q)) == 0;
}

// start:文件位置指针
// 功能：读取一个标识符，检查是否合法
// 返回值：标识符长度
static int read_ident(char *start) {
  char *p = start;
  if (!is_ident1(decode_utf8(&p, p)))
    return 0;
  for (;;) {
    char *q;
    if (!is_ident2(decode_utf8(&q, p)))
      return p - start;
    p = q;
  }
}

// char c:16进制的字符
// 功能：将16进制的字符转换成10进制数值
// 返回值：int c对应的10进制数值
static int from_hex(char c) {
  if ('0' <= c && c <= '9')
    return c - '0';
  if ('a' <= c && c <= 'f')
    return c - 'a' + 10;
  return c - 'A' + 10;
}

// p:文件位置指针
// 功能：读取一个标点符号，检查是否在范围内
// 返回值：标识符长度
static int read_punct(char *p) {
  static char *kw[] = {
    "<<=", ">>=", "...", "==", "!=", "<=", ">=", "->", "+=",
    "-=", "*=", "/=", "++", "--", "%=", "&=", "|=", "^=", "&&",
    "||", "<<", ">>", "##",
  };

  for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++)
    if (startswith(p, kw[i]))
      return strlen(kw[i]);

  return ispunct(*p) ? 1 : 0;
}

// tok:输入的token
// 功能：检查是否是关键字
static bool is_keyword(Token *tok) {
  static HashMap map;

  if (map.capacity == 0) {
    static char *kw[] = {
      "return", "if", "else", "for", "while", "int", "sizeof", "char",
      "struct", "union", "short", "long", "void", "typedef", "_Bool",
      "enum", "static", "goto", "break", "continue", "switch", "case",
      "default", "extern", "_Alignof", "_Alignas", "do", "signed",
      "unsigned", "const", "volatile", "auto", "register", "restrict",
      "__restrict", "__restrict__", "_Noreturn", "float", "double",
      //"typeof", "asm", "_Thread_local", "__thread", "_Atomic","__attribute__",
    };

    for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++)
      hashmap_put(&map, kw[i], (void *)1);
  }

  return hashmap_get2(&map, tok->loc, tok->len);
}
//new_pos:\的地址
//p:\后面一位
//返回值：int
static int read_escaped_char(char **new_pos, char *p) {
  *new_pos = p + 1;
  switch (*p) {
    case 'a': return '\a';
    case 'b': return '\b';
    case 't': return '\t';
    case 'n': return '\n';
    case 'v': return '\v';
    case 'f': return '\f';
    case 'r': return '\r';
    default: return *p;
  }
}

//p:第一个双引号后一个位置的指针
//功能：找到另一个双引号
//返回值：第二个双引号位置
static char *string_literal_end(char *p) {
  char *start = p;
  for (; *p != '"'; p++) {
    if (*p == '\n' || *p == '\0')
      error_at(start, "unclosed string literal");
    if (*p == '\\')
      p++;
  }
  return p;
}

//start:第一个双引号或者u8的u位置的指针
//quote:字符串开始位置的指针
//功能：找到另一个双引号
//返回值：第二个双引号位置
static Token *read_string_literal(char *start, char *quote) {
  char *end = string_literal_end(quote + 1);
  char *buf = calloc(1, end - quote);
  int len = 0;
  //string里面的内容写到buf里面
  for (char *p = quote + 1; p < end;) {
    if (*p == '\\')
      buf[len++] = read_escaped_char(&p, p + 1);
    else
      buf[len++] = *p++;
  }
  //返回字符类型的token
  Token *tok = new_token(TK_STR, start, end + 1);//新建一个String类型的token
  tok->ty = array_of(ty_char, len + 1);
  tok->str = buf;//tok内容
  return tok;
}

//start:第一个单引号或者u8的u位置的指针
//quote:字符开始位置的指针前一个
//读取单个字符
//返回值：字符Token（数值Token）
static Token *read_char_literal(char *start, char *quote, Type *ty) {
  char *p = quote + 1;
  if (*p == '\0')
    error_at(start, "unclosed char literal");
  //字符值转换为整数
  int c;
  if (*p == '\\') //处理转义字符
    c = read_escaped_char(&p, p + 1);
  else            //处理其他字符，一律按UTF8处理
    c = decode_utf8(&p, p);

  char *end = strchr(p, '\'');
  if (!end)
    error_at(p, "unclosed char literal");

  Token *tok = new_token(TK_NUM, start, end + 1);
  tok->val = c;
  tok->ty = ty;
  return tok;
}

//tok:pp_number 
//功能：把pp_number转换成数值token,并判断是否存在非法字符或重复后缀等错误
//返回值：true
static bool convert_pp_int(Token *tok) {
  char *p = tok->loc;

  // Read a binary, octal, decimal or hexadecimal number.
  int base = 10;
  if (!strncasecmp(p, "0x", 2) && isxdigit(p[2])) {
    p += 2;
    base = 16;
  } else if (!strncasecmp(p, "0b", 2) && (p[2] == '0' || p[2] == '1')) {
    p += 2;
    base = 2;
  } else if (*p == '0') {
    base = 8;
  }

  int64_t val = strtoul(p, &p, base);

  //  后面读类型u,l
  bool l = false;
  bool u = false;
  if (*p == 'L' || *p == 'l') {
    p++;
    l = true;
  } else if (*p == 'U' || *p == 'u') {
    p++;
    u = true;
  }

  if (p != tok->loc + tok->len)
    return false;

  // 推测类型
  Type *ty;
  if (base == 10) {
    if (l && u)
      ty = ty_ulong;
    else if (l)
      ty = ty_long;
    else if (u)
      ty = (val >> 32) ? ty_ulong : ty_uint;
    else
      ty = (val >> 31) ? ty_long : ty_int;
  } else {
    if (l && u)
      ty = ty_ulong;
    else if (l)
      ty = (val >> 63) ? ty_ulong : ty_long;
    else if (u)
      ty = (val >> 32) ? ty_ulong : ty_uint;
    else if (val >> 63)
      ty = ty_ulong;
    else if (val >> 32)
      ty = ty_long;
    else if (val >> 31)
      ty = ty_uint;
    else
      ty = ty_int;
  }

  tok->kind = TK_NUM;
  tok->val = val;
  tok->ty = ty;
  return true;
}
// tok:token输入流
// 把预处理数字pp_number转换成正常的数字token
static void convert_pp_number(Token *tok) {
  // 解析一个整数常数
  if (convert_pp_int(tok))
    return;
  // 解析一个浮点数
  char *end;
  double val = strtold(tok->loc, &end);//需要转换的字符串指针，end参数表示转换后停止的位置，
  Type *ty;
  if (*end == 'f' || *end == 'F') {
    ty = ty_float;
    end++;
  } else if (*end == 'l' || *end == 'L') {
    ty = ty_double;
    end++;
  } else {
    ty = ty_double;
  }

  if (tok->loc + tok->len != end)
    error_tok(tok, "invalid numeric constant");

  tok->kind = TK_NUM;
  tok->fval = val;
  tok->ty = ty;
}
//tok:待处理token
//功能：是否是关键字，不是的话转换成预处理数字
void convert_pp_tokens(Token *tok) {
  for (Token *t = tok; t->kind != TK_EOF; t = t->next) {
    if (is_keyword(t))
      t->kind = TK_KEYWORD;
    else if (t->kind == TK_PP_NUM)
      convert_pp_number(t);
  }
}

// tok：当前处理的token
// 功能：给
static void add_line_numbers(Token *tok) {
  char *p = current_file->contents;
  int n = 1;

  do {
    if (p == tok->loc) {
      tok->line_no = n;
      tok = tok->next;
    }
    if (*p == '\n')
      n++;
  } while (*p++);
}

//file 文件
// 把文件转换成token流
Token *tokenize(File *file) {
  current_file = file;//记录当前处理文件
  char *p = file->contents;//p文件内容
  
  Token head = {};
  Token *cur = &head;
  at_bol = true;
  has_space = false;

  while (*p) {
    // case1:跳过注释
    if (startswith(p, "//")) {
      p += 2;
      while (*p != '\n')
        p++;
      has_space = true;
      continue;
    }
    // case2:跳过块注释
    if (startswith(p, "/*")) {
      char *q = strstr(p + 2, "*/");
      if (!q)
        error_at(p, "unclosed block comment");
      p = q + 2;
      has_space = true;
      continue;
    }
    // case3:跳过空行
    if (*p == '\n') {
      p++;
      at_bol = true;
      has_space = false;
      continue;
    }
    // case4:跳过空格
    if (isspace(*p)) {
      p++;
      has_space = true;
      continue;
    }
    // case5:数字字符
    if (isdigit(*p) || (*p == '.' && isdigit(p[1]))) {
      char *q = p++;
      for (;;) {
        if (isalnum(*p) || *p == '.')//为字母a-z A-Z或者数字0-9
          p++;
        else
          break;
      }
      cur = cur->next = new_token(TK_PP_NUM, q, p);
      continue;
    }
    // case6:字符串
    if (*p == '"') {
      cur = cur->next = read_string_literal(p, p);
      p += cur->len;
      continue;
    }
    // case7:UTF-8 字符串
    if (startswith(p, "u8\"")) {
      cur = cur->next = read_string_literal(p, p + 2);
      p += cur->len;
      continue;
    }
    // case8：字符
    if (*p == '\'') {
      cur = cur->next = read_char_literal(p, p, ty_int);
      cur->val = (char)cur->val;
      p += cur->len;
      continue;
    }

    // case9:标识符
    int ident_len = read_ident(p);
    if (ident_len) {
      cur = cur->next = new_token(TK_IDENT, p, p + ident_len);
      p += cur->len;
      continue;
    }

    // case10:标点符号
    int punct_len = read_punct(p);
    if (punct_len) {
      cur = cur->next = new_token(TK_PUNCT, p, p + punct_len);
      p += cur->len;
      continue;
    }

    error_at(p, "invalid token");
  }

  cur = cur->next = new_token(TK_EOF, p, p);
  add_line_numbers(head.next);
  return head.next;
}


// path:文件路径
// 功能：读取文件内容，规范尾部结束内容
// 返回值：char* 文件内容

static char *read_file(char *path)
{
    // STEP1 获取文件指针
    FILE *fp;
    if (strcmp(path, "-") == 0){
        // By convention, read from stdin if a given filename is "-".
        fp = stdin;
    }
    else{
        fp = fopen(path, "r");
        if (!fp) // 打开后没有内容
            return NULL;
    }

    char *buf;      // 指向开辟的缓冲区
    size_t bufsize; // 缓冲区大小，可调整
    FILE *stream = open_memstream(&buf, &bufsize);

    // STEP2 读取文件内容，每次读取 4096字节的内容
    for (;;)
    {
        char block[4096];
        int n = fread(block, 1, sizeof(block), fp); // 数据块的大小,数据块数量，已经打开的文件流的指针
        if (n == 0)                                 // 写到block中，返回读取到的数据块数量
            break;
        fwrite(block, 1, n, stream); // block中内容写到stream指向的缓冲区
    }
    // STEP3 关闭文件指针
    if (fp != stdin)
        fclose(fp);
    fflush(stream);
    // STEP4 确保文件以\n\0结尾，缓冲区数据更新到磁盘
    if (bufsize == 0 || buf[bufsize - 1] != '\n')
        fputc('\n', stream); // 最后一行以\n结尾
    fputc('\0', stream);
    fclose(stream);
    return buf;
}

//返回文件序列
File **get_input_files(void) {
  return input_files;
}
// name:文件路径(名)
// file_no:文件编号
// contents* :文件内容
// 返回值：File
File *new_file(char *name, int file_no, char *contents) {
  File *file = calloc(1, sizeof(File));
  file->name = name;
  file->display_name = name;
  file->file_no = file_no;
  file->contents = contents;
  return file;
}


// path:文件内容指针
// 功能：将字符串中的Windows风格的换行符"\r\n"或回车符"\r"转换成Unix风格的换行符"\n"
// 返回值：void
static void canonicalize_newline(char *p)
{
    int i = 0, j = 0;
    char *temp = (char *)malloc(strlen(p) + 1); // 为了更好的处理不更新的情况，需要额外的数组

    while (p[i])
    {
        if (p[i] == '\r')
        {
            if (p[i + 1] == '\n')
            {
                i += 2; // Windows-style \r\n
                temp[j++] = '\n';
            }
            else
            {
                i++; // Old Macintosh-style \r
                temp[j++] = '\n';
            }
        }
        else
        {
            temp[j++] = p[i++];
        }
    }
    temp[j] = '\0';

    if (strcmp(temp, p) != 0)
    { // 如果有更新，才更新原来的字符串
        strcpy(p, temp);
    }

    free(temp);
}

// p:文件内容指针
// 功能：将字符串中的连续换行\\n跳过，并同步行数
// 返回值：void
static void remove_backslash_newline(char *p) {
  int i = 0, j = 0, n = 0;
  while (p[i]) {
    if (p[i] == '\\' && p[i + 1] == '\n') {
      i += 2;
      n++;
    } else if (p[i] == '\n') {
      p[j++] = p[i++];
      for (; n > 0; n--)
        p[j++] = '\n';
    } else {
      p[j++] = p[i++];
    }
  }
  for (; n > 0; n--)
    p[j++] = '\n';
  p[j] = '\0';
}

// p:文件内容指针
// 功能：从字符串中解析 Unicode 码点，转成32位整数
// 返回值：uint32_t
static uint32_t read_universal_char(const char *p) {
  uint32_t c = 0;
  for (int i = 0; i < 4; i++) {
    if (!isxdigit(p[i]))
      return 0;
    c = (c << 4) | from_hex(p[i]);
  }
  return c;
}

// p:文件内容指针
// 功能:处理\u字符
static void convert_universal_chars(char *p) {
  char *q = p;
  while (*p) {
    if (startswith(p, "\\u")) {//如果是Unicode码点，就转换成32位整数
      uint32_t c = read_universal_char(p + 2);
      if (c) {
        p += 6;
        q += encode_utf8(q, c);
      } else {
        *q++ = *p++;
      }
    } 
    else if (p[0] == '\\') {//如果是普通转义字符，读入
      *q++ = *p++;
      *q++ = *p++;
    } else {//如果是普通字符，直接读入
      *q++ = *p++;
    }
  }

  *q = '\0';
}

//path：文件路径
//返回值：token序列
//对外调用接口
Token *tokenize_file(char *path) {
  char *p = read_file(path);
  if (!p) return NULL;
  // 规范化，移除连续换行符，转换unicode码点
  canonicalize_newline(p);
  remove_backslash_newline(p);
  convert_universal_chars(p);

  // 保存文件名，存放到input_files中
  static int file_no;
  File *file = new_file(path, file_no + 1, p);
  input_files = realloc(input_files, sizeof(char *) * (file_no + 2));
  input_files[file_no] = file;
  input_files[file_no + 1] = NULL;
  file_no++;
  // 序列化文件
  return tokenize(file);
}
