#include "chibicc.h"

// 预处理阶段任务：

// 第一次扫描：
// 处理 #include 指令。读取指定的头文件，将其内容插入到当前文件中。
//     如果是系统头文件，则从系统路径中查找文件；
//     如果是用户自定义的头文件，则从当前目录或指定的目录中查找文件。预处理器会递归地处理被包含的头文件，直到所有的头文件都被处理为止。
// 处理 #define`宏定义,判断条件
//     处理带参数的宏和不带参数的宏，
//     处理条件编译指令`#ifdef`、`#ifndef`、`#if`、`#else` 和 `#endif`
//     处理 `#undef`、`#line`、`#error` 预处理指令。
// 第二次扫描：
// 处理预处理指令和宏定义生成的实际代码
//     将所有的预处理数字类型（TK_PP_NUM）的token转换成真正的数字类型(TK_NUM)


//宏定义参数,只有name和next
typedef struct MacroParam MacroParam;
struct MacroParam {
  MacroParam *next;
  char *name;
};
//宏定义参数,有对应的token和是否是动态的参数
typedef struct MacroArg MacroArg;
struct MacroArg {
  MacroArg *next;
  char *name;
  Token *tok;
};

typedef Token *macro_handler_fn(Token *);//函数指针，传入是Token*,返回值也是Token*

typedef struct Macro Macro;
struct Macro {
  char *name;
  bool is_objlike; // Object-like or function-like
  MacroParam *params;
  //char *va_args_name;
  bool is_variadic;

  Token *body;
  macro_handler_fn *handler;
};

// `#if` can be nested, so we use a stack to manage nested `#if`s.
typedef struct CondIncl CondIncl;
struct CondIncl {
  CondIncl *next;
  enum { IN_THEN, IN_ELIF, IN_ELSE } ctx;
  Token *tok;
  bool included;
};

static HashMap macros;//c++
static CondIncl *cond_incl;
static Token *preprocess2(Token *tok);
static Macro *find_macro(Token *tok);

//tok:必须是行首的#
static bool is_hash(Token *tok) {
  return tok->at_bol && equal(tok, "#");
}

//单纯复制当前的token,指向下一个为null
static Token *copy_token(Token *tok) {
  Token *t = calloc(1, sizeof(Token));
  *t = *tok;
  t->next = NULL;
  return t;
}
//新建一个EOF Token
static Token *new_eof(Token *tok) {
  Token *t = copy_token(tok);
  t->kind = TK_EOF;
  t->len = 0;
  return t;
}



// Append tok2 to the end of tok1.
static Token *append(Token *tok1, Token *tok2) {
  if (tok1->kind == TK_EOF)
    return tok2;

  Token head = {};
  Token *cur = &head;

  for (; tok1->kind != TK_EOF; tok1 = tok1->next)
    cur = cur->next = copy_token(tok1);
  cur->next = tok2;
  return head.next;
}

//tok:传入的token
//功能：跳过中间的#if #endif ，确保skip_cond_incl中跳过的#endif对应正确
static Token *skip_cond_incl2(Token *tok) {
  while (tok->kind != TK_EOF) {//如果中间还有#if #endif 跳过
    if (is_hash(tok) &&
        (equal(tok->next, "if") || equal(tok->next, "ifdef") ||
         equal(tok->next, "ifndef"))) {
      tok = skip_cond_incl2(tok->next->next);
      continue;
    }//要删掉的那一段#if #endif
    if (is_hash(tok) && equal(tok->next, "endif"))
      return tok->next->next;
    tok = tok->next;
  }
  return tok;
}

// tok: #if,#ifdef,#ifndef,#elif,#else 
// 功能：跳过这一段条件编译（#if #endif）,以及中间所有的条件编译（#if #endif）
static Token *skip_cond_incl(Token *tok) {
  while (tok->kind != TK_EOF) {
    if (is_hash(tok) &&
        (equal(tok->next, "if") || equal(tok->next, "ifdef") ||
         equal(tok->next, "ifndef"))) {//如果中间有条件编译段，跳过
      tok = skip_cond_incl2(tok->next->next);
      continue;
    }
    //第一个#endif,#elif,#else,标志前面的内容省略
    if (is_hash(tok) &&
        (equal(tok->next, "elif") || equal(tok->next, "else") ||
         equal(tok->next, "endif")))
      break;
    tok = tok->next;
  }
  return tok;
}

// 给一个string加上双引号后返回
static char *quote_string(char *str) {
  int bufsize = 3;
  for (int i = 0; str[i]; i++) {//先计算size,遇到\,"，要多加一次，因为表示的时候需要转义
    if (str[i] == '\\' || str[i] == '"')
      bufsize++;
    bufsize++;
  }

  char *buf = calloc(1, bufsize);
  char *p = buf;
  *p++ = '"';
  for (int i = 0; str[i]; i++) {//把里面的\,"，进行转义表示
    if (str[i] == '\\' || str[i] == '"')
      *p++ = '\\';
    *p++ = str[i];
  }
  *p++ = '"';
  *p++ = '\0';
  return buf;
}

//新建一个string类型的token,把str里面的内容用双引号包括起来
static Token *new_str_token(char *str, Token *tmpl) {
  char *buf = quote_string(str);
  return tokenize(new_file(tmpl->file->name, tmpl->file->file_no, buf));
}

// rest: &("define"token)
// tok: #define IDENTIFIER 后面的token 
// 复制tok后面所有的token，直到换行，并且token序列尾部加上EOF
static Token *copy_line(Token **rest, Token *tok) {
  Token head = {};
  Token *cur = &head;

  for (; !tok->at_bol; tok = tok->next)
    cur = cur->next = copy_token(tok);

  cur->next = new_eof(tok);
  *rest = tok;
  return head.next;
}

//新建一个num类型的token
static Token *new_num_token(int val, Token *tmpl) {
  char *buf = format("%d\n", val);
  return tokenize(new_file(tmpl->file->name, tmpl->file->file_no, buf));
}

static Token *read_const_expr(Token **rest, Token *tok) {
  tok = copy_line(rest, tok);

  Token head = {};
  Token *cur = &head;

  while (tok->kind != TK_EOF) {
    // #if defined () 
    if (equal(tok, "defined")) {
      Token *start = tok;
      bool has_paren = consume(&tok, tok->next, "(");
      if (tok->kind != TK_IDENT)
        error_tok(start, "macro name must be an identifier");
      Macro *m = find_macro(tok);
      tok = tok->next;
      if (has_paren) tok = skip(tok, ")");
      //如果已经定义过，m不为空，条件值是1，否则0
      cur = cur->next = new_num_token(m ? 1 : 0, start);
      continue;
    }

    cur = cur->next = tok;
    tok = tok->next;
  }

  cur->next = tok;
  return head.next;
}

// 获取条件值 
// tok：if ，elif 
static long eval_const_expr(Token **rest, Token *tok) {
  Token *start = tok;
  Token *expr = read_const_expr(rest, tok->next);//?
  expr = preprocess2(expr);//再进行预处理，看要不要编译

  if (expr->kind == TK_EOF)
    error_tok(start, "no expression");

  // 如果碰到没有定义过的宏，则直接替换成0
  for (Token *t = expr; t->kind != TK_EOF; t = t->next) {
    if (t->kind == TK_IDENT) {
      Token *next = t->next;
      *t = *new_num_token(0, t);
      t->next = next;
    }
  }
  // 把预处理过的number转换成真正的数字
  convert_pp_tokens(expr);
  Token *rest2;
  //调用parse中的函数，获得表达式的值，返回表达式的值
  long val = const_expr(&rest2, expr);
  if (rest2->kind != TK_EOF)
    error_tok(rest2, "extra token");
  return val;
}
//相当于一个栈，push，new->old
static CondIncl *push_cond_incl(Token *tok, bool included) {
  CondIncl *ci = calloc(1, sizeof(CondIncl));
  ci->next = cond_incl;
  ci->ctx = IN_THEN;//?
  ci->tok = tok;
  ci->included = included;//?
  cond_incl = ci;
  return ci;
}
//在macros中根据token找宏，返回结果
static Macro *find_macro(Token *tok) {
  if (tok->kind != TK_IDENT )
    return NULL;
  return hashmap_get2(&macros, tok->loc, tok->len);//c++
}
//name:宏定义的名称
//is_objlike:是否是类对象宏
//body:要替换名称的部分Token
//添加一个宏
static Macro *add_macro(char *name, bool is_objlike, Token *body) {
  Macro *m = calloc(1, sizeof(Macro));
  m->name = name;
  m->is_objlike = is_objlike;
  m->body = body;
  hashmap_put(&macros, name, m);//c++
  return m;
}

// rest: &(#define "("token)
// tok: "("后面的内容token
// is_variadic:参数是否可变
// 读宏定义参数，返回参数链表
static MacroParam *read_macro_params(Token **rest, Token *tok, bool *is_variadic) {
  MacroParam head = {};
  MacroParam *cur = &head;

  while (!equal(tok, ")")) {
    if (cur != &head)
      tok = skip(tok, ",");

    if (equal(tok, "...")) {
      *is_variadic = true;
      *rest = skip(tok->next, ")");
      return head.next;
    }

    if (tok->kind != TK_IDENT)
      error_tok(tok, "expected an identifier");

    MacroParam *m = calloc(1, sizeof(MacroParam));
    m->name = strndup(tok->loc, tok->len);
    cur = cur->next = m;
    tok = tok->next;
  }

  *rest = tok->next;
  return head.next;
}

// rest: &("define"token)
// tok: #define后面的内容token
// 读宏定义
static void read_macro_definition(Token **rest, Token *tok) {
  //STEP1:读变量名
  if (tok->kind != TK_IDENT)
    error_tok(tok, "macro name must be an identifier");
  char *name = strndup(tok->loc, tok->len);
  tok = tok->next;
  //STEP2:读宏定义后面部分
  // 非类对象，带参数的宏定义
  if (!tok->has_space && equal(tok, "(")) {
    bool is_variadic = false;
    MacroParam *params = read_macro_params(&tok, tok->next, &is_variadic);
    Macro *m = add_macro(name, false, copy_line(rest, tok));
    m->params = params;
    m->is_variadic = is_variadic;//是否是可变参数
  } else {
    // 类对象的宏定义
    add_macro(name, true, copy_line(rest, tok));
  }
}

//遇到逗号前，读一次参数，返回参数列表arg，并保存了参数对应的token(arg->tok)，和下一个处理的token的位置（rest）
static MacroArg *read_macro_arg_one(Token **rest, Token *tok, bool read_rest) {
  Token head = {};
  Token *cur = &head;
  int level = 0;

  for (;;) {
    if (level == 0 && equal(tok, ")"))
      break;
    if (level == 0 && !read_rest && equal(tok, ","))
      break;

    if (tok->kind == TK_EOF)
      error_tok(tok, "premature end of input");

    if (equal(tok, "("))
      level++;
    else if (equal(tok, ")"))
      level--;

    cur = cur->next = copy_token(tok);
    tok = tok->next;
  }

  cur->next = new_eof(tok);

  MacroArg *arg = calloc(1, sizeof(MacroArg));
  arg->tok = head.next;
  *rest = tok;
  return arg;
}
//展开函数宏的时候，读参数
static MacroArg *
read_macro_args(Token **rest, Token *tok, MacroParam *params,  bool is_variadic) {
  Token *start = tok;
  tok = tok->next->next;

  MacroArg head = {};
  MacroArg *cur = &head;

  MacroParam *pp = params;
  for (; pp; pp = pp->next) {
    if (cur != &head)
      tok = skip(tok, ",");
    cur = cur->next = read_macro_arg_one(&tok, tok, false);
    cur->name = pp->name;
  }

  if (is_variadic) {
    MacroArg *arg;
    if (equal(tok, ")")) {
      arg = calloc(1, sizeof(MacroArg));
      arg->tok = new_eof(tok);
    } else {
      if (pp != params)
        tok = skip(tok, ",");
      arg = read_macro_arg_one(&tok, tok, true);
    }
    arg->name = "__VA_ARGS__";
    cur = cur->next = arg;
  } else if (pp) {
    error_tok(start, "too many arguments");
  }

  skip(tok, ")");
  *rest = tok;
  return head.next;
}
//在args中找tok对应的参数，找到后返回该参数
static MacroArg *find_arg(MacroArg *args, Token *tok) {
  for (MacroArg *ap = args; ap; ap = ap->next)
    if (tok->len == strlen(ap->name) && !strncmp(tok->loc, ap->name, tok->len))
      return ap;
  return NULL;
}

// tok 和end之间的tokenu串联合并
static char *join_tokens(Token *tok, Token *end) {
  // Compute the length of the resulting token.
  int len = 1;
  for (Token *t = tok; t != end && t->kind != TK_EOF; t = t->next) {
    if (t != tok && t->has_space)
      len++;
    len += t->len;
  }
  char *buf = calloc(1, len);

  // Copy token texts.
  int pos = 0;
  for (Token *t = tok; t != end && t->kind != TK_EOF; t = t->next) {
    if (t != tok && t->has_space)
      buf[pos++] = ' ';
    strncpy(buf + pos, t->loc, t->len);
    pos += t->len;
  }
  buf[pos] = '\0';
  return buf;
}

// arg中所有的token都连接起来，返回一个 string token.
static Token *stringize(Token *hash, Token *arg) {
  char *s = join_tokens(arg, NULL);
  return new_str_token(s, hash);
}

// Concatenate two tokens to create a new token.
static Token *paste(Token *lhs, Token *rhs) {
  // Paste the two tokens.
  char *buf = format("%.*s%.*s", lhs->len, lhs->loc, rhs->len, rhs->loc);

  // Tokenize the resulting string.
  Token *tok = tokenize(new_file(lhs->file->name, lhs->file->file_no, buf));
  if (tok->next->kind != TK_EOF)
    error_tok(lhs, "pasting forms '%s', an invalid token", buf);
  return tok;
}

// 用参数替代宏里面的变量
// tok:m->body 宏里面的变量
// args:参数
static Token *subst(Token *tok, MacroArg *args) {
  Token head = {};
  Token *cur = &head;

  while (tok->kind != TK_EOF) {
    //字符串化后面的参数 #abcd...
    if (equal(tok, "#")) {
      MacroArg *arg = find_arg(args, tok->next);//找到参数
      if (!arg)
        error_tok(tok->next, "'#' is not followed by a macro parameter");
      cur = cur->next = stringize(tok, arg->tok);
      tok = tok->next->next;
      continue;
    }
    //把两个参数连接起来 a##b
    if (equal(tok, "##")) {
      if (cur == &head)
        error_tok(tok, "'##' cannot appear at start of macro expansion");

      if (tok->next->kind == TK_EOF)
        error_tok(tok, "'##' cannot appear at end of macro expansion");

      MacroArg *arg = find_arg(args, tok->next);//找到##后面的参数
      if (arg) {
        if (arg->tok->kind != TK_EOF) {
          *cur = *paste(cur, arg->tok);//把前后连接起来，省略##
          for (Token *t = arg->tok->next; t->kind != TK_EOF; t = t->next)
            cur = cur->next = copy_token(t);//参数列表中的token
        }
        tok = tok->next->next;
        continue;
      }
      //如果没有找到参数直接把前后的tok连起来成为一个token
      *cur = *paste(cur, tok->next);
      tok = tok->next->next;
      continue;
    }
    //正常情况下替换参数，第一步，找到对应的参数
    MacroArg *arg = find_arg(args, tok);

    //第二步，参数对应的token预处理一遍后依次加入到cur中
    if (arg) {
      Token *t = preprocess2(arg->tok);//参数对应的token再预处理一遍
      t->at_bol = tok->at_bol;
      t->has_space = tok->has_space;
      for (; t->kind != TK_EOF; t = t->next)
        cur = cur->next = copy_token(t);
      tok = tok->next;
      continue;
    }

    // 如果没有参数,也就是不是宏，那就加入cur后，直接往后走
    cur = cur->next = copy_token(tok);
    tok = tok->next;
    continue;
  }
  // tok->kind == TK_EOF
  cur->next = tok;
  return head.next;
}

// rest:token位置
// tok:token流开始的地方
// 函数功能：宏展开
static bool expand_macro(Token **rest, Token *tok) {

  Macro *m = find_macro(tok);
  if (!m)
    return false;

  // Built-in 宏，如果有handler，则先用handler处理
  if (m->handler) {
    *rest = m->handler(tok);
    (*rest)->next = tok->next;
    return true;
  }

  // 类对象宏
  if (m->is_objlike) {
    Token *body = m->body;

    for (Token *t = body; t->kind != TK_EOF; t = t->next)
      t->origin = tok;//设置所有宏的参数的token的宏token
    *rest = append(body, tok->next);
    (*rest)->at_bol = tok->at_bol;
    (*rest)->has_space = tok->has_space;
    return true;
  }

  // 函数宏，但是没有参数，宏展开不处理
  if (!equal(tok->next, "("))
    return false;

  // 函数宏 tok:macro (x,y..
  Token *macro_token = tok;
  MacroArg *args = read_macro_args(&tok, tok, m->params, m->is_variadic);
  Token *body = subst(m->body, args);//用到宏的地方展开
  for (Token *t = body; t->kind != TK_EOF; t = t->next)
    t->origin = macro_token;
  *rest = append(body, tok->next);
  (*rest)->at_bol = macro_token->at_bol;
  (*rest)->has_space = macro_token->has_space;
  return true;
}
// filename:文件名
// 功能：在头文件库里面查找文件的路径
//       路径有效则返回路径，否则返回null
char *search_include_paths(char *filename) {
  if (filename[0] == '/')
    return filename;

  // Search a file from the include paths.
  for (int i = 0; i < include_paths.len; i++) {
    char *path = format("%s/%s", include_paths.data[i], filename);
    if (file_exists(path))
      return path;
  }
  return NULL;
}


// Read an #include argument.
static char *read_include_filename(Token **rest, Token *tok, bool *is_dquote) {
  // Pattern 1: #include "foo.h"
  if (tok->kind == TK_STR) {
    //不解释文件名中任何转义序列
    *is_dquote = true;
    //*rest = skip_line(tok->next);
    *rest = tok->next;
    return strndup(tok->loc + 1, tok->len - 2);
  }

  // Pattern 2: #include <foo.h>
  if (equal(tok, "<")) {
    //读文件名 "<" and ">".
    Token *start = tok;

    // Find closing ">".
    for (; !equal(tok, ">"); tok = tok->next)
      if (tok->at_bol || tok->kind == TK_EOF)
        error_tok(tok, "expected '>'");

    *is_dquote = false;
    //*rest = skip_line(tok->next);
    *rest = tok->next;
    return join_tokens(start->next, tok);//文件名要连起来
  }

  // // Pattern 3: #include FOO
  // // In this case FOO must be macro-expanded to either
  // // a single string token or a sequence of "<" ... ">".
  // if (tok->kind == TK_IDENT) {
  //   Token *tok2 = preprocess2(copy_line(rest, tok));
  //   return read_include_filename(&tok2, tok2, is_dquote);
  // }

  error_tok(tok, "expected a filename");
}

//tok:"include"token
//path:头文件路径
//filename_tok:头文件名token
//功能：展开头文件，tokenize,插入到当前token后面
static Token *include_file(Token *tok, char *path, Token *filename_tok) {
  Token *tok2 = tokenize_file(path);//tokenize头文件
  if (!tok2)
    error_tok(filename_tok, "%s: cannot open file: %s", path, strerror(errno));

  return append(tok2, tok);//将新的token流插入到当前token后面
}


// tok:token流
// 功能：
//    展开头文件：#include
//    预处理指令判断：`#ifdef`、`#ifndef`、`#if`、`#else` 和 `#endif`
//    宏定义：#define
//    报错：error
static Token *preprocess2(Token *tok) {
  Token head = {};
  Token *cur = &head;

  while (tok->kind != TK_EOF) {
    // 宏展开
    if (expand_macro(&tok, tok))
      continue;

    // 确保读入"#"，否则continue
    if (!is_hash(tok)) {
      cur = cur->next = tok;
      tok = tok->next;
      continue;
    }
    // start从#后面一个token开始
    Token *start = tok;
    tok = tok->next;
    //case1:#include
    if (equal(tok, "include")) {
      bool is_dquote;
      //STEP1:读取文件名，获取文件类型
      char *filename = read_include_filename(&tok, tok->next, &is_dquote);
      //STEP2:展开文件内容，tokenize,添加到文件名token后面
      // 如果是自定义头文件 ""
      if (filename[0] != '/' && is_dquote) {
        char *path = format("%s/%s", dirname(strdup(start->file->name)), filename);
        if (file_exists(path)) {
          tok = include_file(tok, path, start->next->next);
          continue;
        }
      }
      // 如果是标准库头文件<>
      char *path = search_include_paths(filename);//在头文件库里面找路径
      tok = include_file(tok, path ? path : filename, start->next->next);
      continue;
    }
    
    //case2:#define
    if (equal(tok, "define")) {
      read_macro_definition(&tok, tok->next);
      continue;
    }
    //case3:#undef
    if (equal(tok, "undef")) {
      tok = tok->next;
      if (tok->kind != TK_IDENT)
        error_tok(tok, "macro name must be an identifier");
      undef_macro(strndup(tok->loc, tok->len));//取消一个宏定义
      tok = tok->next;
      continue;
    }
    
    //case4:#if
    if (equal(tok, "if")) {
      long val = eval_const_expr(&tok, tok);//获取表达式的值，决定是否要编译
      push_cond_incl(tok, val); //用栈保存这个#if（token start）
      if (!val)
        tok = skip_cond_incl(tok);//跳过这一段#if #endif
      continue;
    }
    //case5:#ifdef
    if (equal(tok, "ifdef")) {
      bool defined = find_macro(tok->next);//是否定义过这个宏
      push_cond_incl(tok, defined);//用栈保存这个#ifdef
      tok = tok->next->next;
      if (!defined)//没有定义过的话，就跳过
        tok = skip_cond_incl(tok);
      continue;
    }
    //case6:#ifndef
    if (equal(tok, "ifndef")) {
      bool defined = find_macro(tok->next);
      push_cond_incl(tok, !defined);
      //tok = skip_line(tok->next->next);
      tok = tok->next->next;
      if (defined)
        tok = skip_cond_incl(tok);
      continue;
    }
    //case7:#elif
    if (equal(tok, "elif")) {
      if (!cond_incl || cond_incl->ctx == IN_ELSE)
        error_tok(start, "stray #elif");
      cond_incl->ctx = IN_ELIF;

      if (!cond_incl->included && eval_const_expr(&tok, tok))
        cond_incl->included = true;
      else
        tok = skip_cond_incl(tok);
      continue;
    }
    //case8:#else
    if (equal(tok, "else")) {
      if (!cond_incl || cond_incl->ctx == IN_ELSE)
        error_tok(start, "stray #else");
      cond_incl->ctx = IN_ELSE;
      //tok = skip_line(tok->next);
      tok = tok->next;
      if (cond_incl->included)
        tok = skip_cond_incl(tok);
      continue;
    }
    //case9:#endif
    if (equal(tok, "endif")) {
      if (!cond_incl)
        error_tok(start, "stray #endif");
      cond_incl = cond_incl->next;
      //tok = skip_line(tok->next);
      tok = tok->next;
      continue;
    }

    error_tok(tok, "invalid preprocessor directive");
  }

  cur->next = tok;
  return head.next;
}

//定义一个宏，全部保存在<built-in>中
void define_macro(char *name, char *buf) {
  Token *tok = tokenize(new_file("<built-in>", 1, buf));
  add_macro(name, true, tok);
}

//name：宏定义的name
//功能：删除该宏定义
void undef_macro(char *name) {
  hashmap_remove(&macros, name);
  //c++
}

//返回一个宏指针，该宏为："_FILE_",macro_handler_fn:返回文件名
static Macro *add_builtin(char *name, macro_handler_fn *fn) {
  Macro *m = add_macro(name, true, NULL);
  m->handler = fn;
  return m;
}

//文件名的宏，返回string类型的token
static Token *file_macro(Token *tmpl) {
  while (tmpl->origin)
    tmpl = tmpl->origin;
  return new_str_token(tmpl->file->name, tmpl);
}

//宏定义初始化
void init_macros(void) {
  // Define predefined macros
  define_macro("_LP64", "1");
  define_macro("__C99_MACRO_WITH_VA_ARGS", "1");
  define_macro("__ELF__", "1");
  define_macro("__LP64__", "1");
  define_macro("__SIZEOF_DOUBLE__", "8");
  define_macro("__SIZEOF_FLOAT__", "4");
  define_macro("__SIZEOF_INT__", "4");
  define_macro("__SIZEOF_LONG__", "8");
  define_macro("__SIZEOF_POINTER__", "8");
  define_macro("__SIZEOF_PTRDIFF_T__", "8");
  define_macro("__SIZEOF_SHORT__", "2");
  define_macro("__SIZEOF_SIZE_T__", "8");
  define_macro("__SIZE_TYPE__", "unsigned long");
  define_macro("__STDC_HOSTED__", "1");
  define_macro("__STDC_VERSION__", "201112L");
  define_macro("__STDC__", "1");
  define_macro("__USER_LABEL_PREFIX__", "");
  define_macro("__alignof__", "_Alignof");
  define_macro("__amd64", "1");
  define_macro("__amd64__", "1");
  define_macro("__chibicc__", "1");
  define_macro("__const__", "const");
  define_macro("__gnu_linux__", "1");
  define_macro("__inline__", "inline");
  define_macro("__linux", "1");
  define_macro("__linux__", "1");
  define_macro("__signed__", "signed");
  define_macro("__typeof__", "typeof");
  define_macro("__unix", "1");
  define_macro("__unix__", "1");
  define_macro("__volatile__", "volatile");
  define_macro("__x86_64", "1");
  define_macro("__x86_64__", "1");
  define_macro("linux", "1");
  define_macro("unix", "1");
  add_builtin("__FILE__", file_macro);
}


// tok:token流
// 对token流进行预处理指令判断，宏展开
Token *preprocess(Token *tok) {
  //第一次扫描，展开宏，处理预处理指令
  tok = preprocess2(tok);
  //检查预处理指令里面if-elif-endif是否封闭
  if (cond_incl)
    error_tok(cond_incl->tok, "unterminated conditional directive");
  //第二次扫描，转换预处理第一次扫描后的关键字or浮点数or整数
  convert_pp_tokens(tok);
  return tok;
}
