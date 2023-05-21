#include "chibicc.h"

// buf:utf8的值
// c:32位整数
// 返回值，utf8的值的位数
int encode_utf8(char *buf, uint32_t c) {
  if (c <= 0x7F) {
    buf[0] = c;
    return 1;
  }

  if (c <= 0x7FF) {
    buf[0] = 0b11000000 | (c >> 6);
    buf[1] = 0b10000000 | (c & 0b00111111);
    return 2;
  }

  if (c <= 0xFFFF) {
    buf[0] = 0b11100000 | (c >> 12);
    buf[1] = 0b10000000 | ((c >> 6) & 0b00111111);
    buf[2] = 0b10000000 | (c & 0b00111111);
    return 3;
  }

  buf[0] = 0b11110000 | (c >> 18);
  buf[1] = 0b10000000 | ((c >> 12) & 0b00111111);
  buf[2] = 0b10000000 | ((c >> 6) & 0b00111111);
  buf[3] = 0b10000000 | (c & 0b00111111);
  return 4;
}

// new_pos：文件位置
// p:UTF编码文件
// 返回值：32位整数
uint32_t decode_utf8(char **new_pos, char *p) {
  if ((unsigned char)*p < 128) {//ASCII码，1byte，直接返回
    *new_pos = p + 1;
    return *p;
  }
  //非ASCII码，若干byte，返回处理后的32位整数
  char *start = p;
  int len;
  uint32_t c;

  if ((unsigned char)*p >= 0b11110000) {
    len = 4;
    c = *p & 0b111;
  } else if ((unsigned char)*p >= 0b11100000) {
    len = 3;
    c = *p & 0b1111;
  } else if ((unsigned char)*p >= 0b11000000) {
    len = 2;
    c = *p & 0b11111;
  } else {
    error_at(start, "invalid UTF-8 sequence");
  }

  for (int i = 1; i < len; i++) {
    if ((unsigned char)p[i] >> 6 != 0b10)
      error_at(start, "invalid UTF-8 sequence");
    c = (c << 6) | (p[i] & 0b111111);
  }

  *new_pos = p + len;
  return c;
}

// range：字符范围
// c:32位整数
// 返回值：是否在范围内
static bool in_range(uint32_t *range, uint32_t c) {
  for (int i = 0; range[i] != -1; i += 2)
    if (range[i] <= c && c <= range[i + 1])
      return true;
  return false;
}

// c:32位整数
// 功能： 标识符第一个字符的是否有效
// 返回值：是否在范围内
bool is_ident1(uint32_t c) {
  static uint32_t range[] = {
    '_', '_', 'a', 'z', 'A', 'Z', '$', '$',
    0x00A8, 0x00A8, 0x00AA, 0x00AA, 0x00AD, 0x00AD, 0x00AF, 0x00AF,
    0x00B2, 0x00B5, 0x00B7, 0x00BA, 0x00BC, 0x00BE, 0x00C0, 0x00D6,
    0x00D8, 0x00F6, 0x00F8, 0x00FF, 0x0100, 0x02FF, 0x0370, 0x167F,
    0x1681, 0x180D, 0x180F, 0x1DBF, 0x1E00, 0x1FFF, 0x200B, 0x200D,
    0x202A, 0x202E, 0x203F, 0x2040, 0x2054, 0x2054, 0x2060, 0x206F,
    0x2070, 0x20CF, 0x2100, 0x218F, 0x2460, 0x24FF, 0x2776, 0x2793,
    0x2C00, 0x2DFF, 0x2E80, 0x2FFF, 0x3004, 0x3007, 0x3021, 0x302F,
    0x3031, 0x303F, 0x3040, 0xD7FF, 0xF900, 0xFD3D, 0xFD40, 0xFDCF,
    0xFDF0, 0xFE1F, 0xFE30, 0xFE44, 0xFE47, 0xFFFD,
    0x10000, 0x1FFFD, 0x20000, 0x2FFFD, 0x30000, 0x3FFFD, 0x40000, 0x4FFFD,
    0x50000, 0x5FFFD, 0x60000, 0x6FFFD, 0x70000, 0x7FFFD, 0x80000, 0x8FFFD,
    0x90000, 0x9FFFD, 0xA0000, 0xAFFFD, 0xB0000, 0xBFFFD, 0xC0000, 0xCFFFD,
    0xD0000, 0xDFFFD, 0xE0000, 0xEFFFD, -1,
  };

  return in_range(range, c);
}

// c:32位整数
// 功能： 标识符非第一个字符的是否有效
// 返回值：是否在范围内
bool is_ident2(uint32_t c) {
  static uint32_t range[] = {
    '0', '9', '$', '$', 0x0300, 0x036F, 0x1DC0, 0x1DFF, 0x20D0, 0x20FF,
    0xFE20, 0xFE2F, -1,
  };

  return is_ident1(c) || in_range(range, c);
}

