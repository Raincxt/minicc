// 实现了hashtMap
// 插入：put(hashmap,key,keylen,value)
// 删除：remove(hashmap,key,keylen,value)
// 查询：find(hashmap,key,keylen,value)
// 动态调整hashmap大小:rehash(),使用率超过70%，调用rehash,rehash后使用率必须低于50%
// 计算hash值：FNV-1a哈希算法

#include "chibicc.h"
#define INIT_SIZE 16
#define HIGH_WATERMARK 70
#define LOW_WATERMARK 50
#define TOMBSTONE ((void *)-1)

//s:entry指针
//len:entry长度
//功能：FNV-1a哈希算法
//将字符串视为一个整体，将字符串的每个字符作为一个数字，将这些数字看做一系列的位
//在这些位中执行位运算，得到一个64位的哈希值
static uint64_t FNV_hash(char *s, int len) {
  uint64_t hash = 0xcbf29ce484222325;
  for (int i = 0; i < len; i++) {
    hash *= 0x100000001b3;//质数常数
    hash ^= (unsigned char)s[i];//异或后保存
  }
  return hash;
}

// 回收被删除的hashentry,扩大bucket size.
static void rehash(HashMap *map) {
  // nkeys:计算hashmap中有效键值对的数量
  int nkeys = 0;
  for (int i = 0; i < map->capacity; i++)
    if (map->buckets[i].key && map->buckets[i].key != TOMBSTONE)
      nkeys++;
  //扩大hashmap的容量，确保使用率低于50%
  int cap = map->capacity;
  while ((nkeys * 100) / cap >= LOW_WATERMARK)
    cap = cap * 2;
  assert(cap > 0);

  //新建一个hashmap map2
  HashMap map2 = {};
  map2.buckets = calloc(cap, sizeof(HashEntry));
  map2.capacity = cap;
  //map 中的有效键值对复制到map2中
  for (int i = 0; i < map->capacity; i++) {
    HashEntry *ent = &map->buckets[i];
    if (ent->key && ent->key != TOMBSTONE)
      hashmap_put2(&map2, ent->key, ent->keylen, ent->val);
  }
  //map指向新的map2
  assert(map2.used == nkeys);
  *map = map2;
}

//检查entry是否和key匹配
static bool match(HashEntry *ent, char *key, int keylen) {
  return ent->key && ent->key != TOMBSTONE &&
         ent->keylen == keylen && memcmp(ent->key, key, keylen) == 0;
}

//获取一个entry
static HashEntry *get_entry(HashMap *map, char *key, int keylen) {
  if (!map->buckets)
    return NULL;
  //计算hash值
  uint64_t hash = FNV_hash(key, keylen);

  for (int i = 0; i < map->capacity; i++) {
    HashEntry *ent = &map->buckets[(hash + i) % map->capacity];
    if (match(ent, key, keylen))
      return ent;
    if (ent->key == NULL)
      return NULL;
  }
  unreachable();
}

//插入entry，输入key,返回该entry
static HashEntry *insert_entry(HashMap *map, char *key, int keylen) {
  //STEP1 检查维护map
  if (!map->buckets) {//如果map是空的，初始化map
    map->buckets = calloc(INIT_SIZE, sizeof(HashEntry));
    map->capacity = INIT_SIZE;
  } //如果不空，检查是否需要扩容
  else if ((map->used * 100) / map->capacity >= HIGH_WATERMARK) {//使用率高于70%，rehash
    rehash(map);
  }
  //STEP2 计算hash值
  uint64_t hash = FNV_hash(key, keylen);

  for (int i = 0; i < map->capacity; i++) {
    HashEntry *ent = &map->buckets[(hash + i) % map->capacity];

    if (match(ent, key, keylen))//插入，如果key已经存在，替换val
      return ent;

    if (ent->key == TOMBSTONE) {//插入,该位置被用过后删除,设置key，替换val
      ent->key = key;
      ent->keylen = keylen;
      return ent;
    }

    if (ent->key == NULL) {//插入-该位置还没用过，设置key，设置val
      ent->key = key;
      ent->keylen = keylen;
      map->used++;
      return ent;
    }
  }
  unreachable();
}

//获取值，从map中根据key进行查询，获取entry,返回值
void *hashmap_get(HashMap *map, char *key) {
  return hashmap_get2(map, key, strlen(key));
}
void *hashmap_get2(HashMap *map, char *key, int keylen) {
  HashEntry *ent = get_entry(map, key, keylen);
  return ent ? ent->val : NULL;
}

//插入键值对，在map中插入 key ,val ，获取entry,设置值
void hashmap_put(HashMap *map, char *key, void *val) {
   hashmap_put2(map, key, strlen(key), val);
}
void hashmap_put2(HashMap *map, char *key, int keylen, void *val) {
  HashEntry *ent = insert_entry(map, key, keylen);
  ent->val = val;
}

//删除键值对，在map中删除 key ,val ，获取entry,key设置为TOMBSTONE
void hashmap_remove(HashMap *map, char *key) {
  hashmap_remove2(map, key, strlen(key));
}
void hashmap_remove2(HashMap *map, char *key, int keylen) {
  HashEntry *ent = get_entry(map, key, keylen);
  if (ent)
    ent->key = TOMBSTONE;
}
