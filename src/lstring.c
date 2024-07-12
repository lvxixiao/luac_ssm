/*
** $Id: lstring.c $
** String table (keeps all strings handled by Lua)
** See Copyright Notice in lua.h
*/

#define lstring_c
#define LUA_CORE

#include "lprefix.h"


#include <string.h>

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"


/*
** Maximum size for string table.
*/
#define MAXSTRTB	cast_int(luaM_limitN(MAX_INT, TString*))


/*
** equality for long strings
*/
int luaS_eqlngstr (TString *a, TString *b) {
  size_t len = a->u.lnglen;
  lua_assert(a->tt == LUA_VLNGSTR && b->tt == LUA_VLNGSTR);
  return (a == b) ||  /* same instance or... */
    ((len == b->u.lnglen) &&  /* equal length and ... */
     (memcmp(getstr(a), getstr(b), len) == 0));  /* equal contents */
}


unsigned int luaS_hash (const char *str, size_t l, unsigned int seed) {
  unsigned int h = seed ^ cast_uint(l);
  for (; l > 0; l--)
    h ^= ((h<<5) + (h>>2) + cast_byte(str[l - 1]));
  return h;
}


unsigned int luaS_hashlongstr (TString *ts) {
  lua_assert(ts->tt == LUA_VLNGSTR);
  if (ts->extra == 0) {  /* no hash? */
    size_t len = ts->u.lnglen;
    ts->hash = luaS_hash(getstr(ts), len, ts->hash);
    ts->extra = 1;  /* now it has its hash */
  }
  return ts->hash;
}


static void tablerehash (TString **vect, int osize, int nsize) {
  int i;
  for (i = osize; i < nsize; i++)  /* clear new elements */
    vect[i] = NULL;
  for (i = 0; i < osize; i++) {  /* rehash old part of the array */
    TString *p = vect[i];
    vect[i] = NULL;
    while (p) {  /* for each string in the list */
      TString *hnext = p->u.hnext;  /* save next */
      unsigned int h = lmod(p->hash, nsize);  /* new position */
      p->u.hnext = vect[h];  /* chain it into array */
      vect[h] = p;
      p = hnext;
    }
  }
}


/*
** Resize the string table. If allocation fails, keep the current size.
** (This can degrade performance, but any non-zero size should work
** correctly.)
*/
void luaS_resize (lua_State *L, int nsize) {
  stringtable *tb = &G(L)->strt;
  int osize = tb->size;
  TString **newvect;
  if (nsize < osize)  /* shrinking table? */
    tablerehash(tb->hash, osize, nsize);  /* depopulate shrinking part */
  newvect = luaM_reallocvector(L, tb->hash, osize, nsize, TString*);
  if (l_unlikely(newvect == NULL)) {  /* reallocation failed? */
    if (nsize < osize)  /* was it shrinking table? */
      tablerehash(tb->hash, nsize, osize);  /* restore to original size */
    /* leave table as it was */
  }
  else {  /* allocation succeeded */
    tb->hash = newvect;
    tb->size = nsize;
    if (nsize > osize)
      tablerehash(newvect, osize, nsize);  /* rehash for new size */
  }
}


/*
** Clear API string cache. (Entries cannot be empty, so fill them with
** a non-collectable string.)
*/
void luaS_clearcache (global_State *g) {
  int i, j;
  for (i = 0; i < STRCACHE_N; i++)
    for (j = 0; j < STRCACHE_M; j++) {
      if (iswhite(g->strcache[i][j]))  /* will entry be collected? */
        g->strcache[i][j] = g->memerrmsg;  /* replace it with something fixed */
    }
}


/*
** Initialize the string table and the string cache
*/
void luaS_init (lua_State *L) {
  global_State *g = G(L);
  int i, j;
  stringtable *tb = &G(L)->strt;
  tb->hash = luaM_newvector(L, MINSTRTABSIZE, TString*);
  tablerehash(tb->hash, 0, MINSTRTABSIZE);  /* clear array */
  tb->size = MINSTRTABSIZE;
  /* pre-create memory-error message */
  g->memerrmsg = luaS_newliteral(L, MEMERRMSG);
  luaC_fix(L, obj2gco(g->memerrmsg));  /* it should never be collected */
  for (i = 0; i < STRCACHE_N; i++)  /* fill cache with valid strings */
    for (j = 0; j < STRCACHE_M; j++)
      g->strcache[i][j] = g->memerrmsg;
}



/*
** creates a new string object
*/
static TString *createstrobj (lua_State *L, size_t l, int tag, unsigned int h) {
  TString *ts;
  GCObject *o;
  size_t totalsize;  /* total size of TString object */
  totalsize = sizelstring(l);
  o = luaC_newobj(L, tag, totalsize);
  ts = gco2ts(o);
  ts->hash = h;
  ts->extra = 0;
  getstr(ts)[l] = '\0';  /* ending 0 */
  return ts;
}


TString *luaS_createlngstrobj (lua_State *L, size_t l) {
  TString *ts = createstrobj(L, l, LUA_VLNGSTR, G(L)->seed);
  ts->u.lnglen = l;
  return ts;
}


void luaS_remove (lua_State *L, TString *ts) {
  stringtable *tb = &G(L)->strt;
  TString **p = &tb->hash[lmod(ts->hash, tb->size)];
  while (*p != ts)  /* find previous element */
    p = &(*p)->u.hnext;
  *p = (*p)->u.hnext;  /* remove element from its list */
  tb->nuse--;
}


static void growstrtab (lua_State *L, stringtable *tb) {
  if (l_unlikely(tb->nuse == MAX_INT)) {  /* too many strings? */
    luaC_fullgc(L, 1);  /* try to free some... */
    if (tb->nuse == MAX_INT)  /* still too many? */
      luaM_error(L);  /* cannot even create a message... */
  }
  if (tb->size <= MAXSTRTB / 2)  /* can grow string table? */
    luaS_resize(L, tb->size * 2);
}

static TString *internshrstr(lua_State *L, const char *str, size_t l);

/*
** new string (with explicit length)
*/
TString *luaS_newlstr (lua_State *L, const char *str, size_t l) {
  if (l <= LUAI_MAXSHORTLEN)  /* short string? */
    return internshrstr(L, str, l);
  else {
    TString *ts;
    if (l_unlikely(l >= (MAX_SIZE - sizeof(TString))/sizeof(char)))
      luaM_toobig(L);
    ts = luaS_createlngstrobj(L, l);
    memcpy(getstr(ts), str, l * sizeof(char));
    return ts;
  }
}


/*
** Create or reuse a zero-terminated string, first checking in the
** cache (using the string address as a key). The cache can contain
** only zero-terminated strings, so it is safe to use 'strcmp' to
** check hits.
*/
TString *luaS_new (lua_State *L, const char *str) {
  unsigned int i = point2uint(str) % STRCACHE_N;  /* hash */
  int j;
  TString **p = G(L)->strcache[i];
  for (j = 0; j < STRCACHE_M; j++) {
    if (strcmp(str, getstr(p[j])) == 0)  /* hit? */
      return p[j];  /* that is it */
  }
  /* normal route */
  for (j = STRCACHE_M - 1; j > 0; j--)
    p[j] = p[j - 1];  /* move out last element */
  /* new element is first in the list */
  p[0] = luaS_newlstr(L, str, strlen(str));
  return p[0];
}


Udata *luaS_newudata (lua_State *L, size_t s, int nuvalue) {
  Udata *u;
  int i;
  GCObject *o;
  if (l_unlikely(s > MAX_SIZE - udatamemoffset(nuvalue)))
    luaM_toobig(L);
  o = luaC_newobj(L, LUA_VUSERDATA, sizeudata(nuvalue, s));
  u = gco2u(o);
  u->len = s;
  u->nuvalue = nuvalue;
  u->metatable = NULL;
  for (i = 0; i < nuvalue; i++)
    setnilvalue(&u->uv[i].uv);
  return u;
}

/**
 * global shared string
*/
#include "rwlock.h"
#include <stdlib.h>

#define SHRSTR_SLOT 0x10000
#define HASH_NODE(h) ((h) % SHRSTR_SLOT)
#define getaddrstr(ts)	(cast(char *, (ts)) + sizeof(UTString))

typedef struct shrmap_slot {
  struct rwlock lock;
  TString *str;
} shrmap_slot;

typedef struct shrmap {
  shrmap_slot h[SHRSTR_SLOT];
  int n;
} shrmap;

static struct shrmap SSM;


//初始化共享池
LUA_API void
luaS_initssm() {
  shrmap *s = &SSM;
  int i;
  for (i = 0; i < SHRSTR_SLOT; i++) {
    rwlock_init(&s->h[i].lock);
  }
}

//扩充共享池的大小
LUA_API void
luaS_expandssm(int n) {
    __sync_add_and_fetch(&SSM.n, n);
}

//删除共享池
LUA_API void
luaS_exitssm() {
  int i;
  for (i = 0; i < SHRSTR_SLOT; i++) {
      TString *ts = SSM.h[i].str;
      while (ts) {
          TString *next = ts->u.hnext;
          free(ts);
          ts = next;
      }
  }
}

//打印共享池
LUA_API int
luaS_ssminfo(lua_State *L) {
    //字符串数量, 剩余数量, 字符串总size
    unsigned int len = 0, size = 0;
    int i;
    for (i = 0; i < SHRSTR_SLOT; i++) {
        shrmap_slot *s = &SSM.h[i];
        rwlock_rlock(&s->lock);
        TString *ts = s->str;
        while(ts) {
            len++;
            size += ts->shrlen;
            ts = ts->u.hnext;
        }

        rwlock_runlock(&s->lock);
    }

    lua_pushinteger(L, len);
    lua_pushinteger(L, size);
    lua_pushinteger(L, SSM.n);
    return 3;
}

static TString *
newstring(unsigned int h, const char *str, size_t l) {
  size_t sz = sizelstring(l);
  TString *ts = malloc(sz);
  memset(ts, 0, sz);
  ts->tt = LUA_VSHRSTR;
  ts->hash = h;
  ts->shrlen = l;
  ts->isglobal = 1;
  memcpy(getstr(ts), str, l * sizeof(char));
  return ts;
}

//共享池添加字符串
static TString *
addtossm(unsigned int h, const char *str, size_t l) {
  TString *tmp = newstring(h, str, l);
  shrmap_slot *s = &SSM.h[HASH_NODE(h)];
  rwlock_wlock(&s->lock);
  TString *ts = s->str;
  while (ts) {
      // 相同串
      if(ts->hash == h && ts->shrlen == l 
          && memcmp(str, getstr(ts), l) == 0) {
              break;
      }
      ts = ts->u.hnext;
  }
  if (ts == NULL) {
      ts = tmp;
      ts->u.hnext = s->str;
      s->str = ts;
      tmp = NULL;
  }
  rwlock_wunlock(&s->lock);
  if(tmp) {
      // string is create by other thread, so free tmp
      free(tmp);
  }
  return ts;
}

//共享池查询字符串
static TString *
queryfromssm(unsigned int h, const char *str, size_t l) {
  shrmap_slot *s = &SSM.h[HASH_NODE(h)];
  rwlock_rlock(&s->lock);
  TString *ts = s->str;
  while(ts) {
        if(ts->hash == h && ts->shrlen == l 
          && memcmp(str, getstr(ts), l) == 0) {
              break;
      }
      ts = ts->u.hnext;
  }
  rwlock_runlock(&s->lock);
  return ts;
}

/*
** checks whether short string exists and reuses it or creates a new one
*/
static TString *queryfromstrt(lua_State *L, const char *str, size_t l, unsigned int h) {
  TString *ts;
  global_State *g = G(L);
  stringtable *tb = &g->strt;
  TString **list = &tb->hash[lmod(h, tb->size)];
  lua_assert(str != NULL);  /* otherwise 'memcmp'/'memcpy' are undefined */
  for (ts = *list; ts != NULL; ts = ts->u.hnext) {
    if (l == ts->shrlen && (memcmp(str, getstr(ts), l * sizeof(char)) == 0)) {
      /* found! */
      if (isdead(g, ts))  /* dead (but not collected yet)? */
        changewhite(ts);  /* resurrect it */
      return ts;
    }
  }
  return NULL;
}


static TString *addtostrt(lua_State *L, const char *str, size_t l, unsigned int h) {
  TString *ts;
  global_State *g = G(L);
  stringtable *tb = &g->strt;
  TString **list = &g->strt.hash[lmod(h, g->strt.size)];
  if (tb->nuse >= tb->size) {  /* need to grow string table? */
    growstrtab(L, tb);
    list = &tb->hash[lmod(h, tb->size)];  /* rehash with new size */
  }
  ts = createstrobj(L, l, LUA_VSHRSTR, h);
  memcpy(getstr(ts), str, l * sizeof(char));
  ts->shrlen = cast_byte(l);
  ts->u.hnext = *list;
  ts->isglobal = 0;
  *list = ts;
  tb->nuse++;
  return ts;
}

static TString *internshrstr (lua_State *L, const char *str, size_t l) {
  TString *ts;
  global_State *g = G(L);
  unsigned int h = luaS_hash(str, l, g->seed);
  // 从 global state 里查招
  ts = queryfromstrt(L, str, l, h);
  if (ts) {
    return ts;
  }
  // 从 ssm 查找
  unsigned int h0 = luaS_hash(str, l, 0);
  ts = queryfromssm(h, str, l);
  if (ts) {
    return ts;
  }
  // 如果 n > 0, 添加到 SSM
  if (SSM.n > 0) {
    __sync_sub_and_fetch(&SSM.n, 1);
    return addtossm(h0, str, l);
  }

  /* else must create a new string */
  return addtostrt(L, str, l, h);
}