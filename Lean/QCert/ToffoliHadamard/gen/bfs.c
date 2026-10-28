/* Bidirectional BFS over words of involutions, with rotation rules.

Input (stdin), whitespace separated:
  A                      alphabet size (letters 0..A-1)
  MAXLHS                 longest left side of a generated rule
  R                      number of relators
  R lines: n x1 .. xn    relator (word equal to the identity)
  then queries until EOF:
  Q mode maxlen limit  na a1..ana  nb b1..bnb
     mode 0: just search; mode 1: on success add the relator a rev(b) to the rule set
Output per query: "OK k" followed by k steps "pos rid rot cut rv", or "FAIL states".
A step (pos, rid, rot, cut, rv): base = relator rid (reversed if rv),
rotated left by rot; u = base[0..cut), v = reverse(base[cut..n)); replace u
at pos by v.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#ifndef BITS
#define BITS 5
#endif
#define MAXW (128 / BITS)
#define MASK ((1 << BITS) - 1)
typedef unsigned __int128 u128;

static int A, MAXLHS;
/* relators */
static int nrel = 0, caprel = 0;
static int **rels; static int *rlen;

typedef struct { int len; int lhs[32]; int rhsn; int rhs[64]; int rid, rot, cut, rv; } Rule;
static Rule *rules; static int nrules = 0, caprules = 0;
/* hash: key = packed lhs (5 bits per letter, letter+1) -> chain of rule ids */
#define HB (1<<20)
static int *hhead; static int *hnext; static int capnext = 0;
static uint64_t lhskey(const int *u, int ul) { uint64_t k = 1469598103934665603ULL; for (int i = 0; i < ul; i++) { k ^= (uint64_t)(u[i] + 1); k *= 1099511628211ULL; } return k; }
static uint64_t mix(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return k; }
static int lhslens[40]; static int nlhslens = 0;
/* rules by first letter, in the order they were added (order --first) */
static int *byfirst[256]; static int nbyfirst[256], capbyfirst[256];
static int order_first = 0;

static void add_rule(int *u, int ul, int *v, int vl, int rid, int rot, int cut, int rv) {
  if (ul == 0 || ul > MAXLHS || ul > 32 || vl > 64) return;
  if (!hhead) { hhead = malloc(sizeof(int) * HB); memset(hhead, -1, sizeof(int) * HB); }
  uint64_t key = lhskey(u, ul); int b = (int)(mix(key) & (HB - 1));
  for (int t = hhead[b]; t >= 0; t = hnext[t]) {
    Rule *r = &rules[t];
    if (r->len == ul && r->rhsn == vl && !memcmp(r->lhs, u, ul * sizeof(int)) && !memcmp(r->rhs, v, vl * sizeof(int))) return;
  }
  if (nrules == caprules) { caprules = caprules ? 2 * caprules : 1024; rules = realloc(rules, caprules * sizeof(Rule)); }
  Rule *r = &rules[nrules];
  r->len = ul; memcpy(r->lhs, u, ul * sizeof(int)); r->rhsn = vl; memcpy(r->rhs, v, vl * sizeof(int));
  r->rid = rid; r->rot = rot; r->cut = cut; r->rv = rv;
  if (nrules >= capnext) { capnext = capnext ? 2 * capnext : 1024; hnext = realloc(hnext, sizeof(int) * capnext); }
  hnext[nrules] = hhead[b]; hhead[b] = nrules;
  { int f = u[0];
    if (nbyfirst[f] == capbyfirst[f]) { capbyfirst[f] = capbyfirst[f] ? 2 * capbyfirst[f] : 64; byfirst[f] = realloc(byfirst[f], capbyfirst[f] * sizeof(int)); }
    byfirst[f][nbyfirst[f]++] = nrules; }
  int seen = 0; for (int i = 0; i < nlhslens; i++) if (lhslens[i] == ul) seen = 1;
  if (!seen) lhslens[nlhslens++] = ul;
  nrules++;
}

static void add_relator(int *x, int n) {
  if (nrel == caprel) { caprel = caprel ? 2 * caprel : 256; rels = realloc(rels, caprel * sizeof(int *)); rlen = realloc(rlen, caprel * sizeof(int)); }
  rels[nrel] = malloc(n * sizeof(int)); memcpy(rels[nrel], x, n * sizeof(int)); rlen[nrel] = n;
  int rid = nrel++;
  int base[256], rr[256], u[256], v[256];
  for (int rv = 0; rv < 2; rv++) {
    for (int i = 0; i < n; i++) base[i] = rv ? x[n - 1 - i] : x[i];
    for (int rot = 0; rot < n; rot++) {
      for (int i = 0; i < n; i++) rr[i] = base[(rot + i) % n];
      for (int cut = 1; cut <= n; cut++) {
        int ul = cut, vl = n - cut;
        for (int i = 0; i < ul; i++) u[i] = rr[i];
        for (int i = 0; i < vl; i++) v[i] = rr[n - 1 - i];
        add_rule(u, ul, v, vl, rid, rot, cut, rv);
      }
    }
  }
}

/* words: packed 5 bits per letter (letter+1), length <= 25 */
static inline int wlen(u128 w) { int l = 0; while (w) { l++; w >>= BITS; } return l; }
static inline int wget(u128 w, int i) { return (int)((w >> (BITS * i)) & MASK) - 1; }
static u128 pack(int *x, int n) { u128 w = 0; for (int i = n - 1; i >= 0; i--) w = (w << BITS) | (u128)(x[i] + 1); return w; }
static void unpack(u128 w, int *x, int *n) { int l = 0; while (w) { x[l++] = (int)(w & MASK) - 1; w >>= BITS; } *n = l; }

/* hash map: word -> node index */
typedef struct { u128 w; int parent; int rule; int pos; } Node;
typedef struct { Node *nodes; int n, cap; int *tab; int tabcap; } Side;

static uint64_t hh(u128 w) { uint64_t a = (uint64_t)w, b = (uint64_t)(w >> 64); uint64_t h = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL; return h ^ (h >> 29); }

static void side_init(Side *s, int cap) {
  s->cap = cap; s->n = 0; s->nodes = malloc(sizeof(Node) * cap);
  s->tabcap = 1; while (s->tabcap < 2 * cap) s->tabcap <<= 1;
  s->tab = malloc(sizeof(int) * s->tabcap); memset(s->tab, -1, sizeof(int) * s->tabcap);
}
static void side_free(Side *s) { free(s->nodes); free(s->tab); }
static int side_find(Side *s, u128 w) {
  uint64_t m = s->tabcap - 1, i = hh(w) & m;
  while (s->tab[i] >= 0) { if (s->nodes[s->tab[i]].w == w) return s->tab[i]; i = (i + 1) & m; }
  return -1;
}
static int side_add(Side *s, u128 w, int parent, int rule, int pos) {
  if (s->n >= s->cap) return -2;
  uint64_t m = s->tabcap - 1, i = hh(w) & m;
  while (s->tab[i] >= 0) { if (s->nodes[s->tab[i]].w == w) return -1; i = (i + 1) & m; }
  int k = s->n++; s->nodes[k].w = w; s->nodes[k].parent = parent; s->nodes[k].rule = rule; s->nodes[k].pos = pos;
  s->tab[i] = k; return k;
}

static int maxlen, maxgrow = 100;
/* expand nodes [lo, hi) of side s; check meeting with other; return index in s of meeting node or -1; -2 if full */
static int expand(Side *s, Side *o, int lo, int hi, int *meet_other) {
  int x[32], n, y[64];
  for (int k = lo; k < hi; k++) {
    unpack(s->nodes[k].w, x, &n);
    for (int i = 0; i < n; i++) {
     if (order_first) {
      int f = x[i];
      for (int q = 0; q < nbyfirst[f]; q++) {
        int t = byfirst[f][q];
        Rule *r = &rules[t];
        if (i + r->len > n) continue;
        if (r->rhsn > r->len + maxgrow) continue;
        if (memcmp(&x[i], r->lhs, r->len * sizeof(int))) continue;
        int m = n - r->len + r->rhsn;
        if (m > maxlen) continue;
        int p = 0;
        for (int jj = 0; jj < i; jj++) y[p++] = x[jj];
        for (int jj = 0; jj < r->rhsn; jj++) y[p++] = r->rhs[jj];
        for (int jj = i + r->len; jj < n; jj++) y[p++] = x[jj];
        u128 w = pack(y, m);
        int a = side_add(s, w, k, t, i);
        if (a == -2) return -2;
        if (a >= 0) { int b = side_find(o, w); if (b >= 0) { *meet_other = b; return a; } }
      }
      continue;
     }
     for (int li = 0; li < nlhslens; li++) {
      int ul = lhslens[li];
      if (i + ul > n) continue;
      uint64_t key = lhskey(&x[i], ul); int bk = (int)(mix(key) & (HB - 1));
      for (int t = hhead[bk]; t >= 0; t = hnext[t]) {
        Rule *r = &rules[t];
        if (r->len != ul) continue;
        if (r->rhsn > r->len + maxgrow) continue;
        if (memcmp(&x[i], r->lhs, r->len * sizeof(int))) continue;
        int m = n - r->len + r->rhsn;
        if (m > maxlen) continue;
        int p = 0;
        for (int j = 0; j < i; j++) y[p++] = x[j];
        for (int j = 0; j < r->rhsn; j++) y[p++] = r->rhs[j];
        for (int j = i + r->len; j < n; j++) y[p++] = x[j];
        u128 w = pack(y, m);
        int a = side_add(s, w, k, t, i);
        if (a == -2) return -2;
        if (a >= 0) { int b = side_find(o, w); if (b >= 0) { *meet_other = b; return a; } }
      }
     }
    }
  }
  return -1;
}

static void emit_path(Side *s, int k, int forward, int *steps, int *nsteps) {
  /* collect steps from root to k */
  int stack[4096], ns = 0;
  while (s->nodes[k].parent >= 0) { stack[ns++] = k; k = s->nodes[k].parent; }
  if (forward) {
    for (int i = ns - 1; i >= 0; i--) { int q = stack[i]; steps[(*nsteps)++] = q; }
  } else {
    for (int i = 0; i < ns; i++) { int q = stack[i]; steps[(*nsteps)++] = q; }
  }
}

int main(int argc, char **argv) {
  order_first = argc > 1 && strcmp(argv[1], "--first") == 0;
  if (scanf("%d %d", &A, &MAXLHS) != 2) return 1;
  int R; scanf("%d", &R);
  for (int i = 0; i < R; i++) { int n; scanf("%d", &n); int x[512]; for (int j = 0; j < n; j++) scanf("%d", &x[j]); add_relator(x, n); }
  fprintf(stderr, "rules %d\n", nrules);
  int mode, limit;
  while (scanf("%d %d %d %d", &mode, &maxlen, &limit, &maxgrow) == 4) {
    int na, nb, a[64], b[64];
    scanf("%d", &na); for (int i = 0; i < na; i++) scanf("%d", &a[i]);
    scanf("%d", &nb); for (int i = 0; i < nb; i++) scanf("%d", &b[i]);
    if (maxlen > MAXW) maxlen = MAXW;
    u128 wa = pack(a, na), wb = pack(b, nb);
    if (wa == wb) { printf("OK 0\n"); fflush(stdout); continue; }
    Side S[2]; side_init(&S[0], limit / 2 + 16); side_init(&S[1], limit / 2 + 16);
    side_add(&S[0], wa, -1, -1, -1); side_add(&S[1], wb, -1, -1, -1);
    int lo[2] = {0, 0}, hi[2] = {1, 1};
    int found = -1, fside = 0, other = -1, full = 0;
    while (1) {
      int sz0 = hi[0] - lo[0], sz1 = hi[1] - lo[1];
      if (sz0 == 0 && sz1 == 0) break;
      int sd = (sz0 > 0 && (sz1 == 0 || sz0 <= sz1)) ? 0 : 1;
      int start = S[sd].n;
      int r = expand(&S[sd], &S[1 - sd], lo[sd], hi[sd], &other);
      if (r == -2) { full = 1; break; }
      if (r >= 0) { found = r; fside = sd; break; }
      lo[sd] = start; hi[sd] = S[sd].n;
    }
    if (found < 0) { printf("FAIL %d %d\n", S[0].n + S[1].n, full); fflush(stdout); side_free(&S[0]); side_free(&S[1]); continue; }
    /* path a -> meet -> b */
    int ka = fside == 0 ? found : other, kb = fside == 0 ? other : found;
    int sa[4096], nsa = 0, sb[4096], nsb = 0;
    emit_path(&S[0], ka, 1, sa, &nsa);
    emit_path(&S[1], kb, 0, sb, &nsb);
    printf("OK %d\n", nsa + nsb);
    for (int i = 0; i < nsa; i++) { Node *q = &S[0].nodes[sa[i]]; Rule *r = &rules[q->rule]; printf("%d %d %d %d %d\n", q->pos, r->rid, r->rot, r->cut, r->rv); }
    /* b side: node q was reached from its parent by rule r at pos; we go q -> parent, i.e. inverse rule */
    for (int i = 0; i < nsb; i++) { Node *q = &S[1].nodes[sb[i]]; Rule *r = &rules[q->rule]; printf("I %d %d %d %d %d\n", q->pos, r->rid, r->rot, r->cut, r->rv); }
    fflush(stdout);
    if (mode == 1) { int x[128], n = 0; for (int i = 0; i < na; i++) x[n++] = a[i]; for (int i = nb - 1; i >= 0; i--) x[n++] = b[i]; add_relator(x, n); }
    side_free(&S[0]); side_free(&S[1]);
  }
  return 0;
}
