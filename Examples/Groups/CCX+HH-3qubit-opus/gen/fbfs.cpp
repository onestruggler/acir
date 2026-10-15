// Bidirectional breadth-first search over string rewriting.
//
// stdin:  R            (number of rules)
//         R lines: lp p1..plp lq q1..qlq
//         lu u1..ulu
//         lv v1..vlv
//         maxlen maxnodes
// stdout: "FOUND k" followed by k lines "pos rule dir" (dir 1: p->q, -1: q->p),
//         or "NONE nodes".
// Letters are < 32; words have length <= 25 and are packed 5 bits a letter
// with the length in the low bits of the second word.
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <vector>
#include <deque>
#include <algorithm>
#include <array>
using namespace std;

struct Key { uint64_t a, b; bool operator==(const Key&o) const { return a==o.a && b==o.b; } };

static int MAXLEN;
static Key pack(const uint8_t* w, int n) {
  Key k{0,0};
  for (int i = 0; i < n; i++) {
    if (i < 12) k.a |= (uint64_t)w[i] << (5*i);
    else k.b |= (uint64_t)w[i] << (5*(i-12));
  }
  k.b |= (uint64_t)n << 59;
  return k;
}
static int unpack(Key k, uint8_t* w) {
  int n = (int)(k.b >> 59);
  for (int i = 0; i < n; i++) {
    if (i < 12) w[i] = (k.a >> (5*i)) & 31;
    else w[i] = (k.b >> (5*(i-12))) & 31;
  }
  return n;
}
static inline uint64_t hsh(Key k) {
  uint64_t x = k.a * 0x9E3779B97F4A7C15ULL ^ (k.b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL;
  x ^= x >> 29; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 32; return x;
}

struct Node { Key k; int32_t parent; int32_t rule; int16_t pos; int8_t dir; };

struct Table {
  vector<Node> nodes;
  vector<int32_t> slots;
  uint64_t mask;
  void init(size_t cap) {
    size_t s = 1; while (s < cap*2) s <<= 1;
    slots.assign(s, -1); mask = s - 1; nodes.reserve(cap);
  }
  int find(Key k) const {
    uint64_t h = hsh(k) & mask;
    while (true) {
      int32_t i = slots[h];
      if (i < 0) return -1;
      if (nodes[i].k == k) return i;
      h = (h + 1) & mask;
    }
  }
  int insert(Key k, int parent, int rule, int pos, int dir) {
    uint64_t h = hsh(k) & mask;
    while (true) {
      int32_t i = slots[h];
      if (i < 0) { slots[h] = nodes.size(); nodes.push_back({k, parent, rule, (int16_t)pos, (int8_t)dir}); return -1; }
      if (nodes[i].k == k) return i;
      h = (h + 1) & mask;
    }
  }
};

struct Rule { vector<uint8_t> p, q; };
static vector<Rule> rules;
static vector<vector<pair<int,int>>> byFirst; // letter -> (rule, dir)

int main() {
  int R; if (scanf("%d", &R) != 1) return 1;
  rules.resize(R);
  byFirst.assign(32, {});
  for (int r = 0; r < R; r++) {
    int lp; scanf("%d", &lp); rules[r].p.resize(lp); for (auto &x : rules[r].p) { int t; scanf("%d", &t); x = t; }
    int lq; scanf("%d", &lq); rules[r].q.resize(lq); for (auto &x : rules[r].q) { int t; scanf("%d", &t); x = t; }
    if (lp) byFirst[rules[r].p[0]].push_back({r, 1});
  }
  int lu; scanf("%d", &lu); vector<uint8_t> u(lu); for (auto &x : u) { int t; scanf("%d", &t); x = t; }
  int lv; scanf("%d", &lv); vector<uint8_t> v(lv); for (auto &x : v) { int t; scanf("%d", &t); x = t; }
  long long maxnodes; scanf("%d %lld", &MAXLEN, &maxnodes);
  if (MAXLEN > 25) MAXLEN = 25;
  Table T[2];
  T[0].init(maxnodes / 2 + 16); T[1].init(maxnodes / 2 + 16);
  Key ku = pack(u.data(), lu), kv = pack(v.data(), lv);
  T[0].insert(ku, -1, -1, 0, 0); T[1].insert(kv, -1, -1, 0, 0);
  if (ku == kv) { printf("FOUND 0\n"); return 0; }
  size_t lo[2] = {0, 0}, hi[2] = {1, 1};
  uint8_t w[32], nw[64];
  long long total = 2;
  while (lo[0] < hi[0] || lo[1] < hi[1]) {
    int s;
    if (lo[0] < hi[0] && (lo[1] >= hi[1] || hi[0]-lo[0] <= hi[1]-lo[1])) s = 0; else s = 1;
    size_t end = hi[s];
    for (size_t idx = lo[s]; idx < end; idx++) {
      Key k = T[s].nodes[idx].k;
      int n = unpack(k, w);
      for (int i = 0; i < n; i++) {
        for (auto [r, d] : byFirst[w[i]]) {
          const Rule &ru = rules[r];
          int m = ru.p.size();
          if (i + m > n) continue;
          if (memcmp(w + i, ru.p.data(), m)) continue;
          int nn = n - m + ru.q.size();
          if (nn > MAXLEN) continue;
          memcpy(nw, w, i);
          memcpy(nw + i, ru.q.data(), ru.q.size());
          memcpy(nw + i + ru.q.size(), w + i + m, n - i - m);
          Key nk = pack(nw, nn);
          if (T[s].find(nk) >= 0) continue;
          T[s].insert(nk, idx, r, i, 1);
          total++;
          int o = T[1-s].find(nk);
          if (o >= 0) {
            // path: from u to nk (side 0) and from nk to v (side 1)
            int a = (s == 0) ? (int)T[0].nodes.size()-1 : o;
            int b = (s == 0) ? o : (int)T[1].nodes.size()-1;
            vector<array<int,3>> left, right;
            for (int x = a; T[0].nodes[x].parent >= 0; x = T[0].nodes[x].parent)
              left.push_back({T[0].nodes[x].pos, T[0].nodes[x].rule, 1});
            reverse(left.begin(), left.end());
            for (int x = b; T[1].nodes[x].parent >= 0; x = T[1].nodes[x].parent)
              right.push_back({T[1].nodes[x].pos, T[1].nodes[x].rule, -1});
            printf("FOUND %zu\n", left.size() + right.size());
            for (auto &t : left) printf("%d %d %d\n", t[0], t[1], t[2]);
            for (auto &t : right) printf("%d %d %d\n", t[0], t[1], t[2]);
            return 0;
          }
          if (total >= maxnodes) { printf("NONE %lld\n", total); return 0; }
        }
      }
    }
    lo[s] = end; hi[s] = T[s].nodes.size();
  }
  printf("NONE %lld\n", total);
  return 0;
}
