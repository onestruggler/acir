// Knuth–Bendix completion for monoid presentations, recording a
// derivation for every rule, so that the proofs can be replayed in Agda
// (Examples/Groups/Clifford+CS/Engine.agda).
//
// Input (stdin), one directive per line:
//   letters a b c ...                      letter names (ranked in this order)
//   weights 1 1 2 ...                      optional, one per letter
//   axiom NAME : l1 l2 ... = r1 r2 ...     ('.' for the empty word)
//   target NAME : ... = ...
//   maxlen N      overlaps longer than N letters are not considered
//   seconds T     give up after T seconds
//   queue small|fifo   which rule to process next: the shortest (default),
//                 or the oldest
// Output (the file named by argv[1], rewritten every minute and at the
// end): the derivations of the targets proved so far, and of every rule
// they use.
//
// A derivation of u = v is a list of steps (pos, rid, dir) taking u to v:
// at position pos, rule rid is applied forwards (dir = +1, lhs -> rhs)
// or backwards (dir = -1).  Axioms carry no steps.  The order is a
// weighted shortlex.  The targets are checked after every processed rule,
// so that a run is deterministic as long as it ends by proving them all.

#include <bits/stdc++.h>
using namespace std;

struct Step { int pos, rid, dir; };
typedef string Word;   // letters as chars 0..n-1

struct Rule {
    Word lhs, rhs;
    bool axiom = false;
    string name;
    bool flip = false;
    vector<Step> steps;
    bool active = true;
};

int NL;
vector<string> names;
vector<int> weight;
vector<Rule> rules;
int maxlen = 40, maxrules = 300000, maxlhs = 1000;
double seconds = 60;
bool fifo = false;
chrono::steady_clock::time_point t0;

double elapsed() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); }

bool greater_(const Word& u, const Word& v) {
    long wu = 0, wv = 0;
    for (unsigned char c : u) wu += weight[c];
    for (unsigned char c : v) wv += weight[c];
    if (wu != wv) return wu > wv;
    if (u.size() != v.size()) return u.size() > v.size();
    return u > v;
}

// ---- trie of left-hand sides ----------------------------------------
struct Node { vector<int> next; int rid = -1; };
vector<Node> trie;
int maxL = 0;
void trie_init() { trie.assign(1, Node()); trie[0].next.assign(NL, -1); }
void trie_add(int rid) {
    int x = 0;
    for (unsigned char c : rules[rid].lhs) {
        if (trie[x].next[c] < 0) { trie[x].next[c] = trie.size(); trie.push_back(Node()); trie.back().next.assign(NL, -1); }
        x = trie[x].next[c];
    }
    trie[x].rid = rid;
    maxL = max(maxL, (int)rules[rid].lhs.size());
}
void trie_rebuild() {
    trie_init(); maxL = 0;
    for (int i = 0; i < (int)rules.size(); i++) if (rules[i].active) trie_add(i);
}
int match_at(const Word& w, int i) {
    int x = 0;
    for (int j = i; j < (int)w.size(); j++) {
        x = trie[x].next[(unsigned char)w[j]];
        if (x < 0) return -1;
        if (trie[x].rid >= 0 && rules[trie[x].rid].active) return trie[x].rid;
    }
    return -1;
}

Word normalize(Word w, vector<Step>* steps) {
    int i = 0;
    long guard = 0;
    while (i < (int)w.size()) {
        int r = match_at(w, i);
        if (r < 0) { i++; continue; }
        if (steps) steps->push_back({i, r, +1});
        w = w.substr(0, i) + rules[r].rhs + w.substr(i + rules[r].lhs.size());
        i = max(0, i - maxL + 1);
        if (++guard > 50000000) { fprintf(stderr, "normalize: runaway\n"); exit(1); }
    }
    return w;
}

vector<Step> reversed(const vector<Step>& s) {
    vector<Step> r(s.rbegin(), s.rend());
    for (auto& x : r) x.dir = -x.dir;
    return r;
}

// ---- the rules still to be processed -----------------------------------
long rsize(int id) { return (long)rules[id].lhs.size() + (long)rules[id].rhs.size(); }
priority_queue<pair<long,int>, vector<pair<long,int>>, greater<pair<long,int>>> todo_small;
deque<int> todo_fifo;
vector<char> queued;
void todo_push(int id) { if (fifo) todo_fifo.push_back(id); else todo_small.push({rsize(id), id}); }
bool todo_empty() { return fifo ? todo_fifo.empty() : todo_small.empty(); }
size_t todo_size() { return fifo ? todo_fifo.size() : todo_small.size(); }
int todo_pop() {
    int r;
    if (fifo) { r = todo_fifo.front(); todo_fifo.pop_front(); }
    else { r = todo_small.top().second; todo_small.pop(); }
    return r;
}

deque<tuple<Word, Word, vector<Step>>> pending;
int nactive = 0;
long adds = 0;

int add_rule(const Word& a, const Word& b, vector<Step> st);

// resolve the pending equations
void drain() {
    while (!pending.empty()) {
        auto [a, b, st] = pending.front(); pending.pop_front();
        vector<Step> sa, sb;
        Word na = normalize(a, &sa), nb = normalize(b, &sb);
        if (na == nb) continue;
        vector<Step> d = reversed(sa);
        d.insert(d.end(), st.begin(), st.end());
        d.insert(d.end(), sb.begin(), sb.end());
        add_rule(na, nb, d);   // derivation na -> nb
    }
}

int add_rule(const Word& a, const Word& b, vector<Step> st) {
    Rule r;
    if (greater_(a, b)) { r.lhs = a; r.rhs = b; r.steps = st; }
    else { r.lhs = b; r.rhs = a; r.steps = reversed(st); }
    if ((int)r.lhs.size() > maxlhs) return -1;
    int id = rules.size();
    rules.push_back(r);
    queued.push_back(1);
    todo_push(id);
    nactive++;
    trie_add(id);
    // interreduce: a rule whose lhs contains the new lhs is retired and its
    // equation re-added; one whose rhs does is replaced by its normal form
    for (int s = 0; s < id; s++) {
        if (!rules[s].active) continue;
        if (rules[s].lhs.find(rules[id].lhs) != string::npos) {
            rules[s].active = false; nactive--;
            pending.push_back({rules[s].lhs, rules[s].rhs, vector<Step>{{0, s, +1}}});
        } else if (rules[s].rhs.find(rules[id].lhs) != string::npos) {
            vector<Step> sr;
            Word nr = normalize(rules[s].rhs, &sr);
            vector<Step> d{{0, s, +1}};
            d.insert(d.end(), sr.begin(), sr.end());
            Rule R2; R2.lhs = rules[s].lhs; R2.rhs = nr; R2.steps = d;
            rules[s].active = false;
            int id2 = rules.size();
            bool q = queued[s];
            rules.push_back(R2);
            queued.push_back(q);
            if (q) todo_push(id2);
            trie_add(id2);
        }
    }
    if (++adds % 2000 == 0) trie_rebuild();
    return id;
}

void overlaps(int r1, int r2) {
    const Word a = rules[r1].lhs, b = rules[r2].lhs;
    // a suffix of a is a prefix of b
    for (int k = 1; k < (int)min(a.size(), b.size()); k++) {
        if (a.compare(a.size() - k, k, b, 0, k) == 0) {
            Word w = a + b.substr(k);
            if ((int)w.size() > maxlen) continue;
            int p2 = a.size() - k;
            Word w1 = rules[r1].rhs + b.substr(k);
            Word w2 = a.substr(0, p2) + rules[r2].rhs;
            pending.push_back({w1, w2, vector<Step>{{0, r1, -1}, {p2, r2, +1}}});
        }
    }
    // b occurs in a
    if (r1 != r2 && b.size() <= a.size()) {
        for (size_t i = 0; i + b.size() <= a.size(); i++) {
            if (a.compare(i, b.size(), b) == 0) {
                Word w1 = rules[r1].rhs;
                Word w2 = a.substr(0, i) + rules[r2].rhs + a.substr(i + b.size());
                pending.push_back({w1, w2, vector<Step>{{0, r1, -1}, {(int)i, r2, +1}}});
            }
        }
    }
}

// ---- targets -----------------------------------------------------------
struct Target { string name; Word l, r; };
vector<Target> targets;

// A target's derivation is kept from the first time both sides meet:
// later rules may part the normal forms again, but the rules a derivation
// uses are never deleted.
vector<char> thave;
vector<vector<Step>> tproof;

bool all_proved() {
    if (thave.size() != targets.size()) { thave.assign(targets.size(), 0); tproof.assign(targets.size(), {}); }
    bool all = true;
    for (size_t k = 0; k < targets.size(); k++) {
        if (thave[k]) continue;
        vector<Step> sa, sb;
        Word na = normalize(targets[k].l, &sa), nb = normalize(targets[k].r, &sb);
        if (na != nb) { all = false; continue; }
        vector<Step> d = sa; auto rb = reversed(sb); d.insert(d.end(), rb.begin(), rb.end());
        thave[k] = 1; tproof[k] = d;
    }
    return all;
}

string fmtw(const Word& w) {
    if (w.empty()) return ".";
    string s;
    for (size_t i = 0; i < w.size(); i++) { if (i) s += ' '; s += names[(unsigned char)w[i]]; }
    return s;
}

void dump(FILE* out) {
    vector<pair<int, vector<Step>>> tp;
    set<int> need;
    function<void(const vector<Step>&)> visit = [&](const vector<Step>& st) {
        for (auto& s : st) if (!need.count(s.rid)) { need.insert(s.rid); if (!rules[s.rid].axiom) visit(rules[s.rid].steps); }
    };
    int proved = 0;
    for (size_t k = 0; k < targets.size(); k++) {
        if (!thave[k]) {
            Word na = normalize(targets[k].l, nullptr), nb = normalize(targets[k].r, nullptr);
            fprintf(out, "unproved %s : %s = %s\n", targets[k].name.c_str(), fmtw(na).c_str(), fmtw(nb).c_str());
            continue;
        }
        proved++;
        visit(tproof[k]);
        tp.push_back({(int)k, tproof[k]});
    }
    for (int id : need) {
        Rule& R = rules[id];
        fprintf(out, "rule %d : %s = %s", id, fmtw(R.lhs).c_str(), fmtw(R.rhs).c_str());
        if (R.axiom) fprintf(out, " axiom %s %d\n", R.name.c_str(), R.flip ? 1 : 0);
        else { fprintf(out, " steps"); for (auto& s : R.steps) fprintf(out, " %d %d %d", s.pos, s.rid, s.dir); fprintf(out, "\n"); }
    }
    for (auto& [k, d] : tp) {
        fprintf(out, "target %s : %s = %s steps", targets[k].name.c_str(), fmtw(targets[k].l).c_str(), fmtw(targets[k].r).c_str());
        for (auto& s : d) fprintf(out, " %d %d %d", s.pos, s.rid, s.dir);
        fprintf(out, "\n");
    }
    fprintf(stderr, "proved %d / %zu targets; %zu rules (%d active), %zu used, %.1f s\n",
            proved, targets.size(), rules.size(), nactive, need.size(), elapsed());
}

string outpath;
void dump_to_file() {
    string tmp = outpath + ".tmp";
    FILE* f = fopen(tmp.c_str(), "w");
    if (!f) return;
    dump(f); fclose(f);
    rename(tmp.c_str(), outpath.c_str());
}

Word parse_word(istringstream& in, map<string, int>& idx, string stop) {
    Word w; string tok;
    while (in >> tok) {
        if (tok == stop) break;
        if (tok == ".") continue;
        if (!idx.count(tok)) { fprintf(stderr, "unknown letter %s\n", tok.c_str()); exit(1); }
        w += (char)idx[tok];
    }
    return w;
}

int main(int argc, char** argv) {
    outpath = argc > 1 ? argv[1] : "kbc-out.txt";
    t0 = chrono::steady_clock::now();
    map<string, int> idx;
    string line;
    vector<tuple<string, Word, Word>> axioms;
    while (getline(cin, line)) {
        istringstream in(line);
        string d; if (!(in >> d)) continue;
        if (d[0] == '#') continue;
        if (d == "letters") { string t; while (in >> t) { idx[t] = names.size(); names.push_back(t); } NL = names.size(); weight.assign(NL, 1); }
        else if (d == "weights") { for (int i = 0; i < NL; i++) in >> weight[i]; }
        else if (d == "maxlen") in >> maxlen;
        else if (d == "maxrules") in >> maxrules;
        else if (d == "maxlhs") in >> maxlhs;
        else if (d == "seconds") in >> seconds;
        else if (d == "queue") { string q; in >> q; fifo = (q == "fifo"); }
        else if (d == "axiom" || d == "target") {
            string name, colon; in >> name >> colon;
            Word l = parse_word(in, idx, "="), r = parse_word(in, idx, "");
            if (d == "axiom") axioms.push_back({name, l, r}); else targets.push_back({name, l, r});
        }
    }
    trie_init();
    for (auto& [name, l, r] : axioms) {
        if (l == r) continue;
        Rule R; R.axiom = true; R.name = name;
        if (greater_(l, r)) { R.lhs = l; R.rhs = r; R.flip = false; } else { R.lhs = r; R.rhs = l; R.flip = true; }
        rules.push_back(R); queued.push_back(1); todo_push(rules.size() - 1); nactive++;
    }
    // interreduce the axioms
    trie_rebuild();
    {
        int n0 = rules.size();
        for (int i = 0; i < n0; i++) {
            if (!rules[i].active) continue;
            for (int j = 0; j < n0; j++) if (j != i && rules[j].active && rules[i].lhs.find(rules[j].lhs) != string::npos && rules[i].lhs != rules[j].lhs) {
                rules[i].active = false; nactive--;
                pending.push_back({rules[i].lhs, rules[i].rhs, vector<Step>{{0, i, +1}}});
                break;
            }
        }
        trie_rebuild();
        drain();
    }
    long iter = 0;
    double lastlog = 0, lastdump = 0;
    bool done = false;
    while (!todo_empty()) {
        int r = todo_pop();
        if (!queued[r]) continue;
        queued[r] = 0;
        if (!rules[r].active) continue;
        // pair r with itself and every rule processed before it; the rules
        // processed after it pair with r then
        int n0 = rules.size();
        for (int s = 0; s < n0; s++) {
            if (!rules[s].active || !rules[r].active) continue;
            if (queued[s]) continue;
            overlaps(r, s); drain();
            if (s != r && rules[r].active && rules[s].active) { overlaps(s, r); drain(); }
        }
        ++iter;
        if (!targets.empty() && all_proved()) {
            fprintf(stderr, "all targets proved\n"); done = true; break;
        }
        if (elapsed() - lastlog > 5) {
            lastlog = elapsed();
            fprintf(stderr, "[%.0fs] %zu rules, %d active, todo %zu\n", elapsed(), rules.size(), nactive, todo_size());
        }
        if (elapsed() - lastdump > 60) { lastdump = elapsed(); all_proved(); dump_to_file(); }
        if (elapsed() > seconds) { fprintf(stderr, "deadline\n"); break; }
        if (nactive > maxrules) { fprintf(stderr, "maxrules\n"); break; }
    }
    if (!done && todo_empty()) fprintf(stderr, "completed: confluent (up to maxlen)\n");
    all_proved();
    dump_to_file();
}
