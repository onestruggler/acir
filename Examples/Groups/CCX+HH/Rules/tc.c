/*
 * Coset enumeration (HLT with coincidence processing) for presentations
 * whose generators are all involutions.  Research tool for Rules/.
 *
 * Input on stdin:
 *   ngens limit
 *   nrel  then nrel lines: length g1 g2 ...
 *   nsub  then nsub lines: length g1 g2 ...
 * Output: the index of the subgroup, or "overflow" past `limit` cosets.
 *
 * Build: gcc -O2 -o tc tc.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int ngens, limit, ncos, alive;
static int *table;   /* table[c * ngens + g], -1 undefined */
static int *parent;
static int *queue_a, *queue_b, qcap;

static int find(int c) {
    while (parent[c] != c) { parent[c] = parent[parent[c]]; c = parent[c]; }
    return c;
}

static int new_coset(void) {
    if (ncos >= limit) { printf("overflow\n"); exit(0); }
    int c = ncos++;
    for (int g = 0; g < ngens; g++) table[c * ngens + g] = -1;
    parent[c] = c;
    alive++;
    return c;
}

static void set(int c, int g, int d) { table[c * ngens + g] = d; table[d * ngens + g] = c; }

static void coincidence(int a0, int b0) {
    int qh = 0, qt = 0;
    queue_a[qt] = a0; queue_b[qt] = b0; qt++;
    while (qh < qt) {
        int a = find(queue_a[qh]), b = find(queue_b[qh]); qh++;
        if (a == b) continue;
        if (a > b) { int t = a; a = b; b = t; }
        parent[b] = a;
        alive--;
        for (int g = 0; g < ngens; g++) {
            int d = table[b * ngens + g];
            if (d < 0) continue;
            table[b * ngens + g] = -1;
            d = find(d);
            if (table[d * ngens + g] == b) table[d * ngens + g] = -1;
            int e = table[a * ngens + g];
            if (e >= 0) {
                if (qt >= qcap) { qcap *= 2; queue_a = realloc(queue_a, qcap * sizeof(int)); queue_b = realloc(queue_b, qcap * sizeof(int)); }
                queue_a[qt] = find(e); queue_b[qt] = d; qt++;
            } else {
                int da = table[d * ngens + g];
                if (da >= 0 && find(da) != a) {
                    if (qt >= qcap) { qcap *= 2; queue_a = realloc(queue_a, qcap * sizeof(int)); queue_b = realloc(queue_b, qcap * sizeof(int)); }
                    queue_a[qt] = find(da); queue_b[qt] = a; qt++;
                    continue;
                }
                set(a, g, d);
            }
        }
    }
}

static void scan_fill(int c, const int *w, int n) {
    for (;;) {
        c = find(c);
        int f = c, i = 0;
        while (i < n && table[f * ngens + w[i]] >= 0) { f = find(table[f * ngens + w[i]]); i++; }
        if (i == n) { if (f != c) coincidence(f, c); return; }
        int b = c, j = n - 1;
        while (j >= i && table[b * ngens + w[j]] >= 0) { b = find(table[b * ngens + w[j]]); j--; }
        if (j < i) { coincidence(f, b); return; }
        if (j == i) { set(f, w[i], b); return; }
        int d = new_coset();
        set(f, w[i], d);
    }
}

static int **read_words(int *count, int **lens) {
    if (scanf("%d", count) != 1) exit(2);
    int **ws = malloc((*count + 1) * sizeof(int *));
    *lens = malloc((*count + 1) * sizeof(int));
    for (int k = 0; k < *count; k++) {
        if (scanf("%d", &(*lens)[k]) != 1) exit(2);
        ws[k] = malloc(((*lens)[k] + 1) * sizeof(int));
        for (int i = 0; i < (*lens)[k]; i++) if (scanf("%d", &ws[k][i]) != 1) exit(2);
    }
    return ws;
}

int main(void) {
    if (scanf("%d %d", &ngens, &limit) != 2) return 2;
    int nrel, nsub, *rlen, *slen;
    int **rel = read_words(&nrel, &rlen);
    int **sub = read_words(&nsub, &slen);
    table = malloc((size_t)limit * ngens * sizeof(int));
    parent = malloc((size_t)limit * sizeof(int));
    qcap = 1 << 16;
    queue_a = malloc(qcap * sizeof(int)); queue_b = malloc(qcap * sizeof(int));
    if (!table || !parent) { printf("nomem\n"); return 1; }
    int start = new_coset();
    for (int k = 0; k < nsub; k++) scan_fill(start, sub[k], slen[k]);
    for (int c = 0; c < ncos; c++) {
        if (find(c) != c) continue;
        for (int k = 0; k < nrel; k++) {
            scan_fill(c, rel[k], rlen[k]);
            if (find(c) != c) break;
        }
        if (find(c) != c) continue;
        for (int g = 0; g < ngens; g++)
            if (table[c * ngens + g] < 0) { int d = new_coset(); set(c, g, d); }
    }
    printf("%d\n", alive);
    return 0;
}
