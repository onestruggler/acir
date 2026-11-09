"""Derivation search with narrow steps.

A narrow step replaces a block of letters lying on m adjacent wires
(s .. s+m-1) by another block on those wires with the same function;
Agda justifies it by completeness on m wires (Narrow2.by2 for m = 2,
Narrow3.by3 for m = 3), lifted s wires up.  Rule steps are those of
derive.Lib.  Steps are (lin, i, P, Q, agda): rewrite P at position i of
the linearisation lin into Q, justified by the Agda expression agda.
"""
import os
import sys
from collections import deque
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xc import perm, ARITY
from derive import (Lib, parse, show, canon, occurrences, shifted, agda_eq, agda_list,
                    wires, dep, base_lib)


def window_letters(m):
    out = [('X', i) for i in range(m)] + [('CX', i) for i in range(m - 1)] + \
          [('SW', i) for i in range(m - 1)] + [('CCX', i) for i in range(m - 2)]
    return out


class Table:
    """Words on m wires, by function: all of length <= the shortest + slack."""

    def __init__(self, m, slack=1, cap=16, enum_len=6):
        self.m = m
        gens = window_letters(m)
        ident = tuple(range(2 ** m))
        words = {}
        if m <= 2:
            # every word up to enum_len letters, grouped by function
            layer = [()]
            allw = [()]
            for _ in range(enum_len):
                layer = [w + (g,) for w in layer for g in gens]
                allw += layer
            dist = {}
            for w in allw:
                p = perm(w, m)
                dist[p] = min(dist.get(p, 99), len(w))
            for w in allw:
                p = perm(w, m)
                if len(w) <= dist[p] + slack:
                    lst = words.setdefault(p, [])
                    if len(lst) < cap:
                        lst.append(w)
        else:
            # one shortest word per function, by breadth-first search
            dist = {ident: 0}
            words = {ident: [()]}
            frontier = [ident]
            while frontier:
                nxt = []
                for p in frontier:
                    w = words[p][0]
                    for g in gens:
                        w2 = w + (g,)
                        p2 = perm(w2, m)
                        if p2 not in dist:
                            dist[p2] = len(w2)
                            words[p2] = [w2]
                            nxt.append(p2)
                frontier = nxt
        self.dist = dist
        self.words = words

    def alts(self, p):
        return self.words.get(p, [])


def in_window(l, s, m):
    return wires(l) <= set(range(s, s + m))


def window_first(w, s, m):
    """A linearisation of w emitting window letters as early as possible."""
    w = list(w)
    out = []
    while w:
        pick = None
        for i, l in enumerate(w):
            if any(dep(w[j], l) for j in range(i)):
                continue
            if in_window(l, s, m):
                pick = i
                break
            if pick is None:
                pick = i
        out.append(w.pop(pick))
    return tuple(out)


class Searcher:
    def __init__(self, lib, narrow=None, maxseg=6):
        """narrow: list of (m, Table, agda-function-name)."""
        self.lib = lib
        self.narrow = narrow or []
        self.maxseg = maxseg

    def moves(self, w, maxlen, allow=None):
        for tag, P, Q in self.lib.instances(allow):
            for lin, i in occurrences(w, P):
                res = lin[:i] + Q + lin[i + len(P):]
                if len(res) <= maxlen:
                    (en, s, rev) = tag
                    yield res, (lin, i, P, Q, agda_eq(en, s, rev), agda_eq(en, s, not rev))
        if allow is not None and 'narrow' not in allow:
            return
        W = self.lib.width
        for (m, tab, fn) in self.narrow:
            for s in range(0, W - m + 1):
                lin = window_first(w, s, m)
                n = len(lin)
                a = 0
                while a < n:
                    if not in_window(lin[a], s, m):
                        a += 1
                        continue
                    b = a
                    while b < n and in_window(lin[b], s, m):
                        b += 1
                    for i in range(a, b):
                        for j in range(i + 1, min(b, i + self.maxseg) + 1):
                            seg = lin[i:j]
                            base = shifted(seg, -s)
                            p = perm(base, m)
                            for alt in tab.alts(p):
                                if alt == base or len(alt) > len(seg) + 1:
                                    continue
                                Q = shifted(alt, s)
                                res = lin[:i] + Q + lin[j:]
                                if len(res) > maxlen:
                                    continue
                                e = '%s %s %s refl' % (fn, agda_list(base), agda_list(alt))
                                er = '%s %s %s refl' % (fn, agda_list(alt), agda_list(base))
                                for _ in range(s):
                                    e = 'lift⁼ (%s)' % e
                                    er = 'lift⁼ (%s)' % er
                                yield res, (lin, i, seg, Q, e, er)
                    a = b

    def connect1(self, a, b, depth, maxlen, allow):
        """Bidirectional breadth-first search, depth = total number of steps."""
        ca, cb = canon(a), canon(b)
        if ca == cb:
            return []
        fwd = {ca: None}
        bwd = {cb: None}
        ff, fb = [ca], [cb]
        df = db = 0
        while (df < depth and ff) or (db < depth and fb):
            can_f = df < depth and ff
            can_b = db < depth and fb
            expand_f = can_f and (not can_b or len(ff) <= len(fb))
            frontier, seen, other = (ff, fwd, bwd) if expand_f else (fb, bwd, fwd)
            nxt = []
            meet = None
            for w in frontier:
                for res, step in self.moves(w, maxlen, allow):
                    c = canon(res)
                    if c in seen:
                        continue
                    seen[c] = (w, step)
                    nxt.append(c)
                    if c in other:
                        meet = c
                        break
                if meet is not None:
                    break
            if expand_f:
                ff = nxt
                df += 1
            else:
                fb = nxt
                db += 1
            if meet is not None:
                steps = []
                x = meet
                while fwd[x] is not None:
                    pw, st = fwd[x]
                    steps.append(st)
                    x = pw
                steps.reverse()
                x = meet
                while bwd[x] is not None:
                    pw, (lin, i, P, Q, e, er) = bwd[x]
                    # the step pw -> x, run backwards: x -> pw
                    lin2 = lin[:i] + Q + lin[i + len(P):]
                    steps.append((lin2, i, Q, P, er, e))
                    x = pw
                return steps
        return None
    def connect(self, a, b, depth=3, maxlen=None, allow=None):
        if maxlen is None:
            maxlen = max(len(a), len(b)) + 4
        for d in range(1, depth + 1):
            r = self.connect1(a, b, d, maxlen, allow)
            if r is not None:
                return r
        raise RuntimeError('no connection within depth %d: %s  ->  %s' % (depth, show(a), show(b)))

    def derivation(self, name, arity, waypoints, depth=3, allow=None, typ=None, maxlen=None,
                   check=True):
        ws = [parse(x) if isinstance(x, str) else tuple(x) for x in waypoints]
        lhs, rhs = ws[0], ws[-1]
        W = self.lib.width
        if check:
            assert perm(lhs, W) == perm(rhs, W), (name, 'unsound')
        steps = []
        cur = lhs
        for nxt in ws[1:]:
            for lin, i, P, Q, e, _ in self.connect(cur, nxt, depth=depth, maxlen=maxlen, allow=allow):
                steps.append('perm %s' % agda_list(lin))
                steps.append('rw %d (%s)' % (i, e))
                cur = lin[:i] + Q + lin[i + len(P):]
            if canon(cur) != canon(nxt):
                raise RuntimeError('waypoint mismatch at ' + show(nxt))
        if cur != rhs:
            steps.append('perm %s' % agda_list(rhs))
        nn = {1: '₁₊ n', 2: '₂₊ n', 3: '₃₊ n', 4: '₄₊ n'}[arity]
        typ = typ or 'Eqn (%s)' % nn
        body = ' ∷\n     '.join(steps)
        stl = '(' + body + ' ∷ [])' if steps else '[]'
        return ('%s : %s\n%s = derive %s\n  %s\n  %s\n  refl\n' %
                (name, typ, name, agda_list(lhs), agda_list(rhs), stl))
