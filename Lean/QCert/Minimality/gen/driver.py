"""Derivations between consecutive printed lines of the paper, for any fragment.

A fragment configuration `C` provides: `fr` (tsearch.Frag), `axioms`, `syms` (name -> (k, lhs,
rhs) in time order), `LABELS` (paper label -> axiom name), `SHORTCUTS` (labels of definitions),
`word(fig) -> (n, time word)`, `TEX` (the appendix file), `cancel(lemmas)` (gate -> (kind, name,
k, lhs, rhs) of its x^k = ε), `CANC` (names of cancellation rules), `COMM` (names of lemmas
[x, y] = [y, x] used as commutations), `ONEWIRE` (one-wire gates), `CACHE` (file), `EXTRA`.
"""
import sys, time, pickle, ast
sys.setrecursionlimit(20000)
from tsearch import Engine, op, shift_word
from tsearch2 import Engine2, invert
import variants
import figs

def W(s):
    return [(g, int(o)) for g, o in (t.rsplit('@', 1) for t in s.split())]

class Driver:
    def __init__(self, C):
        self.C = C
        self.lemmas = {}
        self.results = {}
        self.FAILED = []
        self.CACHE = {}
        self.NBR = []
        self.REPAIRS = []
        try: self.CACHE.update(ast.literal_eval(open(C.CACHE, encoding='utf-8').read()))
        except FileNotFoundError: pass

    # --- equations
    def eq_indices(self, eng, labs, use_all=False, with_syms=True):
        C = self.C
        idx = []
        if with_syms:
            for nm, (k, l, r) in C.syms.items(): idx += eng.placements('sym', nm, k, l, r)
        names = list(C.axioms) + list(self.lemmas) if use_all else labs
        expanded = []
        for lab in names:
            m = C.LABELS.get(lab, lab)
            expanded += m if isinstance(m, list) else [lab]
        for lab in expanded:
            if lab in C.SHORTCUTS: continue
            lab = C.LABELS.get(lab, lab)
            if lab in C.axioms:
                k, l, r = C.axioms[lab]; idx += eng.placements('ax', lab, k, l, r)
            elif lab in self.lemmas:
                k, l, r = self.lemmas[lab]; idx += eng.placements('lem', lab, k, l, r)
            else:
                raise Exception('unknown label %s' % lab)
        return idx

    def resolve(self, lab):
        C = self.C
        lab = C.LABELS.get(lab, lab)
        if isinstance(lab, list): return None
        if lab in C.axioms: return 'ax', lab, C.axioms[lab]
        if lab in self.lemmas: return 'lem', lab, self.lemmas[lab]
        return None

    def engine(self, n):
        return Engine2(self.C.fr, n, self.C.cancel(self.lemmas))

    def nat1_eqs(self, eng):
        C = self.C
        return {g: eng.add(op(C.syms['nat1 .' + g][1]), op(C.syms['nat1 .' + g][2]), ('sym', 'nat1 .' + g, 0, 0))
                for g in C.ONEWIRE}

    def finish(self, nm, k, eng, L2, R2, st, cache_key='variant'):
        a, sa = eng.normalize(L2); b, sb = eng.normalize(R2)
        st = invert(sa) + st + sb; L2, R2 = a, b
        assert eng.replay(L2, st) == tuple(R2)
        used = sorted({s[2] for s in st if s[0] == 'rw'})
        ren = {x: j for j, x in enumerate(used)}
        st2 = [s if s[0] == 'swap' else ('rw', s[1], ren[s[2]], s[3]) for s in st]
        self.results[nm] = (k, op(L2), op(R2), [eng.eqs[x][2] for x in used], st2)
        self.lemmas[nm] = (k, list(op(L2)), list(op(R2)))
        self.CACHE[nm] = (cache_key, self.results[nm])

    def make_variant(self, lab, which):
        """lab~i (inverse), lab~m (mirror, two wires), lab~r (reversed, three wires)."""
        C = self.C
        nm = lab + '~' + which
        if nm in self.lemmas: return nm
        rs = self.resolve(lab)
        if rs is None: return None
        kind, base, (k, l, rr) = rs
        eng = self.engine(k)
        e = eng.add(op(l), op(rr), (kind, base, 0, 0))
        L, R = op(l), op(rr)
        try:
            if which == 'i':
                st = variants.inverse_steps(eng, e, L, R)
                if st is None: return None
                L2, R2 = eng.inv_word(L), eng.inv_word(R)
            elif which == 'r':
                if k != 3: return None
                letter_eq = {}
                for x in set(L) | set(R):
                    nm3 = self.r3_lemma(x)
                    if nm3 is None: return None
                    k3, l3, r3 = self.lemmas[nm3]
                    letter_eq[x] = eng.add(op(l3), op(r3), ('lem', nm3, 0, 0))
                invol = self.invol3(eng)
                sl = variants.rconj_push(L, letter_eq, invol, C.fr)
                sr = variants.rconj_push(R, letter_eq, invol, C.fr)
                st = invert(sl) + [('rw', 3, e, False)] + sr
                L2, R2 = variants.rho3_word(L, C.fr), variants.rho3_word(R, C.fr)
            else:
                if k != 2: return None
                st = variants.mirror_steps(eng, e, L, R, self.nat1_eqs(eng), self.invol2(eng), C.fr)
                L2, R2 = variants.mirror_word(L, C.fr), variants.mirror_word(R, C.fr)
        except (AssertionError, KeyError):
            return None
        assert eng.replay(L2, st) == tuple(R2)
        self.finish(nm, k, eng, L2, R2, st)
        return nm

    def invol2(self, eng):
        C = self.C
        return eng.add(op(C.syms['invol'][1]), op(C.syms['invol'][2]), ('sym', 'invol', 0, 0))

    def invol3(self, eng):
        C = self.C
        return {0: eng.add(op(C.syms['invol'][1]), op(C.syms['invol'][2]), ('sym', 'invol', 1, 0)),
                1: eng.add(op(shift_word(C.syms['invol'][1], 1)), op(shift_word(C.syms['invol'][2], 1)),
                           ('sym', 'invol', 0, 1))}

    def with_variants(self, labs):
        C = self.C
        out = list(labs)
        exp = []
        for lab in labs:
            m = C.LABELS.get(lab, lab)
            exp += m if isinstance(m, list) else [lab]
        for lab in exp:
            if lab in C.SHORTCUTS: continue
            lab = C.LABELS.get(lab, lab)
            for which in ['i', 'm', 'r']:
                v = self.make_variant(lab, which)
                if v: out.append(v)
            vm = self.make_variant(lab, 'm')
            if vm:
                v = self.make_variant(vm, 'i')
                if v: out.append(v)
        return out

    # --- one step
    def step_search(self, eng, name, i, A, B, cur, nxt, labs, quiet):
        C = self.C
        canc = [x for x in C.CANC if x in C.axioms or x in self.lemmas]
        nbr = list(dict.fromkeys(labs + [x for x in self.NBR if x not in labs]))
        ei = self.eq_indices; wv = self.with_variants
        stages = [
            ('plain', lambda: ei(eng, labs, with_syms=False), dict(maxdepth=8, timeout=3)),
            ('plain+forms', lambda: ei(eng, wv(labs), with_syms=False), dict(maxdepth=4, timeout=5)),
            ('cited', lambda: ei(eng, labs, with_syms=False), dict(maxdepth=8, timeout=5)),
            ('plain+syms', lambda: ei(eng, wv(labs)), dict(maxdepth=4, timeout=5)),
            ('cited+forms', lambda: ei(eng, wv(labs), with_syms=False), dict(maxdepth=4, timeout=10)),
            ('nbr+forms', lambda: ei(eng, wv(nbr), with_syms=False), dict(maxdepth=4, timeout=10)),
            ('+syms', lambda: ei(eng, wv(labs)), dict(maxdepth=6, timeout=30)),
            ('+partial', lambda: ei(eng, wv(labs) + canc), dict(maxdepth=4, partial=True, timeout=60)),
            ('nbr+partial', lambda: ei(eng, wv(nbr) + canc), dict(maxdepth=4, partial=True, timeout=30)),
            ('all', lambda: ei(eng, [], use_all=True), dict(maxdepth=3, partial=True, timeout=90)),
        ]
        # long words make every expansion slower: give the stages time in proportion
        scale = max(1.0, (max(len(A), len(B)) / 60.0) ** 2)
        for sname, idxf, kw in stages:
            kw = dict(kw)
            kw['timeout'] = kw['timeout'] * scale
            t1 = time.time()
            idx = idxf()
            if sname.startswith('plain'):
                eng.reducing = False
                ca, cb = eng.canon(A), eng.canon(B)
                path = eng.search(ca, cb, idx, maxnodes=10**7, maxlen=max(80, len(ca), len(cb)) + 16, **kw)
                out = None
                if path is not None:
                    mid = eng.path_steps(path)
                    eng.reducing = True
                    out = invert(eng.reduce(ca)[1]) + mid + eng.reduce(cb)[1]
                eng.reducing = True
            else:
                path = eng.search(cur, nxt, idx, maxnodes=10**7, maxlen=max(80, len(cur), len(nxt)) + 16, **kw)
                out = None if path is None else eng.path_steps(path)
            if out is not None:
                if sname != 'plain' and not quiet:
                    print('   (%s step %d %s: %s, %.1fs)' % (name, i, labs, sname, time.time() - t1), flush=True)
                return out
        return None

    def r3_lemma(self, x):
        nm = 'R3:%s%d' % x
        if nm in self.lemmas: return nm
        ok = self.derive(nm, 3, [list(variants.R3) + [x] + list(variants.R3),
                                 list(variants.rho3_letter(x, self.C.fr))], [[]], quiet=True)
        return nm if ok else None

    def split_scalars(self, Wd):
        sc = tuple(a for a in Wd if a[0] in self.C.fr.scalars)
        rest = tuple(a for a in Wd if a[0] not in self.C.fr.scalars)
        return sc, rest

    def upside_down(self, eng, n, Wd):
        """For Wd = scalars, P·w·P (P the swap or the reversal of three wires, up to where the
        scalars stand): (M, steps from Wd to M) with M = scalars, mirror(w)."""
        from tsearch2 import shift_step
        sc, rest = self.split_scalars(Wd)
        if not self.conj_shape(n, rest): return None
        perm = eng.permute(Wd, sc + rest)
        if n == 2:
            inner = rest[1:-1]
            ms = variants.mirror_push(eng, inner, self.nat1_eqs(eng), self.invol2(eng), self.C.fr)
            ms = invert(ms)                                   # rest -> mirror(inner)
            M = sc + variants.mirror_word(inner, self.C.fr)
        else:
            inner = rest[3:-3]
            letter_eq = {}
            for x in set(inner):
                nm = self.r3_lemma(x)
                if nm is None: return None
                k, l, rr = self.lemmas[nm]
                letter_eq[x] = eng.add(op(l), op(rr), ('lem', nm, 0, 0))
            ms = variants.rconj_push(inner, letter_eq, self.invol3(eng), self.C.fr)  # rest -> rho(inner)
            M = sc + variants.rho3_word(inner, self.C.fr)
        steps = perm + [shift_step(st, len(sc)) for st in ms]
        assert eng.replay(Wd, steps) == tuple(M)
        return M, steps

    def mirror_any(self, eng, n, name, i, A, B, cur, nxt, labs, quiet):
        for side in ['A', 'B']:
            Wd = A if side == 'A' else B
            try:
                r = self.upside_down(eng, n, Wd)
            except (AssertionError, KeyError):
                r = None
            if r is None: continue
            M, ms = r
            nm_, sm = eng.normalize(M)
            if side == 'A':
                pre = invert(eng.normalize(A)[1]) + ms + sm
                st = self.step_search(eng, name, i, M, B, nm_, nxt, labs, True)
                if st is not None:
                    if not quiet: print('   (%s step %d %s: upside down)' % (name, i, labs), flush=True)
                    return pre + st
            else:
                post = invert(sm) + invert(ms) + eng.normalize(B)[1]
                st = self.step_search(eng, name, i, A, M, cur, nm_, labs, True)
                if st is not None:
                    if not quiet: print('   (%s step %d %s: upside down)' % (name, i, labs), flush=True)
                    return st + post
        return None

    def mirror_try(self, eng, name, i, A, B, cur, nxt, labs, quiet):
        return self.mirror_any(eng, 2, name, i, A, B, cur, nxt, labs, quiet)

    def mirror3_try(self, eng, name, i, A, B, cur, nxt, labs, quiet):
        return self.mirror_any(eng, 3, name, i, A, B, cur, nxt, labs, quiet)

    def conj_shape(self, n, Wd):
        if n == 2: return len(Wd) >= 2 and Wd[0] == ('SW', 0) and Wd[-1] == ('SW', 0)
        if n == 3: return len(Wd) >= 6 and tuple(Wd[:3]) == variants.R3 and tuple(Wd[-3:]) == variants.R3
        return False

    # --- a derivation through given lines
    def derive(self, name, n, ways, labels, quiet=False):
        C = self.C
        t = time.time()
        key = repr((n, ways, labels))
        if name in self.CACHE and self.CACHE[name][0] == key:
            self.results[name] = self.CACHE[name][1]; self.lemmas[name] = (n, ways[0], ways[-1])
            if not quiet: print('%s: cached' % name, flush=True)
            return True
        eng = self.engine(n)
        for cm in C.COMM:
            if cm in self.lemmas and not name.startswith(cm + '~') and name != cm:
                k, l, rr = self.lemmas[cm]; eng.add_comm('lem', cm, k, l, rr)
        steps = []
        cur, st = eng.normalize(op(ways[0])); steps += st
        for i in range(len(ways) - 1):
            A, B = op(ways[i]), op(ways[i + 1])
            nxt, _ = eng.normalize(B)
            self.NBR[:] = (list(labels[i - 1]) if i > 0 else []) + (list(labels[i + 1]) if i + 1 < len(labels) else [])
            st = None
            conjA, conjB = self.conj_shape(n, self.split_scalars(A)[1]), self.conj_shape(n, self.split_scalars(B)[1])
            if name.startswith('R3:'): conjA = conjB = None     # the letters of the reversal itself
            if conjA != conjB:      # drawn upside down on one side: try that first
                st = (self.mirror_try if n == 2 else self.mirror3_try)(eng, name, i, A, B, cur, nxt, list(labels[i]), quiet)
            if st is None:
                st = self.step_search(eng, name, i, A, B, cur, nxt, list(labels[i]), quiet)
            if st is None and n == 2 and conjA == conjB and conjA is not None:
                st = self.mirror_try(eng, name, i, A, B, cur, nxt, list(labels[i]), quiet)
            if st is None and n == 3 and conjA == conjB and conjA is not None:
                st = self.mirror3_try(eng, name, i, A, B, cur, nxt, list(labels[i]), quiet)
            if st is None:
                print('  FAILED %s step %d %s' % (name, i, labels[i]), flush=True)
                self.FAILED.append((name, i))
                self.lemmas[name] = (n, ways[0], ways[-1])   # assumed, to see the rest
                return False
            steps += st
            cur = nxt
        last, stl = eng.normalize(op(ways[-1]))
        assert last == cur
        steps += invert(stl)
        assert eng.replay(op(ways[0]), steps) == op(ways[-1])
        used = sorted({s[2] for s in steps if s[0] == 'rw'})
        ren = {e: j for j, e in enumerate(used)}
        steps2 = [s if s[0] == 'swap' else ('rw', s[1], ren[s[2]], s[3]) for s in steps]
        eqs2 = [eng.eqs[e][2] for e in used]
        self.results[name] = (n, ways[0], ways[-1], eqs2, steps2)
        self.lemmas[name] = (n, ways[0], ways[-1])
        self.CACHE[name] = (key, self.results[name])
        self.save()
        if not quiet:
            print('%s: %d steps, %d eqs, %.1fs' % (name, len(steps2), len(eqs2), time.time() - t), flush=True)
        return True

    def save(self):
        with open(self.C.CACHE, 'w', encoding='utf-8', newline='\n') as f:
            f.write('{\n')
            for k in sorted(self.CACHE):
                f.write('%r: %r,\n' % (k, self.CACHE[k]))
            f.write('}\n')

    def chain_ways(self, label, tex=None):
        C = self.C
        toks = figs.derivations(tex or C.TEX)[label]
        first, steps = figs.chain(toks)
        n, w0 = C.word(first)
        ways = [w0]; labs = []
        carry = []
        for i, (l, f) in enumerate(steps):
            extra = C.EXTRA.get(label, {}).get(i, [])
            for (el, ew) in extra:
                ways.append(ew); labs.append(carry + list(el)); carry = []
            try:
                w = C.word(f)[1]
            except Exception as e:
                if 'no such file' not in str(e): raise
                print('   (%s: figure %s missing, line skipped)' % (label, f))
                self.REPAIRS.append((label, f, 'missing'))
                carry = carry + list(l)
                continue
            ways.append(w); labs.append(carry + list(l)); carry = []
        if getattr(C, 'REPAIR', False):
            ways, labs = self.repair(label, n, ways, labs)
        return n, ways, labs

    def repair(self, label, n, ways, labs):
        """Lines whose matrix is the first line's times a power of the scalar get that power
        compensated; lines whose matrix is not a multiple of it are dropped."""
        import numpy as np, cmath
        C = self.C
        sc, order = C.SCALAR
        M0 = C.mat(n, ways[0])
        out_w, out_l = [ways[0]], []
        pend = []
        for i in range(1, len(ways)):
            pend = pend + list(labs[i - 1])
            M = C.mat(n, ways[i])
            r = M @ np.linalg.inv(M0)
            if not np.allclose(r, r[0, 0] * np.eye(r.shape[0])):
                print('   (%s: line %d is not a multiple of the first, dropped)' % (label, i))
                self.REPAIRS.append((label, i, 'dropped'))
                continue
            k = round(cmath.phase(r[0, 0]) / (2 * cmath.pi) * order) % order
            w = list(ways[i])
            if k:
                w = w + [(sc, 0)] * ((order - k) % order)
                self.REPAIRS.append((label, i, k))
            out_w.append(w); out_l.append(pend); pend = []
        return out_w, out_l

    def from_chain(self, label, name=None, tex=None):
        n, ways, labs = self.chain_ways(label, tex)
        return self.derive(name or label, n, ways, labs)
