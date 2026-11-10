"""Independent re-check of every macro_*.json, the order derivation composed
from its pieces, and the bookkeeping the report needs.

    python ..\\capped.py 1000 300 verify_all.py      -> summary_macro.json

The checker below shares nothing with macro.py: gates are parsed from
their names ('0~2>1': target 1, black control 0, white control 2), their
functions on the 16 states are computed here, and two words are the same
up to the interchange of letters on disjoint wires iff their projections
to each wire agree.
"""
import glob
import itertools
import json
import sys

sys.dont_write_bytecode = True

# ---------------------------------------------------------------- checker


def parse_gate(name):
    cs, t = name.split('>')
    ctrl = []
    white = False
    for ch in cs:
        if ch == '~':
            white = True
        else:
            ctrl.append((int(ch), 0 if white else 1))
            white = False
    return int(t), tuple(ctrl)


class Checker:
    def __init__(self, names):
        self.g = [parse_gate(n) for n in names]
        self.names = names
        self.wires = [frozenset([t] + [c for c, _ in cs]) for t, cs in self.g]
        self.f = []
        for t, cs in self.g:
            self.f.append(tuple(x ^ (1 << t) if all((x >> c & 1) == v for c, v in cs) else x
                                for x in range(16)))

    def func(self, w):
        p = list(range(16))
        for l in w:
            q = self.f[l]
            p = [q[v] for v in p]
        return tuple(p)

    def same_trace(self, u, v):
        if len(u) != len(v):
            return False
        for w in range(4):
            if [l for l in u if w in self.wires[l]] != [l for l in v if w in self.wires[l]]:
                return False
        return True

    def check(self, start, goal, steps):
        """Replays the steps; returns counts.  Raises AssertionError."""
        cur = list(start)
        f0 = self.func(start)
        assert f0 == self.func(goal), 'unsound target'
        cnt = {'narrow': 0, 'pair': 0, 'expand': 0, 'lemma_instances': []}
        for n, st in enumerate(steps):
            lin = list(st['lin'])
            assert self.same_trace(lin, cur), 'step %d: lin is not the current word' % n
            i = st['i']
            if st['kind'] == 'narrow':
                tr = set(st['triple'])
                assert len(tr) <= 3
                j = st['j']
                assert 0 <= i <= j <= len(lin)
                old, new = lin[i:j], list(st['new'])
                for l in old + new:
                    assert self.wires[l] <= tr, 'step %d: letter off the triple' % n
                assert self.func(old) == self.func(new), 'step %d: function changes' % n
                cur = lin[:i] + new + lin[j:]
            elif st['kind'] == 'pair':
                old, new = list(st['old']), list(st['new'])
                assert len(old) == 2 and lin[i:i + 2] == old
                g, h = old
                assert new[:2] == [h, g] and len(new) <= 3 or new[1:] == [h, g] and len(new) == 3
                assert self.func(old) == self.func(new), 'step %d: pair lemma false' % n
                cnt['lemma_instances'].append((g, h))
                cur = lin[:i] + new + lin[i + 2:]
            elif st['kind'] == 'expand':
                old, new = list(st['old']), list(st['new'])
                assert len(old) == 1 and lin[i:i + 1] == old and len(new) == 4
                assert new[2:] == new[:2]
                assert self.func(old) == self.func(new), 'step %d: expand lemma false' % n
                cnt['lemma_instances'].append((new[0], new[1]))
                cur = lin[:i] + new + lin[i + 1:]
            else:
                raise AssertionError('unknown kind')
            cnt[st['kind']] += 1
            assert self.func(cur) == f0
        assert self.same_trace(cur, list(goal)), 'end word differs from the goal'
        return cnt


# ---------------------------------------------------------------- order, composed

def triple_of(M, g):
    for tm in M.TRIPLES:
        if not (M.MASK[g] & ~tm):
            return [k for k in range(4) if tm >> k & 1]


def apply_lemma(M, cur, pos, lem):
    """cur = pre + lhs + post  ->  pre + rhs + post, with the lemma's stored
    reduction of lhs rhs^-1 to the empty word.  Returns (steps, new word)."""
    l, r = tuple(lem['lhs']), tuple(lem['rhs'])
    cur = tuple(cur)
    assert cur[pos:pos + len(l)] == l
    pre, post = cur[:pos], cur[pos + len(l):]
    steps = []
    # insert r^-1 r after lhs, one cancelling pair at a time (narrow steps)
    mid = ()
    for k in reversed(range(len(r))):
        x = r[k]
        at = len(pre) + len(l) + len(mid) // 2
        lin = pre + l + mid + post
        steps.append({'kind': 'narrow', 'triple': triple_of(M, x), 'lin': list(lin),
                      'i': at, 'j': at, 'new': [x, x]})
        h = len(mid) // 2
        mid = mid[:h] + (x, x) + mid[h:]
    assert mid == tuple(reversed(r)) + r
    tail = r + post
    for st in lem['steps']:
        s2 = dict(st)
        s2['lin'] = list(pre) + list(st['lin']) + list(tail)
        s2['i'] = st['i'] + len(pre)
        if 'j' in st:
            s2['j'] = st['j'] + len(pre)
        steps.append(s2)
    return steps, pre + r + post


def compose_order(M):
    L1 = json.load(open('macro_L1.json'))
    Tz = json.load(open('macro_Tz.json'))
    T, C = L1['lhs'][0], L1['lhs'][1]
    start = (T, C) * 6                       # K^3
    steps = []
    cur = start
    for pos, lem in ((0, L1), (6, L1), (2, Tz)):
        st, cur = apply_lemma(M, cur, pos, lem)
        steps += st
    # what is left is t C z C t C after T T cancels: all on three wires
    cur = M.canon(cur)
    w, nst = M.normalise(cur)
    steps += nst
    assert w == (), M.show(w)
    return start, steps


# ---------------------------------------------------------------- main

def main():
    import macro as M
    import pairs
    import run_macro as R
    import common
    import kdefs

    names = [M.gname(i) for i in range(M.NG)]
    ck = Checker(names)
    for i in range(M.NG):
        assert ck.f[i] == M.F[i]

    summary = {'derivations': {}, 'not_found': {}}
    used_orbits = {}
    try:
        raw = {r['pair']: r for r in json.load(open('pairlemmas_raw.json'))}
    except OSError:
        raw = {}

    def account(nm, rel, steps, extra):
        cnt = ck.check(rel, (), steps)
        assert M.check(tuple(rel), (), steps)
        orbs = {}
        for g, h in cnt['lemma_instances']:
            key = pairs.orbit_key(g, h)
            lab = '%s , %s' % (M.gname(key[0]), M.gname(key[1]))
            orbs[lab] = orbs.get(lab, 0) + 1
            used_orbits[lab] = used_orbits.get(lab, 0) + 1
        rec = {'relator': M.show(rel), 'letters': len(rel), 'narrow_steps': cnt['narrow'],
               'pair_steps': cnt['pair'], 'expand_steps': cnt['expand'],
               'macro_steps': len(steps), 'pair_lemma_orbits': orbs, 'verified': True}
        if raw:
            # every pair/expand step is one use of its orbit's lemma (g h)^2 = k,
            # transported by a symmetry of the cube: rule (7) steps are counted
            # exactly; narrow steps: those of the lemma (lower figure), plus at
            # most 3 per rule (7) step for a change of colours and 12 for
            # turning (g h)^2 = k into the form used (upper figure)
            r7 = sum(raw[o]['rule7_steps'] * c for o, c in orbs.items())
            nlo = cnt['narrow'] + sum(raw[o]['narrow_steps'] * c for o, c in orbs.items())
            nhi = nlo + 3 * r7 + 12 * sum(orbs.values())
            rec['raw_rule7_steps'] = r7
            rec['raw_narrow_steps_between'] = [nlo, nhi]
        rec.update(extra)
        summary['derivations'][nm] = rec
        print('%-14s ok: %3d letters, %3d steps = %3d narrow + %2d pair + %2d expand; raw: %4d rule7, %5d..%5d narrow' % (
            nm, len(rel), len(steps), cnt['narrow'], cnt['pair'], cnt['expand'],
            rec.get('raw_rule7_steps', -1), *rec.get('raw_narrow_steps_between', [-1, -1])), flush=True)

    for path in sorted(glob.glob('macro_*.json')):
        rec = json.load(open(path))
        nm = rec['name']
        if nm == 'order':                 # written below, from its pieces
            continue
        if not rec.get('found'):
            summary['not_found'][nm] = {k: rec.get(k) for k in ('status', 'expanded', 'time', 'relator_text')}
            print('%-14s no derivation in the file (%s)' % (nm, rec.get('status')), flush=True)
            continue
        assert rec['gates'] == names
        account(nm, rec['relator'], rec['steps'],
                {'search_time': rec.get('time'), 'expanded': rec.get('expanded'),
                 'lhs': M.show(rec['lhs']), 'rhs': M.show(rec['rhs'])})

    # the order relation K^3 = id, composed from L1 (twice) and Tz
    start, steps = compose_order(M)
    account('order', list(start), steps, {'composed_from': ['L1', 'L1', 'Tz'],
                                          'lhs': M.show(start), 'rhs': 'e'})
    json.dump({'name': 'order', 'found': True, 'checked': True, 'composed_from': ['L1', 'L1', 'Tz'],
               'lhs': list(start), 'rhs': [], 'relator': list(start), 'relator_text': M.show(start),
               'steps': steps, 'gates': names,
               'narrow_steps': sum(1 for s in steps if s['kind'] == 'narrow'),
               'pair_steps': sum(1 for s in steps if s['kind'] == 'pair'),
               'expand_steps': sum(1 for s in steps if s['kind'] == 'expand')},
              open('macro_order.json', 'w'))

    # the forms of the cycles as Syntactics.agda defines them
    A = ['Ex0', 'Ex2', 'CCX0', 'Ex2', 'Ex0']
    C = ['CCX0']
    assert kdefs.state_func((A + C) * 2) == kdefs.state_func(common.K)
    agda_form = []
    for i in range(14):
        a, b, wires = common.corner(i)
        s = ['X%d' % k for k in wires] + common.FACE[(a, b)]
        word = []
        for g in (A, C, A, C):
            f = kdefs.state_func(s + g + s[::-1])
            word.append(M.FID[f])
        word = tuple(word)
        assert M.func(word) == kdefs.func(kdefs.OM[i])
        agda_form.append(R.FORMS[i].index(word))
    summary['agda_form'] = agda_form
    summary['forms'] = [[M.show(w) for w in R.FORMS[i]] for i in range(14)]
    print('forms of the cycles in Syntactics.agda (index into forms):', agda_form)

    # letterwise forms of the apart instances
    lw = {}
    for i in range(14):
        for j in range(i + 3, 14):
            ok = []
            for fi in range(2):
                for fj in range(2):
                    if all(M.func((g, h)) == M.func((h, g))
                           for g in R.FORMS[i][fi][:2] for h in R.FORMS[j][fj][:2]):
                        ok.append([fi, fj])
            lw['%d_%d' % (i, j)] = ok
    summary['letterwise_forms'] = lw
    import shapes
    orb = {}
    for i in range(14):
        for j in range(i + 3, 14):
            orb.setdefault(shapes.canon([shapes.corner(i), shapes.corner(j)]), []).append((i, j))
    summary['apart_shapes'] = [{'representative': list(v[0]), 'instances': len(v),
                                'letterwise_in_some_forms': bool(lw['%d_%d' % v[0]])}
                               for v in orb.values()]
    print('apart shapes letterwise in some forms: %d of %d' % (
        sum(1 for x in summary['apart_shapes'] if x['letterwise_in_some_forms']), len(orb)))
    print('letterwise forms of apart (0,10):', lw['0_10'])
    summary['pair_lemma_orbits_used'] = used_orbits
    print('pair-lemma orbits used:', used_orbits)
    json.dump(summary, open('summary_macro.json', 'w'), indent=1)


if __name__ == '__main__':
    main()
