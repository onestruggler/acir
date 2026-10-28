"""Generate the Lean modules of the real stabilizer development.

    python3 generate.py              derive everything and write the modules
    python3 generate.py --check      derive, and compare with the modules on disk
    python3 generate.py --cache F    keep the derivations in F between runs

Inputs (not committed; see README.md): the paper's TeX source with
`relations.tex` (`tex.TEX`) and the supplement (`suppdraw.SUPP`).

Every derivation is found here, in one run, from R1-R16 (Figure 1):

1. the supplement's lemmas L1-L19 and their upside-down versions, line by
   line (`derive.derive_lines`);
2. the typed relations, in the supplement's order, from its derivations;
   where a relation is false as printed (`relations.CORRECTIONS`) its
   corrected statement is derived instead, each drawn line that is off by
   one gate being repaired by the one insertion that lets the cited step go
   through (`derive_repaired`);
3. the 139 relations of Appendix B as stated (`relations.records`), each
   by a short derivation from the equation of step 2 it is (up to the order
   of commuting letters and the side of the scalar), or from its typed twin.

The modules are `Boxes.lean` (the derived generators), `Axioms.lean`,
`Lemmas.lean`, `Typed1.lean`... (the supplement's derivations) and
`Relations1.lean`... (Appendix B).
"""
import os
import pickle
import subprocess
import sys

if os.environ.get('PYTHONHASHSEED') != '0':
    env = dict(os.environ, PYTHONHASHSEED='0')
    sys.exit(subprocess.call([sys.executable] + sys.argv, env=env))

import derive      # noqa: E402
import engine      # noqa: E402
import paper       # noqa: E402
import relations   # noqa: E402
import suppdraw    # noqa: E402
from engine import Deriv, canon, strip_w   # noqa: E402

M = ('m',)
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ------------------------------------------------------------ derivations

def named(steps):
    return [s if s[0] == 'mv' else ('rw', engine.DB[s[1]][0]) + tuple(s[2:]) for s in steps]


def add(name, k, first, last):
    engine.set_db(engine.DB + [derive.normalise(name, k, first, last)])


def repairs(gs, neg, L, k):
    """The lines one Z or X gate away from gs that denote L."""
    for p in range(len(gs), -1, -1):
        for g in ('Z', 'X'):
            for q in range(k):
                gs2 = gs[:p] + [(g, q)] + gs[p:]
                if paper.same(derive.letters(gs2, neg), L, k):
                    yield gs2


def derive_repaired(lines, k, known):
    """Like derive.derive_lines, but a line that does not denote the first
    line's operator is replaced by the first repair the cited step reaches."""
    L = derive.letters(lines[0][1], lines[0][2])
    d = Deriv(L, k)
    prev = L
    pending = []
    for idx in range(1, len(lines)):
        lab, gs, neg = lines[idx]
        pending.append(lab)
        names, anyone = [], False
        for lb in pending:
            ls = derive.labels_for(lb, known)
            if ls is None:
                anyone = True
            else:
                names += ls
        w = derive.letters(gs, neg)
        if paper.same(w, L, k):
            cands = [w]
        else:
            cands = [derive.letters(g2, neg) for g2 in repairs(gs, neg, L, k)]
        for tgt in cands:
            saved = (list(d.word), list(d.steps))
            derive.reorder_to_canon(d, prev)
            if derive.step(d, names, tgt, anyone, known):
                prev = tgt
                pending = []
                break
            d.word, d.steps = saved
        else:
            if idx == len(lines) - 1:
                return None, 'last line not reached'
    return d, None


def finish(d, R):
    """Reorder the end of a derivation to exactly R; False if it ends
    elsewhere (`derive_lines` skips a last line that does not denote the
    operator of the first)."""
    derive.reorder_to_canon(d, R)
    return d.word == R


def run_derivations():
    ders, order = suppdraw.derivations()
    recs = relations.records(ders)
    engine.set_db(derive.reduced_db())
    known = [e[0] for e in engine.DB]
    res = {'lemmas': [], 'typed': [], 'records': [], 'failed': []}
    # 1. lemmas
    for name in order:
        if not name.startswith('L'):
            continue
        lines = ders[name]
        k = derive.frame(lines)
        todo = [(name, lines)]
        if k >= 2:
            todo.append(('M' + name, derive.mirror_lines(lines, k)))
        for nm, ls in todo:
            d, err = derive.derive_lines(ls, k, known, log=log, name=nm)
            if err:
                log(nm, 'FAILED', err)
                res['failed'].append(nm)
                continue
            first = derive.letters(ls[0][1], ls[0][2])
            last = derive.letters(ls[-1][1], ls[-1][2])
            if not finish(d, last):
                log(nm, 'FAILED (ends elsewhere)')
                res['failed'].append(nm)
                continue
            res['lemmas'].append((nm, k, first, last, named(d.steps)))
            add(nm, k, first, last)
            known.append(nm)
            log(nm, 'ok', len(d.steps))
    # 2. the supplement's derivations of the typed relations
    bysupp = {r[2]: r for r in recs if r[2]}
    for name in order:
        if name.startswith('L'):
            continue
        lines = ders[name]
        rec = bysupp.get(name)
        corrected = rec is not None and rec[0] in relations.CORRECTIONS and \
            relations.CORRECTIONS[rec[0]][0] != 'supp'
        d, err = None, None
        if not corrected:
            k = derive.frame(lines)
            d, err = derive.derive_lines(lines, k, known, log=log, name=name)
            if not err:
                first = derive.letters(lines[0][1], lines[0][2])
                last = derive.letters(lines[-1][1], lines[-1][2])
                if not finish(d, last):
                    log(name, 'ends elsewhere')
                    err = 'ends elsewhere'
        if d is None or err:
            if rec is None:
                log(name, 'FAILED (no relation)')
                res['failed'].append(name)
                continue
            _, _, _, (lg, ln), (rg, rn), _ = rec
            ls = [(None, lg, ln)] + lines[1:-1] + [(lines[-1][0], rg, rn)]
            k = max(derive.frame(ls), 2)
            d, err = derive_repaired(ls, k, known)
            if err:
                log(name, 'FAILED', err)
                res['failed'].append(name)
                continue
            first = derive.letters(lg, ln)
            last = derive.letters(rg, rn)
            if not finish(d, last):
                log(name, 'FAILED (ends elsewhere)')
                res['failed'].append(name)
                continue
        tn = 'T' + name
        res['typed'].append((tn, k, first, last, named(d.steps)))
        add(tn, k, first, last)
        known.append(tn)
        log(tn, 'ok', len(d.steps))
    # 3. Appendix B as stated
    tkeys = {}
    for tn, k, first, last, _ in res['typed']:
        a, ap = strip_w(first)
        b, bp = strip_w(last)
        tkeys.setdefault((tuple(canon(a)), tuple(canon(b)), (ap + bp) % 2), (tn, k))
        tkeys.setdefault((tuple(canon(b)), tuple(canon(a)), (ap + bp) % 2), (tn, k))
    for num, fig, supp, (lg, ln), (rg, rn), note in recs:
        L = derive.letters(lg, ln)
        R = derive.letters(rg, rn)
        a, ap = strip_w(L)
        b, bp = strip_w(R)
        hit = tkeys.get((tuple(canon(a)), tuple(canon(b)), (ap + bp) % 2))
        if hit is None:
            log('relation', num, 'FAILED (no derivation)')
            res['failed'].append(num)
            continue
        tn, k = hit
        k = max(k, paper.width(L), paper.width(R), 1)
        d = Deriv(L, k)
        if not (derive.step(d, [tn], R, False, known) and finish(d, R)):
            log('relation', num, 'FAILED (step)')
            res['failed'].append(num)
            continue
        res['records'].append((num, fig, supp, (lg, ln), (rg, rn), note, k, tn, named(d.steps)))
    res['db'] = list(engine.DB)
    return res


# ------------------------------------------------------------ Lean output

def ident(name):
    return str(name).replace('.', '_').replace('@', '_v')


def lt(a):
    if a[0] == 'm':
        return '.neg'
    return {'H': '.H', 'Z': '.Z', 'C': '.CZ'}[a[0]] + ' %d' % a[1]


def wrap_items(items, indent, width=92):
    out, line = [], ''
    for it in items:
        cand = it if not line else line + ', ' + it
        if len(cand) + indent > width and line:
            out.append(line + ',')
            line = it
        else:
            line = cand
    out.append(line)
    return ('\n' + ' ' * indent).join(out)


def lst(word, indent=4):
    return '[' + wrap_items([lt(a) for a in word], indent + 1) + ']'


def steps_lean(st, remap, indent=4):
    items = []
    for s in st:
        if s[0] == 'mv':
            items.append('.mv %d %d' % (s[1], s[2]))
        else:
            _, e, pos, sh, rev = s
            items.append('.rw %d %d %d %s' % (remap[e], pos, sh, 'true' if rev else 'false'))
    return '[' + wrap_items(items, indent + 1) + ']'


def used(st):
    out = []
    for s in st:
        if s[0] == 'rw' and s[1] not in out:
            out.append(s[1])
    return out


def dbterm(names):
    t = 'db_ok_nil'
    for g in reversed(names):
        t = 'db_ok_cons h%s (%s)' % (ident(g), t) if t != 'db_ok_nil' else \
            'db_ok_cons h%s db_ok_nil' % ident(g)
    return t


def of_derives(names, st, indent=2):
    remap = {g: i for i, g in enumerate(names)}
    pad = ' ' * indent
    return (pad + 'Holds.of_derives (%s)\n' % dbterm(names) +
            pad + '  (steps := %s)\n' % steps_lean(st, remap, indent + 2) +
            pad + '  (by decide +kernel)\n')


def eqn_def(name, k, l, r, doc=None):
    s = '/-- %s -/\n' % doc if doc else ''
    return s + 'def e%s : Eqn :=\n  ⟨%d, %s,\n    %s⟩\n\n' % (ident(name), k, lst(l, 6), lst(r, 4))


# box expressions -----------------------------------------------------------

def box_word(kind, i, n):
    return paper.expand([('box', kind, i, tuple(range(n)))])


def sym_lt(a):
    """A letter of a box at wire `a` (+ offset)."""
    if a[0] == 'm':
        return '.neg'
    w = 'a' if a[1] == 0 else '(a + %d)' % a[1]
    return {'H': '.H', 'Z': '.Z', 'C': '.CZ'}[a[0]] + ' ' + w


BOXES = [('A', 3, 1), ('B', 8, 2), ('C', 2, 1), ('D', 4, 2), ('E', 2, 1)]


def gen_boxes():
    s = HEAD.format(doc='''# Real stabilizer circuits: the derived generators

The derived generators of kind `A`-`E` (Definitions 4.1-4.5), `X = HZH` and
`CXZ` (Section 3), as words of letters in time order, read off the paper's
definitions (generated by `gen/generate.py`).  `bA i a`, `bC k a`, `bE h a`
act on the wire `a`, `bB j a` and `bD l a` on the wires `a, a + 1` (the
paper's upper wire is our `a + 1`).  `B₅`-`B₈` are the circuits `B₁`-`B₄`
with other wire types (Definition 4.6).''', imports='import QCert.RealStabilizer.Letters\n')
    for kind, cnt, n in BOXES:
        s += '/-- The derived generators of kind %s. -/\n' % kind
        s += 'def b%s : ℕ → ℕ → List Lt\n' % kind
        for i in range(1, cnt + 1):
            w = box_word(kind, i, n)
            if w:
                s += '  | %d, a => [%s]\n' % (i, ', '.join(sym_lt(x) for x in w))
        s += '  | _, _ => []\n\n'
    xw = paper.expand([('X', 0)])
    s += '/-- `X = HZH` on the wire `a`. -/\n'
    s += 'def bX (a : ℕ) : List Lt := [%s]\n\n' % ', '.join(sym_lt(x) for x in xw)
    s += ('/-- `CXZ` with `XZ` on the wire `t` and its control on the wire `c`\n'
          '(adjacent): `H_t CZ H_t CZ`. -/\n'
          'def bCXZ (t c : ℕ) : List Lt := [.H t, .CZ (min t c), .H t, .CZ (min t c)]\n\n')
    s += 'end QCert.RealStabilizer\n'
    return s


def gate_expr(g):
    if g[0] in ('H', 'Z'):
        return '[.%s %d]' % (g[0], g[1])
    if g[0] == 'CZ':
        return '[.CZ %d]' % min(g[1], g[2])
    if g[0] == 'X':
        return 'bX %d' % g[1]
    if g[0] == 'CXZ':
        return 'bCXZ %d %d' % (g[1], g[2])
    if g[0] == 'box':
        return 'b%s %d %d' % (g[1], g[2], min(g[3]))
    raise ValueError(g)


def circ_expr(gs, neg):
    parts, cur = [], []
    for g in gs:
        e = gate_expr(g)
        if e.startswith('['):
            cur.append(e[1:-1])
        else:
            if cur:
                parts.append('[' + ', '.join(cur) + ']')
                cur = []
            parts.append(e)
    if neg:
        cur.append('.neg')
    if cur:
        parts.append('[' + ', '.join(cur) + ']')
    return ' ++ '.join(parts) if parts else '[]'


def gate_text(g):
    if g[0] in ('H', 'Z', 'X'):
        return '%s%d' % g
    if g[0] in ('CZ', 'CXZ'):
        return '%s(%d,%d)' % g
    return '%s%d(%s)' % (g[1], g[2], ','.join(map(str, g[3])))


def circ_text(gs, neg):
    return ' '.join(gate_text(g) for g in gs) + (' -1' if neg else '') if gs or neg else 'I'


# modules --------------------------------------------------------------------

HEAD = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

{doc}
-/
{imports}
namespace QCert.RealStabilizer

set_option maxRecDepth 8000

'''


class Emitter:
    """Writes the database entries in dependency order, each once."""

    def __init__(self, res):
        self.db = {e[0]: e for e in res['db']}
        self.raw = {}
        for nm, k, first, last, st in res['lemmas'] + res['typed']:
            self.raw[nm] = (k, first, last, st)
        self.done = set()

    def need(self, name, out):
        if name in self.done:
            return
        nm, k, l, r = self.db[name]
        if '@' in name:
            base, _, idx = name.partition('@')
            self.need(base, out)
            f, i, j = idx.split('.')
            out.append(eqn_def(name, k, l, r, 'A form of %s (`Holds.variant`).' % base))
            out.append('theorem h%s : Holds e%s.k e%s.l e%s.r :=\n'
                       '  Holds.variant\' h%s (by decide) (by decide) %s %s %s (by decide +kernel)\n\n'
                       % (ident(name), ident(name), ident(name), ident(name), ident(base), f, i, j))
        elif name in self.raw:
            k0, first, last, st = self.raw[name]
            for g in used(st):
                self.need(g, out)
            doc = DOCS.get(name, 'Derived as in the supplement.')
            if (l, r) == (first, last):
                out.append(eqn_def(name, k, l, r, doc))
                out.append('theorem h%s : Holds e%s.k e%s.l e%s.r :=\n' % ((ident(name),) * 4) +
                           of_derives(used(st), st))
            else:
                out.append(eqn_def(name + '_raw', k, first, last, doc))
                out.append('theorem h%s_raw : Holds e%s_raw.k e%s_raw.l e%s_raw.r :=\n'
                           % ((ident(name),) * 4) + of_derives(used(st), st))
                out.append(eqn_def(name, k, l, r, 'The same, the scalars collected on the right.'))
                out.append('theorem h%s : Holds e%s.k e%s.l e%s.r :=\n'
                           '  Holds.variant\' h%s_raw (by decide) (by decide) 0 0 %d (by decide +kernel)\n\n'
                           % (ident(name), ident(name), ident(name), ident(name), ident(name),
                              len(l)))
        else:
            raise KeyError(name)
        self.done.add(name)


DOCS = {}


def module(doc, imports, body):
    return HEAD.format(doc=doc, imports=imports) + ''.join(body) + 'end QCert.RealStabilizer\n'


def gen_all(res):
    files = {'Boxes.lean': gen_boxes()}
    em = Emitter(res)
    # Axioms
    body = []
    for nm, k, l, r in res['db']:
        if nm.startswith('R') and '@' not in nm:
            num = int(nm[1:])
            if num == 1:
                body.append(eqn_def(nm, k, l, r, 'R1 of Figure 1: `(-1)(-1) = 1`.'))
            else:
                body.append(eqn_def(nm, k, l, r, 'R%d of Figure 1.' % num))
            body.append('theorem h%s : Holds e%s.k e%s.l e%s.r :=\n'
                        '  Holds.of_rel Rel.%s _ _ rfl rfl (by decide) (by decide)\n\n'
                        % (nm, nm, nm, nm, nm))
            em.done.add(nm)
    files['Axioms.lean'] = module('''# Real stabilizer circuits: the relations as equations of letters

The reduced relations R1-R16 of Figure 1 as equations between words of
letters (time order, our wire numbering), each holding on every number of
wires at least its own (`Holds.of_rel`).''', 'import QCert.RealStabilizer.Relator\n', body)
    # Lemmas
    body = []
    for nm, *_ in res['lemmas']:
        DOCS[nm] = ('Lemma %s of the supplement.' % nm[1:] if nm.startswith('L') else
                    'Lemma %s of the supplement, upside down.' % nm[2:])
        em.need(nm, body)
    files['Lemmas.lean'] = module('''# Real stabilizer circuits: the lemmas of the supplement

Lemmas 1-19 of the supplement, and their upside-down versions (`ML…`), as
equations between words of letters in time order, each derived from R1-R16
and the lemmas before it by a checked derivation that follows the
supplement's proof line by line (generated by `gen/generate.py`).''',
                                  'import QCert.RealStabilizer.Axioms\n', body)
    # Typed relations, in parts
    parts = []
    body = []
    for tn, *_ in res['typed']:
        DOCS[tn] = 'The relation (%s) of the supplement.' % tn[1:]
        em.need(tn, body)
        if sum(len(b) for b in body) > 120000:
            parts.append(body)
            body = []
    if body:
        parts.append(body)
    prev = 'QCert.RealStabilizer.Lemmas'
    tnames = []
    for p, body in enumerate(parts):
        fn = 'Typed%d.lean' % (p + 1)
        files[fn] = module('''# Real stabilizer circuits: the typed relations, as derived (part %d)

The supplement's derivations of the typed relations of Appendix B, from
R1-R16, its lemmas and the relations before, as checked derivations that
follow it line by line; where a relation is false as printed, its corrected
statement (README.md).  Equations used in another form (rotated, reversed or
split relators, `Holds.variant`) are stated as they are used.  Generated by
`gen/generate.py`.''' % (p + 1), 'import %s\n' % prev, body)
        prev = 'QCert.RealStabilizer.Typed%d' % (p + 1)
        tnames.append(fn)
    # Appendix B as stated
    parts = []
    body = []
    for num, fig, supp, (lg, ln), (rg, rn), note, k, tn, st in res['records']:
        for g in used(st):
            em.need(g, body)
        doc = 'Relation %d of Appendix B (Figure %d): `%s = %s`.' % (
            num, fig, circ_text(lg, ln), circ_text(rg, rn))
        if note:
            doc += '  Corrected: %s.' % note
        body.append('/-- %s -/\n' % doc)
        body.append('theorem rel%d :\n    Holds %d (%s)\n      (%s) :=\n' % (
            num, k, circ_expr(lg, ln), circ_expr(rg, rn)) + of_derives(used(st), st))
        if sum(len(b) for b in body) > 120000:
            parts.append(body)
            body = []
    if body:
        parts.append(body)
    for p, body in enumerate(parts):
        fn = 'Relations%d.lean' % (p + 1)
        imports = 'import %s\nimport QCert.RealStabilizer.Boxes\n' % prev
        files[fn] = module('''# Real stabilizer circuits: the typed relations of Appendix B (part %d)

The 139 relations of Appendix B (Definition 5.1) as stated in the paper,
with the derived generators (`Boxes`), each derived from the relations of
Figure 1 (`rel1`-`rel139`, numbered in the order of the paper's figures,
left to right and row by row).  Generated by `gen/generate.py`.''' % (p + 1),
                           imports, body)
        prev = 'QCert.RealStabilizer.Relations%d' % (p + 1)
    return files


def main():
    args = sys.argv[1:]
    cache = None
    if '--cache' in args:
        cache = args[args.index('--cache') + 1]
    if cache and os.path.exists(cache):
        res = pickle.load(open(cache, 'rb'))
    else:
        res = run_derivations()
        if cache:
            pickle.dump(res, open(cache, 'wb'))
    if res['failed']:
        log('FAILED:', res['failed'])
    files = gen_all(res)
    bad = 0
    for fn, text in files.items():
        path = os.path.join(OUT, fn)
        if '--check' in args:
            old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
            if old != text:
                log('differs:', fn)
                bad += 1
        else:
            with open(path, 'w', encoding='utf-8', newline='\n') as f:
                f.write(text)
    if '--check' in args:
        log('all modules agree' if not bad else '%d modules differ' % bad)
    return 1 if bad or res['failed'] else 0


if __name__ == '__main__':
    sys.exit(main())
