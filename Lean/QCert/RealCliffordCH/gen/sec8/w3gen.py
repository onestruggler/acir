"""Write Sec8/D/W3.lean: Lemma D.2 at width 3 as engine runs.

    python w3gen.py D2.json OUT.lean [EQ ...]

Plans: the paper's chain for each equation (parsed by chains.py), each step turned into
engine steps by w3.Prover; (117), (118) cancel letter by letter (Lemma B.2); (120),
(122), (138) are mirror images of (119), (121), (136) (Lemma B.3); (137) is (136)
conjugated by X on wire 2 ((81)); (129)'s chain ends one diagram early (its last one is
a stray).  The table of each run holds the rules it uses ((12)-(18), (f3), (f4), their
mirror images, each proved by its own run) and the D.2 equations proved before.  An
equation whose run is not complete keeps its `sorry`.
"""
import json
import sys

import eng3
import letters as LT
import w3

N = 2
X2 = [('H', 2), ('Z', 2), ('H', 2)]
RULE_CTOR = {'e12': 'e12', 'e13': 'e13', 'e14': 'e14', 'e15': 'e15', 'e16': 'e16', 'e17': 'e17',
             'e18': 'e18', 'f3': 'f3', 'f4': 'f4'}


def lw(w):
    return '[' + ', '.join(f'L.{a} {j}' for a, j in w) + ']'


class Gen:
    def __init__(self, d):
        self.d = d
        self.stw = w3.statement_words(d)
        self.table = list(w3.RULES)
        for name, l, r in w3.RULES:
            self.table.append((name + 'm', l[::-1], r[::-1]))
        order = [str(n) for n in range(117, 148)] + ['148a', '148b']
        for n in order:
            self.table.append(('d' + n, self.stw[n][0], self.stw[n][1]))
        # conjugates of the D.2 equations by X on one wire ((81)): derived entries
        self.derived = {}
        eng0 = eng3.Engine(N, [(l, r) for _, l, r in self.table])
        for n in order:
            k = self.index_of('d' + n)
            for j in range(3):
                xg = [('H', j), ('Z', j), ('H', j)]
                l2, r2, st = w3.conj_variant(eng0, k, self.table[k][1], self.table[k][2], xg)
                name = f'd{n}x{j}'
                self.derived[name] = (k, st)
                self.table.append((name, l2, r2))
        self.index = {name: k for k, (name, _, _) in enumerate(self.table)}
        self.pr = w3.Prover(self.table)
        self.eng = self.pr.eng
        self.runs = {}

    def index_of(self, name):
        return next(k for k, t in enumerate(self.table) if t[0] == name)

    def chain_run(self, ws, cites, log):
        steps = []
        for i, (u, v) in enumerate(zip(ws, ws[1:])):
            try:
                st = self.pr.step(u, v, cites[i] if i < len(cites) else [])
            except w3.Fail:
                log.append(i)
                return None
            assert self.pr.check(u, st, v)
            steps += st
        return steps

    def plan(self, n):
        l, r = self.stw[n]
        if n in ('117', '118'):
            k = len(l) // 2
            assert l[k:] == l[:k][::-1] and r == []
            return w3.cancel_pairs(0, l[:k])
        if n in ('120', '122', '138'):
            m = {'120': '119', '122': '121', '138': '136'}[n]
            lm, rm = self.stw[m]
            k = self.index['d' + m]
            st = w3.mirror_run(k, lm, rm)          # rev lm -> rev rm
            if l == lm[::-1] and r == rm[::-1]:
                return st
            if l == rm[::-1] and r == lm[::-1]:
                return eng3.reverse_steps(self.eng, lm[::-1], st)
            return None
        if n == '137':
            l6, r6 = self.stw['136']
            ws = [l, X2 + X2 + l + X2 + X2, X2 + l6 + X2, X2 + r6 + X2, r]
            log = []
            return self.chain_run(ws, [[], [], ['136'], []], log)
        ch = self.d['proofs'].get(n, [None])[0]
        if ch is None:
            return None
        ws = [w3.words_of(D) for D in ch['diags']]
        cites = ch['cites']
        if n == '129':
            ws = ws[:-1]
        # the chain's ends against the statement's words (same operators; the words may be
        # spelled differently): one more step at either end
        if ws[0] != l:
            ws = [l] + ws
            cites = [[]] + cites
        if ws[-1] != r:
            ws = ws + [r]
        log = []
        st = self.chain_run(ws, cites, log)
        if st is None:
            print(n, 'fails at step', log)
        return st

    def run_all(self, only=None):
        for n in [str(k) for k in range(117, 148)]:
            if only and n not in only:
                continue
            st = self.plan(n)
            if st is None:
                print(n, 'no run')
                continue
            w, bad = self.eng.run(self.stw[n][0], st)
            assert w == self.stw[n][1], n
            # only earlier equations may be used
            used = {s[2] for s in st if s[0] == 'rw'}
            later = [self.table[k][0] for k in used if self.table[k][0][0] == 'd'
                     and int(self.table[k][0][1:4]) >= int(n)]
            if later:
                print(n, 'uses later', later)
                continue
            missing = [self.table[k][0] for k in used if self.table[k][0][0] == 'd'
                       and w3.base(self.table[k][0])[1:] not in self.runs]
            if missing:
                print(n, 'uses unproved', missing)
                continue
            self.runs[n] = st
            print(n, 'ok', len(st), 'steps')

    # ------------------------------------------------------------------ Lean
    def lean_table(self, used):
        """(entries, proofs) for the table entries `used` (global indices)."""
        entries, proofs = [], []
        for k in used:
            name, l, r = self.table[k]
            entries.append(f'({lw(l)}, {lw(r)})')
            if name in self.derived:
                self.used_derived.add(name)
                proofs.append(f't_{name} ih')
            elif name in RULE_CTOR:
                proofs.append(f't_{name}')
            elif name.endswith('m') and name[:-1] in RULE_CTOR:
                proofs.append(f't_{name} ih')
            else:
                proofs.append(f'{name} ih')
        return entries, proofs

    def lean_run(self, name, lhs, rhs, st, unfold=None):
        used = sorted({s[2] for s in st if s[0] == 'rw'})
        loc = {k: i for i, k in enumerate(used)}
        steps = []
        for s in st:
            if s[0] == 'rw':
                steps.append(('rw', s[1], loc[s[2]], s[3]))
            else:
                steps.append(s)
        entries, proofs = self.lean_table(used)
        ss = ', '.join(eng3.lean_steps(steps))
        out = []
        tbl = '[' + ', '.join(entries) + ']'
        if used:
            pf = '\n    '.join(f'· exact {p}' for p in proofs)
            pats = ' | '.join(['rfl'] * len(used))
            tproof = (f'(by\n    intro e he\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at he\n'
                      f'    rcases he with {pats}\n    {pf})')
        else:
            tproof = '(fun _ h => by simp at h)'
        body = (f'check_sound ih (T := {tbl})\n    {tproof}\n'
                f'    (w := {lw(lhs)}) (v := {lw(rhs)})\n    (ss := [{ss}])\n    (by decide +kernel)')
        return body

    def emit(self, path):
        out = [HEADER]
        # the rules
        for name, l, r in w3.RULES:
            opt = 'set_option maxRecDepth 20000 in\n' if name == 'e15' else ''
            out.append(f'{opt}theorem t_{name} : Derivable (theory 3) (circW 3 {lw(l)}) (circW 3 {lw(r)}) :=\n'
                       f'  derivable_rule Rule.{RULE_CTOR[name]} 0\n')
        for k, (name, l, r) in enumerate(w3.RULES):
            st = w3.mirror_run(k, l, r)
            # the mirror run uses table index k (the rule itself)
            body = self.lean_run(name + 'm', l[::-1], r[::-1], st)
            out.append(f'/-- ({name[1:]}) read right to left (its mirror image, Lemma B.3). -/\n'
                       f'theorem t_{name}m (ih : IH 3) :\n'
                       f'    Derivable (theory 3) (circW 3 {lw(l[::-1])}) (circW 3 {lw(r[::-1])}) :=\n  {body}\n')
        self.used_derived = set()
        bodies = {}
        for n in [str(k) for k in range(117, 148)] + ['148a', '148b']:
            if n in self.runs:
                l, r = self.stw[n]
                bodies[n] = self.lean_run('d' + n, l, r, self.runs[n])
        # the derived entries the runs use, right after the equation they come from
        derived_after = {}
        for name in sorted(self.used_derived):
            k, st = self.derived[name]
            _, l2, r2 = self.table[self.index[name]]
            body = self.lean_run(name, l2, r2, st)
            src = w3.base(name)[1:]
            derived_after.setdefault(src, []).append(
                f'/-- ({src}) conjugated by `X` on wire {name[-1]} ((81)). -/\n'
                f'theorem t_{name} (ih : IH 3) :\n'
                f'    Derivable (theory 3) (circW 3 {lw(l2)}) (circW 3 {lw(r2)}) :=\n  {body}\n')
        for n in [str(k) for k in range(117, 148)] + ['148a', '148b']:
            if n in self.runs:
                out.append(f'theorem d{n} (ih : IH 3) : Derivable (theory 3) l{n} r{n} := by\n'
                           f'  unfold l{n} r{n}\n  exact {bodies[n]}\n')
            else:
                out.append(f'theorem d{n} (ih : IH 3) : Derivable (theory 3) l{n} r{n} := by\n  sorry\n')
            out += derived_after.get(n, [])
        out.append('end QCert.RealCliffordCH.Sec8.D\n')
        with open(path, 'w', encoding='utf-8', newline='\n') as f:
            f.write('\n'.join(out))


HEADER = """/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.2 at width 3 (package (i))

The equations (117)–(148) of `SmallDefs` derived on three wires from the
equations of Figure 4, with completeness on two wires (`IH 3`), as runs of
the engine of `EngineN` decided by `decide +kernel`.  Generated by
`gen/sec8/w3gen.py` from the paper's derivations (parsed from the figures by
`gen/sec8/figparse.py`): each step of the paper becomes engine steps —
semantic windows on two wires (Lemma 7.6 and the one- and two-wire
equations), exchanges of disjoint letters, and rewrites with the three-wire
equations (12)–(18), (f3), (f4) (`t_…`), their mirror images (`t_…m`,
Lemma B.3) and the equations of D.2 proved before.  (117), (118) cancel
letter by letter (Lemma B.2); (120), (122), (138) are the mirror images of
(119), (121), (136); (137) is (136) conjugated by `X` on wire 2 ((81)).
-/
import QCert.RealCliffordCH.Sec8.D.SmallDefs

namespace QCert.RealCliffordCH.Sec8.D

open Circuit Eng
"""


if __name__ == '__main__':
    d = json.load(open(sys.argv[1], encoding='utf-8'))
    g = Gen(d)
    g.run_all(sys.argv[3:] or None)
    g.emit(sys.argv[2])
