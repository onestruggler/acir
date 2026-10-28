"""Generate the three-wire modules of CliffCS₂: `CliffordCS/W3Lemmas.lean` (the derivations of
the decoded three-qubit relations, from `cs3_cache.txt`) and `CliffordCS/W3Rels.lean` (every
refined relation of Bian and Selinger's three-qubit presentation decoded, and the round trips).

    python3 run_cs3.py && python3 gen_cs3.py
"""
import os, re, ast
import numpy as np
import cscliff as C
import cs3src as S
import leangen
from leangen import Gen as LGen
from gen_cs2 import HDR as HDR2, wrap, write, ident, lword

HDR = HDR2.replace('`gen/cs2blk.py`, `gen/cs2abs.py`', '`gen/run_cs3.py`, `gen/cs3src.py`')
SYMS = {'invol': 'Sym.invol', 'nat1 .H': '(Sym.nat1 Gate.H)', 'nat1 .S': '(Sym.nat1 Gate.S)',
        'nat2 .CS': '(Sym.nat2 Gate.CS)', 'nat2 .swap': '(Sym.nat2 Gate.swap)'}
TOPS = ['R3 c12', 'R3 c13', 'R3 c14', 'R3 c15', 'R3 c16', 'R3 c17']

class G3(LGen):
    """Axioms with an argument (SH k) parenthesised."""
    def eq(self, e):
        if e[0] == 'ax' and ' ' in e[1]:
            return 'DEqn.inst (P := pres) (S := fun _ => True) (Ax.%s) trivial %d %d' % (e[1], e[2], e[3])
        return LGen.eq(self, e)

def lemmas():
    leangen.SLIDES = True
    CACHE = ast.literal_eval(open('cs3_cache.txt', encoding='utf-8').read())
    res = {k: v[1] for k, v in CACHE.items()}
    g = G3(SYMS, 'Gate.ω', ident)
    order, seen = [], set()
    def visit(x):
        if x in seen: return
        seen.add(x)
        if res[x][3] != 'SEM':
            for e in res[x][3]:
                if e[0] == 'lem': visit(e[1])
        order.append(x)
    for t in TOPS: visit(t)
    idents = [ident(x) for x in order]
    assert len(set(idents)) == len(idents)
    out = [HDR % '''# CliffCS₂ on three wires: the decoded three-qubit relations

The decodings of Bian and Selinger's three-qubit relations (C12)–(C17),
read reversed as the paper draws them, derived from Figure 6 (`dR3_c12` …
`dR3_c17`).  Two-wire steps are either derived by rewriting (the lemmas of
Appendix E) or semantic (`dS2_*`, proved by completeness on two wires,
`complete₂`); the three-wire structure comes from (I), (SH₁), the lemmas
(C12) and (C17) of Appendix E, and the laws of the symmetry.  From (I) and
`d d = 1`: `d = b c b c`, `(b c)⁴ = 1`, `b d = d b` and `b c b = c d`
(`b`, `c`, `d` the CNOTs from wire `2` to `1`, from `1` to `0` and from `2`
to `0`), hence (P3) `b CZ₀₁ b = CZ₀₁ CZ₀₂`, which gives (C14) and (C15).''']
    out.append('''import QCert.Minimality.CliffordCS.W3Base

namespace QCert.Minimality.CliffordCS.W3

open QCert.Circuit
''')
    for nm in order:
        n, l, r, eqs, st = res[nm]
        if eqs == 'SEM':
            out.append('''/-- `%s` (semantic). -/
def %s : DEqn Th 2 :=
  sem2D (tw 2 %s)
    (tw 2 %s)
    (semrow (by decide +kernel))
''' % (nm, ident(nm), lword(l), lword(r)))
            continue
        if len(st) > 300:
            sn = ident(nm) + '_steps'
            out.append(g.steps_def(sn, st, 'The steps of `%s`.' % ident(nm)))
            pf = g.proof_named(eqs, sn, 4)
        else:
            pf = g.proof(eqs, st, 4)
        out.append('''/-- `%s`. -/
def %s : DEqn Th %d where
  lhs := tw %d %s
  rhs := tw %d %s
  proof := %s
''' % (nm, ident(nm), n, n, lword(l), n, lword(r), pf))
    out.append('end QCert.Minimality.CliffordCS.W3\n')
    write('W3Lemmas.lean', '\n'.join(out))
    print(len(order), 'derivations')

# ---------------------------------------------------------------- W3Rels.lean
def tw3(w): return 'tw 3 %s' % lword(w)

def wires(w):
    return sorted(set(o + k for (g, o) in w if g != 'w' for k in range({'H': 1, 'S': 1, 'CS': 2, 'SW': 2}[g])))

def mat3(w): return C.mat(3, w)

def proof_of(l, r, top=None):
    """A Lean proof term of `Derivable (Lift Th 3) (tw 3 l) (tw 3 r)` (both time order)."""
    assert np.allclose(mat3(l), mat3(r))
    if top is not None:
        return 'derivable_congr\' (by decide) (by decide) %s.proof' % ident(top)
    ws = sorted(set(wires(l)) | set(wires(r)))
    if set(ws) <= {0, 1}:
        return 'lo2 (u := tw 2 %s)\n        (u\' := tw 2 %s) (by decide) (by decide)\n        (semrow (by decide +kernel))' % (
            lword(l), lword(r))
    if set(ws) <= {1, 2}:
        down = lambda w: [(g, o - 1) if g != 'w' else (g, o) for (g, o) in w]
        return 'hi2s (u := tw 2 %s)\n        (u\' := tw 2 %s) (by decide) (by decide)\n        (semrow (by decide +kernel))' % (
            lword(down(l)), lword(down(r)))
    raise Exception('three wires: %s' % ((l, r),))

def deeper(text):
    """Continuation lines indented for a bullet."""
    return text.replace('\n        ', '\n          ')

def comm_proof(u, v):
    """`tw 3 (u ++ v)`-style commutation: the time words u then v, against v then u."""
    return ('derivable_congr\' (by decide) (by decide)\n        (comm_words (FreeMonoid.toList (tw 3 %s))\n'
            '          (FreeMonoid.toList (tw 3 %s)) (by decide))') % (lword(v), lword(u))

LOCAL = ['K', 'S']
def lw(A, q):
    return [(A, 2 - q)]

def rels():
    R = S.rels()
    dec = S.dec_rev
    out = [HDR % '''# CliffCS₂ on three wires: the decoded relations and the round trips

Every refined relation of Bian and Selinger's three-qubit presentation,
read reversed, decodes to a derivable equation (`rel_derivable`): those on
at most two qubits by completeness on two wires (`lo2`, `hi2s`, each
decided in the semantics), those of part (e) by commuting generators on
disjoint wires (`comm_words`), and (C12)–(C17) by `W3Lemmas`.  Decoding the
encoding of a generator derives it (`DE_gen`).''']
    out.append('''import QCert.Minimality.CliffordCS.W3Lemmas

namespace QCert.Minimality.CliffordCS.W3

open QCert.Circuit QCert.CliffordCS3
''')
    o = []
    o.append('''/-- Every refined relation of the three-qubit presentation, read reversed,
decodes to a derivable equation. -/
theorem rel_derivable : ∀ {a b : FreeMonoid (Option QCert.CliffordCS3.Gen)},
    RRel QCert.CliffordCS3.Rel gi a b → Derivable (Lift Th 3) (D a.reverse) (D b.reverse) := by
  intro a b r
  cases r with
  | src r =>
    cases r with''')
    def arm(head, proofs, ind=4):
        sp = ' ' * ind
        o.append('%s| %s =>' % (sp, head))
        return sp
    def one(key):
        l, r = R[key]
        return proof_of(dec(l), dec(r))
    # c1
    o.append('    | c1 =>\n      exact %s' % one('c1'))
    for c in ['c2', 'c3', 'c4']:
        o.append('    | %s q =>\n      fin_cases q' % c)
        for q in range(3):
            o.append('      · exact %s' % deeper(one('%s %d' % (c, q))))
    for c in ['c5', 'c6', 'c7', 'c8', 'c9', 'c10', 'c11']:
        o.append('    | %s j =>\n      fin_cases j' % c)
        for j in range(2):
            o.append('      · exact %s' % deeper(one('%s %d' % (c, j))))
    for c in ['c12', 'c13', 'c14', 'c15', 'c16', 'c17']:
        l, r = R[c]
        o.append('    | %s =>\n      exact %s' % (c, proof_of(dec(l), dec(r), top='R3 ' + c)))
    # comm_i
    o.append('    | comm_i A hA =>\n      cases A')
    for A in ['i', 'K₀', 'K₁', 'K₂', 'S₀', 'S₁', 'S₂', 'CS₀₁', 'CS₁₂']:
        if A == 'i':
            o.append('      · exact absurd rfl hA')
            continue
        l, r = R['comm_i .%s' % A]
        L0, R0 = dec(l), dec(r)
        a = S.letter(S.GENS[A][0])
        assert L0 == [('w', 0), ('w', 0)] + a
        o.append('      · exact %s' % deeper(comm_proof([('w', 0), ('w', 0)], a)))
    # comm_loc
    o.append('    | comm_loc A B q r hqr =>\n      cases A <;> cases B <;> fin_cases q <;> fin_cases r')
    for A in LOCAL:
        for Bn in LOCAL:
            for q in range(3):
                for rr in range(3):
                    if not q < rr:
                        o.append('      · exact absurd hqr (by decide)')
                        continue
                    l, r = R['comm_loc .%s .%s %d %d' % (A, Bn, q, rr)]
                    L0, R0 = dec(l), dec(r)
                    if (q, rr) == (0, 2):
                        a, b = S.letter(S.GENS[A + '₀'][0]), S.letter(S.GENS[Bn + '₂'][0])
                        assert L0 == a + b and R0 == b + a
                        o.append('      · exact %s' % deeper(comm_proof(a, b)))
                    else:
                        o.append('      · exact %s' % deeper(proof_of(L0, R0)))
    for nm, A0 in [('comm_0_12', '₀'), ('comm_2_01', '₂')]:
        o.append('    | %s A =>\n      cases A' % nm)
        for A in LOCAL:
            l, r = R['%s .%s' % (nm, A)]
            L0, R0 = dec(l), dec(r)
            a = S.letter(S.GENS[A + A0][0])
            cs = S.letter(('CSs', 0) if nm == 'comm_0_12' else ('CSs', 1))
            assert L0 == a + cs and R0 == cs + a
            o.append('      · exact %s' % deeper(comm_proof(a, cs)))
    # the refinement
    o.append('  | comm y =>\n    cases y')
    for A in ['i', 'K₀', 'K₁', 'K₂', 'S₀', 'S₁', 'S₂', 'CS₀₁', 'CS₁₂']:
        a = S.letter(S.GENS[A][0])
        o.append('    · exact %s' % comm_proof([('w', 0)], a))
    o.append('  | sq => exact Derivable.refl _\n')
    out.append('\n'.join(o))
    # DE
    o = ['''/-- Decoding the encoding of a generator derives it. -/
theorem DE_gen : ∀ g : QCert.Gen Gate 3, Derivable (Lift Th 3) (D (e g)) (FreeMonoid.of g)''']
    gens = [('.gate0 .ω', None), ('.gate1 .H', ('H', 0)), ('.gate1 .S', ('S', 0)), ('.gate2 .CS', ('CS', 0)),
            ('.gate2 .swap', ('SW', 0)), ('.up (.gate0 .ω)', 'scal1'), ('.up (.gate1 .H)', ('H', 1)),
            ('.up (.gate1 .S)', ('S', 1)), ('.up (.gate2 .CS)', ('CS', 1)), ('.up (.gate2 .swap)', ('SW', 1)),
            ('.up (.up (.gate0 .ω))', 'scal2'), ('.up (.up (.gate1 .H))', ('H', 2)),
            ('.up (.up (.gate1 .S))', ('S', 2)), ('.up (.up (.up (.gate0 .ω)))', 'scal3')]
    for pat, gl in gens:
        if gl is None:
            o.append('  | %s => Derivable.refl _' % pat); continue
        if gl == 'scal1':
            o.append('  | %s => (Derivable.of (Lift.scalar Gate.ω)).symm' % pat); continue
        if gl == 'scal2':
            o.append('  | %s => scalar_up2 (n := 1) Gate.ω' % pat); continue
        if gl == 'scal3':
            o.append('  | %s => scalar_up3 (n := 0) Gate.ω' % pat); continue
        g, w = gl
        enc = S.enc(g, w)
        L0 = S.dec_fwd(enc)
        if g in ('S', 'CS'):
            assert L0 == [gl], (gl, L0)
            o.append('  | %s => Derivable.refl _' % pat); continue
        o.append('  | %s =>\n      %s' % (pat, proof_of(L0, [gl])))
    out.append('\n'.join(o) + '\n')
    out.append('end QCert.Minimality.CliffordCS.W3\n')
    write('W3Rels.lean', '\n'.join(out))

if __name__ == '__main__':
    import sys
    if 'lemmas' in sys.argv[1:] or len(sys.argv) == 1: lemmas()
    if 'rels' in sys.argv[1:] or len(sys.argv) == 1: rels()
