"""Writes CCerts.lean: the symbols of EvenRS 8 as words of labels, the
relation, rev and closure certificates, and the action of each symbol's
word on the upper half.

Port of the Agda's gen/mk_ccerts.py, writing Lean instead of Agda.  The
certificates are computed exactly as for the Agda: this generator imports
the Agda's gen/ccerts.py (a model of CRel's decided side conditions and of
LabelEngine's moves), which runs the search of gen/c8/certgen.py for the 54
relations of EvenRS 8 (on double transpositions, then expanded and
replayed), the breadth-first searches for the rev certificates and the
closure tree; nothing is saved between runs, the whole computation taking
about ten seconds.  Like the Agda's, this generator is untrusted: Lean
checks what it writes.

Run with WSL's python3 from this folder: `python3 mk_ccerts.py`.
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent                       # Lean/QCert/XCXCCX4bit
REPO = LEAN.parents[2]                   # the repository root
AGEN = REPO / 'Examples' / 'Groups' / 'XCXCCX-4bit' / 'gen'
OUT = LEAN / 'CCerts.lean'

sys.path.insert(0, str(AGEN / 'c8'))
sys.path.insert(0, str(AGEN))
import ccerts  # noqa: E402  (the Agda's model and searches)
from ccerts import phiQ, SYMS, MU0_IDX, BASE_SYMS, BASE_MOVES  # noqa: E402


def labs(ls):
    return '[' + ', '.join('%d' % i for i in ls) + ']'


def move(m):
    k = m[0]
    if k in ('H', 'Hi', 'C', 'K'):
        return 'Move.%s %d' % (k, m[1])
    if k == 'I':
        return 'Move.I %d %d' % (m[1], m[2])
    if k == 'Ki':
        return 'Move.Ki %d %d %d' % (m[1], m[2], m[3])
    raise ValueError(m)


def moves(ms, indent):
    """A list of moves, wrapped at 100 columns, continuation lines indented
    to `indent` + 1."""
    if not ms:
        return '[]'
    items = [move(m) for m in ms]
    out, line = [], '['
    for k, it in enumerate(items):
        piece = it + (', ' if k + 1 < len(items) else ']')
        if indent + len(line) + len(piece) > 98 and line.strip('['):
            out.append(line.rstrip())
            line = ''
        line += piece
    out.append(line)
    return ('\n' + ' ' * (indent + 1)).join(out)


def b(c):
    return 'true' if c else 'false'


def sym_term(x):
    c, d = x
    return 'sy %s %d' % (b(c), d)


def lemma(name, ms, lw, rw):
    """A certificate as a lemma of its own: one Boolean, decided by the
    kernel in a declaration of its own."""
    head = 'private theorem %s : 4 ⊢ Xs %s ≈ Xs %s :=' % (name, labs(lw), labs(rw))
    if len(head) > 100:
        head = 'private theorem %s :\n    4 ⊢ Xs %s ≈ Xs %s :=' % (name, labs(lw), labs(rw))
    return ('%s\n  check_sound\n    %s\n    _ _ (by decide +kernel)'
            % (head, moves(ms, 4)))


def cert_call(ms, lw, rw, ind=2):
    """`check_sound ms lw rw (by decide +kernel)`, the call at `ind`, its
    arguments two further in."""
    a = ' ' * (ind + 2)
    return ('%scheck_sound\n%s%s\n%s%s\n%s%s\n%s(by decide +kernel)'
            % (' ' * ind, a, moves(ms, ind + 2), a, labs(lw), a, labs(rw), a))


def main():
    certs = ccerts.relation_certificates()
    revs = ccerts.rev_certificates()
    par = ccerts.closure()
    o = [HDR]

    o.append('/-! ## The symbols as words of labels -/')
    o.append('')
    o.append('/-- The word of labels of a symbol. -/')
    o.append('def Φ : Sch 8 → List L')
    for c, d in SYMS:
        o.append('  | ⟨%s, %d, _, _⟩ => %s' % (b(c), d, labs(phiQ(c, d))))
    o.append('  | _ => []')
    o.append('')
    o.append(PHISTAR)

    o.append('/-! ## The action of each symbol on the upper half -/')
    o.append('')
    o.append('theorem Φ_act_ok : ∀ x : Sch 8,')
    o.append('    allFin 8 (fun i => eqV (mFs (Φ x) (enc8 i)) (enc8 (Symmetric.perm (f 8 x) i))) = true')
    o.append('  | ⟨_, 0, p, _⟩ => absurd p (by decide)')
    for c, d in SYMS:
        x = '(%s)' % sym_term((c, d))
        o.append('  | ⟨%s, %d, _, _⟩ => (by decide +kernel : allFin 8 (fun i =>' % (b(c), d))
        o.append('      eqV (mFs (Φ %s) (enc8 i)) (enc8 (Symmetric.perm (f 8 %s) i))) = true)'
                 % (x, x))
    o.append('  | ⟨_, _ + 7, _, q⟩ => absurd q (by omega)')
    o.append('')

    o.append('/-! ## The relations of EvenRS 8, certified -/')
    o.append('')
    pats = []
    for name, l, r, lw, rw, ms in certs:
        k = name[0]
        if k == 'order':
            pat = '.order %s %d _ _' % (b(name[1]), name[2])
            nm = 'R_order_%s%d' % (b(name[1])[0], name[2])
        elif k == 'braid0':
            pat = '.braid₀ %s _' % b(name[1])
            nm = 'R_braid₀_%s' % b(name[1])[0]
        elif k == 'braid':
            pat = '.braid %s %d _ _' % (b(name[1]), name[2])
            nm = 'R_braid_%s%d' % (b(name[1])[0], name[2])
        elif k == 'far0':
            pat = '.far₀ %s %d _ _' % (b(name[1]), name[2])
            nm = 'R_far₀_%s%d' % (b(name[1])[0], name[2])
        else:
            pat = '.far %s %d %d _ _ _' % (b(name[1]), name[2], name[3])
            nm = 'R_far_%s%d_%d' % (b(name[1])[0], name[2], name[3])
        o.append(lemma(nm, ms, lw, rw))
        o.append('')
        pats.append((pat, nm))
    o.append('theorem R_rel : ∀ {u v : Word (Sch 8)}, RSRel 8 u v → 4 ⊢ Xs (Φs u) ≈ Xs (Φs v)')
    for pat, nm in pats:
        o.append('  | _, _, %s => %s' % (pat, nm))
    o.append('  | _, _, .order _ 0 p _ => absurd p (by decide)')
    o.append('  | _, _, .order _ (_ + 7) _ q => absurd q (by omega)')
    o.append('  | _, _, .braid _ 0 p _ => absurd p (by decide)')
    o.append('  | _, _, .braid _ (_ + 6) _ q => absurd q (by omega)')
    o.append('  | _, _, .far₀ _ 0 p _ => absurd p (by decide)')
    o.append('  | _, _, .far₀ _ 1 p _ => absurd p (by decide)')
    o.append('  | _, _, .far₀ _ (_ + 7) _ q => absurd q (by omega)')
    o.append('  | _, _, .far _ 0 _ p _ _ => absurd p (by decide)')
    for d in range(1, 5):
        for e in range(0, d + 2):
            o.append('  | _, _, .far _ %d %d _ q _ => absurd q (by decide)' % (d, e))
        o.append('  | _, _, .far _ %d (_ + 7) _ _ r => absurd r (by omega)' % d)
    o.append('  | _, _, .far _ (_ + 5) _ _ q r => (by omega : False).elim')
    o.append('')

    o.append('/-! ## A symbol reversed is the inverse symbol -/')
    o.append('')
    o.append('/-- The inverse symbol. -/')
    o.append('def inv_sym : Sch 8 → Sch 8')
    o.append('  | ⟨c, d, p, q⟩ => ⟨!c, d, p, q⟩')
    o.append('')
    for c, d in SYMS:
        a = list(reversed(phiQ(c, d)))
        bb = phiQ(not c, d)
        o.append(lemma('rev_%s%d' % (b(c)[0], d), revs[(c, d)], a, bb))
        o.append('')
    o.append('theorem rev_ok : ∀ x : Sch 8, 4 ⊢ Xs (Φ x).reverse ≈ Xs (Φ (inv_sym x))')
    o.append('  | ⟨_, 0, p, _⟩ => absurd p (by decide)')
    for c, d in SYMS:
        o.append('  | ⟨%s, %d, _, _⟩ => rev_%s%d' % (b(c), d, b(c)[0], d))
    o.append('  | ⟨_, _ + 7, _, q⟩ => absurd q (by omega)')
    o.append('')

    o.append('/-! ## The closure: every label from μ₀ by symbols -/')
    o.append('')
    o.append('def μ₀ : L := %d' % MU0_IDX)
    o.append('')
    o.append('/-- `γ₂ γ₄ γ₆` is `μ₀`: the product of the double transpositions')
    o.append('`(0 1)(2 3)`, `(0 1)(4 5)` and `(0 1)(6 7)`. -/')
    o.append('def base_word : Word (Sch 8) :=')
    o.append('  FreeMonoid.of (%s) * (FreeMonoid.of (%s) * FreeMonoid.of (%s))'
             % tuple(sym_term(x) for x in BASE_SYMS))
    o.append('')
    o.append('theorem base_ok : 4 ⊢ Xs (Φs base_word) ≈ Xs [μ₀] :=')
    o.append(cert_call(BASE_MOVES, ccerts.phiQs(BASE_SYMS), [MU0_IDX]))
    o.append('')
    o.append('/-- The tree: each label but `μ₀` is its parent conjugated by the')
    o.append('word of a symbol, one level deeper. -/')
    o.append('def parT : List L :=')
    o.append(wrap([str(par[m][0]) for m in range(105)], 2))
    o.append('')
    o.append('def symT : List (Sch 8) :=')
    o.append(wrap([sym_term(par[m][1]) for m in range(105)], 2))
    o.append('')
    o.append('def depT : List ℕ :=')
    o.append(wrap([str(par[m][2]) for m in range(105)], 2))
    o.append('')
    o.append(TAIL)
    with open(OUT, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write('\n'.join(o) + '\n')
    print('wrote', OUT)


def wrap(items, indent):
    """A list literal, wrapped at 100 columns."""
    out, line = [], ' ' * indent + '['
    for k, it in enumerate(items):
        piece = it + (', ' if k + 1 < len(items) else ']')
        if len(line) + len(piece) > 99 and line.strip(' ['):
            out.append(line.rstrip())
            line = ' ' * (indent + 1)
        line += piece
    out.append(line)
    return '\n'.join(out)


HDR = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Certificates for the controlled A₈

Translation of `CCerts.agda`.  The controlled matchings generate, on the
upper half of the states, the even permutations of the eight Gray
positions, which `EvenRS 8` presents by symbols `γ c d`.  Each symbol is a
word of two or four labels (`Φ`, after the canonical factorisation of a
double transposition into two commuting matchings, with the auxiliary pair
`(6 7)` for `d = 1`) whose matchings compose to `f (γ c d)` (`Φ_act_ok`,
decided on the eight positions).  Each relation of `EvenRS 8` is a
certificate of `LabelEngine` between the words of its two sides (`R_rel`;
found by the Agda's `gen/c8/certgen.py` on double transpositions and
expanded), a symbol's word reversed is the word of the inverse symbol
(`rev_ok`), and every label is reached from `μ₀ = Φ (γ₂ γ₄ γ₆)` by
conjugating with the words of symbols, along a breadth-first tree (`parT`,
`symT`, `depT`, checked by `closure_all`).

Names.  The Agda's `Φ*`, `Φ-act-ok`, `R-rel`, `inv-sym`, `rev-ok`,
`base-word`, `base-ok`, `sym-of`, `conjs-ok`, `closure-ok`, `closure-all`
are `Φs`, `Φ_act_ok`, `R_rel`, `inv_sym`, `rev_ok`, `base_word`, `base_ok`,
`sym_of`, `conjs_ok`, `closure_ok`, `closure_all`; the moves are
`LabelEngine.Move`'s constructors, written `Move.H 3`; `check`, `Xs`,
`Xs_append` and `check_sound` are `LabelEngine`'s at the labels, the side
conditions of `CRel` and the relations of `CBC` (the Agda opens the
modules `LabelEngine` and `LabelEngine.Sound` with those arguments).

**Deviations from the Agda.**  Each certificate is one Boolean
(`LabelEngine.check`), decided by `decide +kernel` (the Agda's `refl`), in
a private lemma of its own (`R_order_f1`, …, `R_far_t4_6`, `rev_f1`, …,
`rev_t6`), which `R_rel` and `rev_ok` dispatch to: as clauses of one
definition the checks exhausted its heartbeats.  `Φ_act_ok` is decided for
each symbol over the eight positions at once.  The tables `parT`, `symT`,
`depT` are lists read by `List.getD` (the Agda's `Vec`s read by `lookup`).

Generated by `gen/mk_ccerts.py` (the port of the Agda's
`gen/mk_ccerts.py`, from the Agda's `gen/ccerts.py`).
-/
import QCert.XCXCCX4bit.CBC
import QCert.XCXCCX4bit.CSem
import QCert.XCXCCX4bit.LabelEngine
import QCert.XCXCCX4bit.EvenRS

namespace QCert.XCXCCX4bit.CCerts

open QCert QCert.Circuit CircuitProp IndepProp
open EvenRS CRel CSem
open LabelEngine (Move)

/-- A certificate over the labels (the Agda's `check`, from `LabelEngine`
opened at the labels). -/
abbrev check (ms : List (Move L)) (l r : List L) : Bool :=
  LabelEngine.check eqLab c3 conj_ok mul klein_ok ms l r

/-- A word of labels as a circuit: the controlled matchings in order. -/
abbrev Xs (ws : List L) : Circ 4 := LabelEngine.Xs Xm ws

theorem Xs_append (xs ys : List L) : Xs (xs ++ ys) = Xs xs * Xs ys :=
  LabelEngine.Xs_append Xm xs ys

/-- A checked certificate is a derivation. -/
theorem check_sound (ms : List (Move L)) (l r : List L) (h : check ms l r = true) :
    4 ⊢ Xs l ≈ Xs r :=
  LabelEngine.check_sound eqLab_sound CBC.X_inv CBC.X_conj CBC.X_klein ms l r h

/-- A symbol with its bounds decided. -/
def sy (c : Bool) (d : ℕ) (p : 1 ≤ d := by decide) (q : 2 + d ≤ 8 := by decide) : Sch 8 :=
  ⟨c, d, p, q⟩
'''

PHISTAR = '''/-- A word of symbols as a word of labels (the Agda's `Φ*`). -/
def Φs (w : Word (Sch 8)) : List L := (FreeMonoid.toList w).flatMap Φ

theorem Φs_mul (u v : Word (Sch 8)) : Φs (u * v) = Φs u ++ Φs v := by
  simp [Φs]

theorem Φs_one : Φs 1 = [] := rfl

theorem Φs_of (x : Sch 8) : Φs (FreeMonoid.of x) = Φ x := by
  simp [Φs]
'''

TAIL = '''def par (μ : L) : L := parT.getD μ.1 μ₀

def sym_of (μ : L) : Sch 8 := symT.getD μ.1 (sy false 1)

def dep (μ : L) : ℕ := depT.getD μ.1 0

/-- Conjugation by a word of labels, the last letter innermost. -/
def star : List L → L → L
  | [], ν => ν
  | w :: ws, ν => c3 w (star ws ν)

/-- The side conditions of the steps of `star`. -/
def conjs_ok : List L → L → Bool
  | [], _ => true
  | w :: ws, ν => conj_ok w (star ws ν) && conjs_ok ws ν

/-- The step of the tree at a label of the given depth. -/
def cstep (μ : L) : ℕ → Bool
  | 0 => eqLab μ μ₀
  | n + 1 => Nat.beq (dep (par μ)) n &&
      (conjs_ok (Φ (sym_of μ)) (par μ) && eqLab (star (Φ (sym_of μ)) (par μ)) μ)

def closure_ok (μ : L) : Bool := cstep μ (dep μ)

theorem closure_all : allFin 105 closure_ok = true := by decide +kernel

end QCert.XCXCCX4bit.CCerts'''

if __name__ == '__main__':
    main()
