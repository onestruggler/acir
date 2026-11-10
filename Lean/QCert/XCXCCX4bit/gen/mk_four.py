"""Writes Four.lean: completeness on four wires from the faithfulness of the
circuits that keep wire 3 (the top layer).

Port of the Agda's gen/mk_four.py, writing Lean instead of Agda.  It imports
the Agda's generator for its data, which that module computes when imported
(and writes nothing): the Gray numbering `G` and the wires `T` it flips, the
realisations `R` of the symbols of EvenRS 16 (found by breadth-first
search), the translations `BASIC` of the letters by Coxeter words in a Young
subgroup, and the three-wire steps `EXC` for the four letters in none.  Like
the Agda's, it is untrusted: Lean checks what it writes.

Run with WSL's python3 from this folder: `python3 mk_four.py`.
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent                       # Lean/QCert/XCXCCX4bit
REPO = LEAN.parents[2]                   # the repository root
AGEN = REPO / 'Examples' / 'Groups' / 'XCXCCX-4bit' / 'gen'
OUT = LEAN / 'Four.lean'

sys.path.insert(0, str(AGEN))
import mk_four as ag  # noqa: E402  (the Agda generator, for its data)

N = ag.N
G = ag.G
T = ag.T
ALL = ag.ALL
R = ag.R
BASIC = ag.BASIC
EXC = ag.EXC
SUB = {0: '₀', 1: '₁', 2: '₂', 3: '₃'}


def letter(l):
    if l[0] == 'X':
        return 'PG.Xₚ %d' % l[1]
    if l[0] == 'CX':
        return 'PG.CXₚ %d %d' % (l[1], l[2])
    return 'PG.CCXₚ %d %d %d' % (l[1], l[2], l[3])


def pattern(l):
    if l[0] == 'X':
        return '.Xₚ %d' % l[1]
    if l[0] == 'CX':
        return '.CXₚ %d %d _' % (l[1], l[2])
    return '.CCXₚ %d %d %d _' % (l[1], l[2], l[3])


def wrap(items, indent, first, last, start=None):
    """`first`, the items separated by ', ', `last`, the first line starting at
    column `start` (default `indent`), wrapped at 100 columns with
    continuation lines indented by `indent`."""
    start = indent if start is None else start
    out, line = [], first
    for k, it in enumerate(items):
        piece = it + (', ' if k + 1 < len(items) else last)
        col = indent if out else start
        if col + len(line) + len(piece) > 100 and line.strip(' [('):
            out.append(line.rstrip())
            line = ''
        line += piece
    out.append(line)
    return ('\n' + ' ' * indent).join(out)


def lean_list(w, col):
    """A list of letters starting at column `col`."""
    if not w:
        return '[]'
    return wrap([letter(l) for l in w], col + 1, '[', ']', start=col)


def lname(l):
    return 'ok_' + l[0] + ''.join(SUB[x] for x in l[1:])


def bool_(c):
    return 'false' if c == 0 else 'true'


def sch_word(sch, col):
    if not sch:
        return '1'
    return wrap(['(%s, %d)' % (bool_(c), d) for c, d in sch], col + 5, 'syw [', ']', start=col)


def bits(s):
    return ' ∷ '.join('true' if (s >> w) & 1 else 'false' for w in range(4)) + ' ∷ .nil'


def gen():
    out = []
    o = out.append
    o(HDR)
    o('/-! ## The states, numbered along the reflected Gray code -/')
    o('')
    o('def enc : Fin 16 → Bits 4')
    for i in range(N):
        o('  | %d => %s' % (i, bits(G[i])))
    o('  | ⟨k + 16, h⟩ => absurd h (by omega)')
    o('')
    o('def dec : Bits 4 → Fin 16')
    for i in range(N):
        o('  | %s => %d' % (bits(G[i]), i))
    o('')
    o('theorem dec_enc : ∀ i, dec (enc i) = i := by decide')
    o('')
    o('theorem enc_dec : ∀ x, enc (dec x) = x')
    for i in range(N):
        o('  | %s => rfl' % bits(G[i]))
    o('')
    o('/-- The wire on which the states `d` and `d + 1` differ. -/')
    o('def t : ℕ → Wire')
    for d in range(N - 1):
        o('  | %d => %d' % (d, T[d]))
    o('  | _ => 0')
    o('')
    o('/-! ## The symbols as words of letters that target wires 0 and `t d` only -/')
    o('')
    o('def R : Sch 16 → List PG')
    for d in range(1, N - 1):
        for c in (0, 1):
            lead = '  | ⟨%s, %d, _, _⟩ => ' % (bool_(c), d)
            o(lead + lean_list(R[(c, d)], len(lead)))
    o('  | _ => []')
    o('')
    o('theorem R_act : ∀ (x : Sch 16) (i : Fin 16),')
    o('    semPs (R x) (enc i) = enc (Symmetric.perm (f 16 x) i)')
    o('  | ⟨_, 0, p, _⟩, _ => absurd p (by decide)')
    for d in range(1, N - 1):
        for c in (0, 1):
            x = '(sy %s %d)' % (bool_(c), d)
            o('  | ⟨%s, %d, _, _⟩, i => (by decide +kernel : ∀ i : Fin 16,' % (bool_(c), d))
            o('      semPs (R %s) (enc i) = enc (Symmetric.perm (f 16 %s) i)) i' % (x, x))
    o('  | ⟨_, _ + 15, _, q⟩, _ => absurd q (by omega)')
    o('')
    o('theorem R_tgt : ∀ (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ 16),')
    o('    every (targets 0 (t d)) (R ⟨c, d, p, q⟩) = true')
    o('  | _, 0, p, _ => absurd p (by decide)')
    for d in range(1, N - 1):
        for c in (0, 1):
            o('  | %s, %d, _, _ => rfl' % (bool_(c), d))
    o('  | _, _ + 15, _, q => absurd q (by omega)')
    o('')
    o(MID)
    o('/-! ## Every letter as a word in the symbols -/')
    o('')
    o('def tw₀ : PG → Word (Sch 16)')
    for l, (m, sch) in BASIC.items():
        lead = '  | %s => ' % pattern(l)
        o(lead + sch_word(sch, len(lead)))
    o('  | _ => 1')
    o('')
    o(TWL)
    o('def tw₁ : PG → Word (Sch 16)')
    for l, m, us in EXC[:3]:
        lead = '  | %s => twL₀ ' % pattern(l)
        o(lead + lean_list(us, len(lead)))
    o('  | g => tw₀ g')
    o('')
    o(TWL1)
    o('def tw : PG → Word (Sch 16)')
    l, m, us = EXC[3]
    lead = '  | %s => twL₁ ' % pattern(l)
    o(lead + lean_list(us, len(lead)))
    o('  | g => tw₁ g')
    o('')
    o('section Letters')
    o('')
    o('variable (f₃ : Faithful 3)')
    o('include f₃')
    o('')
    for l, (m, sch) in BASIC.items():
        o('theorem %s : 4 ⊢ ι (%s) ≈ ιs (RL.Rs (tw₀ (%s))) :=' % (lname(l), letter(l), letter(l)))
        o('  basic f₃ (%s) %d rfl (by decide +kernel) (by decide +kernel)' % (letter(l), m))
        o('')
    for l, m, us in EXC:
        twn = 'tw' if l == EXC[3][0] else 'tw₁'
        okn, con = ('okL₁', 'Oks₁') if l == EXC[3][0] else ('okL₀', 'Oks₀')
        o('theorem %s : 4 ⊢ ι (%s) ≈ ιs (RL.Rs (%s (%s))) :=' % (lname(l), letter(l), twn, letter(l)))
        o('  viaN (%s) %d' % (letter(l), m))
        o('    ' + lean_list(us, 4))
        o('    (%s (%s)) rfl rfl (by decide +kernel)' % (twn, letter(l)))
        toks = ['(%s' % okn, '_'] + ['(.cons (%s f₃)' % lname(u) for u in us]
        toks.append('.nil' + ')' * (len(us) + 1))
        lines, line = [], '    '
        for tk in toks:
            if len(line) + len(tk) + 1 > 100 and line.strip():
                lines.append(line.rstrip())
                line = '      '
            line += tk + ' '
        lines.append(line.rstrip())
        o('\n'.join(lines))
        o('')
    o('theorem tw_ok : ∀ g, 4 ⊢ ι g ≈ ιs (RL.Rs (tw g))')
    for l in ALL:
        o('  | %s => %s f₃' % (pattern(l), lname(l)))
    valid = set(ALL)
    for c in range(4):
        o('  | .CXₚ %d %d ok => nomatch ok' % (c, c))
    for a in range(4):
        for b in range(4):
            for w in range(4):
                if ('CCX', a, b, w) not in valid:
                    o('  | .CCXₚ %d %d %d ok => nomatch ok' % (a, b, w))
    o('')
    o(END)
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(out) + '\n')
    print('wrote', OUT)


HDR = r'''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness on four wires, from the faithfulness of the circuits that keep wire 3

Translation of `Four.agda`: `ByEvenRS` for the numbering of the 16 states
along the reflected Gray code, so that the transposition `s_d` of the states
`d` and `d + 1` flips one wire `t d`.  The symbol `γ c d` of `A₁₆` (`s_d s_0`
or `s_0 s_d`) is realised by a word whose letters target wires 0 and `t d`
only (`R`, found by breadth-first search; `R_act` checks it), so it keeps
the other two wires.  A relation of `A₁₆` involves at most two values of
`t` besides 0, so all its symbols keep a wire `m` in {1, 2, 3} (`pick`), and
`Faithful m`, from the hypothesis by relabelling, decides it (`R_rel`, five
generic clauses).  Every placed letter is a word in the symbols (`tw`): by
a Coxeter word inside the Young subgroup of the positions that preserves a
wire `m` that the letter keeps, so that `Faithful m` decides the
translation, or, for the four letters in no such subgroup (`X₃`, `CX₀₃`,
`CX₁₃`, `CCX₀₁₃`), by a three-wire step into letters translated before
(`viaN`).  So two words of placed letters with the same function are equal,
and so are two circuits (`complete₄`).

**Deviations from the Agda.**

* The Agda's module parameter `f₃ : Faithful ₃` is an argument of the
  theorems that use it (`R_rel`, `basic`, the `ok_…` lemmas, `tw_ok`,
  `complete`, `complete₄`).
* `R_act` is decided for each symbol over the 16 states (one `decide
  +kernel` per symbol), where the Agda has one `refl` per symbol and state.
* A word of symbols `[ sy c d ]ʷ • …` is `syw [(c, d), …]`, its bounds
  decided by the function (`sy c d` is a single symbol, its bounds
  auto-parameters).
* `R_rel` puts the Agda's five clauses through one lemma, `rel_by`: the
  symbols of a relation flip at most the wires `a` and `b`, so they keep
  `pick a b`.
* `ByEvenRS`'s module `Realisation` is the structure value `RL`.

Generated by `gen/mk_four.py` (the port of the Agda's `gen/mk_four.py`).
-/
import QCert.XCXCCX4bit.ByEvenRS
import QCert.XCXCCX4bit.Faithful
import QCert.XCXCCX4bit.Narrow3

namespace QCert.XCXCCX4bit.Four

open QCert QCert.Circuit CircuitProp IndepProp
open Placed ToPlaced Faithful EvenRS ByEvenRS

/-- A symbol with its bounds decided. -/
def sy (c : Bool) (d : ℕ) (p : 1 ≤ d := by decide) (q : 2 + d ≤ 16 := by decide) : Sch 16 :=
  ⟨c, d, p, q⟩

/-- A word of symbols, its bounds decided (the symbols out of bounds left
out). -/
def syw (l : List (Bool × ℕ)) : Word (Sch 16) :=
  FreeMonoid.ofList (l.filterMap fun x =>
    if h : 1 ≤ x.2 ∧ 2 + x.2 ≤ 16 then some ⟨x.1, x.2, h.1, h.2⟩ else none)
'''

MID = r'''/-! ## The relations -/

/-- The realisation of the symbols. -/
def RL : Realisation := ⟨enc, dec, dec_enc, enc_dec, R, R_act⟩

/-- A wire in {1, 2, 3} other than `a` and `b`. -/
def pick : Wire → Wire → Wire
  | 3, 3 => 2
  | 3, 2 => 1
  | 2, 3 => 1
  | 3, _ => 2
  | _, 3 => 2
  | _, _ => 3

theorem pick_ok : ∀ a b : Wire,
    (!weq (pick a b) 0) = true ∧ (!weq (pick a b) a) = true ∧ (!weq (pick a b) b) = true := by
  decide

/-- A symbol keeps every wire other than 0 and `t d` (the Agda's `kR`). -/
theorem kR (m : Wire) (x : Sch 16) (h₀ : (!weq m 0) = true) (h : (!weq m (t x.d)) = true) :
    every (keeps m) (R x) = true :=
  keeps_from m 0 (t x.d) (R x) (R_tgt x.c x.d x.p x.q) h₀ h

theorem every_RLs (m : Wire) : ∀ l : List (Sch 16), (∀ x ∈ l, every (keeps m) (R x) = true) →
    every (keeps m) (RL.RLs l) = true
  | [], _ => rfl
  | x :: l, h => every_append _ (R x) (RL.RLs l) (h x List.mem_cons_self)
    (every_RLs m l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A relation whose symbols flip only the wires 0, `a` and `b` is decided
by `Faithful (pick a b)`. -/
theorem rel_by (f₃ : Faithful 3) {u v : Word (Sch 16)} (r : RSRel 16 u v) (a b : Wire)
    (hu : ∀ x ∈ FreeMonoid.toList u, t x.d = a ∨ t x.d = b)
    (hv : ∀ x ∈ FreeMonoid.toList v, t x.d = a ∨ t x.d = b) :
    4 ⊢ ιs (RL.Rs u) ≈ ιs (RL.Rs v) := by
  obtain ⟨k₀, ka, kb⟩ := pick_ok a b
  have kx : ∀ x : Sch 16, (t x.d = a ∨ t x.d = b) → every (keeps (pick a b)) (R x) = true := by
    intro x hx
    rcases hx with h | h
    · exact kR _ x k₀ (by rw [h]; exact ka)
    · exact kR _ x k₀ (by rw [h]; exact kb)
  exact faithful f₃ (pick a b) _ _ (every_RLs _ _ fun x hx => kx x (hu x hx))
    (every_RLs _ _ fun x hx => kx x (hv x hx)) (RL.rel_sem r)

theorem R_rel (f₃ : Faithful 3) :
    ∀ {u v : Word (Sch 16)}, RSRel 16 u v → 4 ⊢ ιs (RL.Rs u) ≈ ιs (RL.Rs v)
  | _, _, .order c d p q => rel_by f₃ (.order c d p q) (t d) (t d) (by simp) (by simp)
  | _, _, .braid₀ c q => rel_by f₃ (.braid₀ c q) (t 1) (t 1) (by simp) (by simp)
  | _, _, .braid c d p q => rel_by f₃ (.braid c d p q) (t d) (t (d + 1)) (by simp) (by simp)
  | _, _, .far₀ c e p q => rel_by f₃ (.far₀ c e p q) (t e) (t e) (by simp) (by simp)
  | _, _, .far c d e p q r => rel_by f₃ (.far c d e p q r) (t d) (t e) (by simp) (by simp)
'''

TWL = r'''/-- A word of letters, letter by letter. -/
def twL₀ : List PG → Word (Sch 16)
  | [] => 1
  | g :: u => tw₀ g * twL₀ u

inductive Oks₀ : List PG → Prop
  | nil : Oks₀ []
  | cons {g : PG} {u : List PG} : 4 ⊢ ι g ≈ ιs (RL.Rs (tw₀ g)) → Oks₀ u → Oks₀ (g :: u)

theorem okL₀ : ∀ u : List PG, Oks₀ u → 4 ⊢ ιs u ≈ ιs (RL.Rs (twL₀ u))
  | [], .nil => Derivable.refl _
  | g :: u, .cons e es => by
    show 4 ⊢ ι g * ιs u ≈ ιs (RL.Rs (tw₀ g * twL₀ u))
    rw [RL.Rs_mul, ιs_append]
    exact e.mul (okL₀ u es)

/-- A letter whose translation keeps wire `m`: `Faithful m` decides it. -/
theorem basic (f₃ : Faithful 3) (g : PG) (m : Wire) (hg : every (keeps m) [g] = true)
    (ht : every (keeps m) (RL.Rs (tw₀ g)) = true)
    (hs : eqF 4 (semPs [g]) (semPs (RL.Rs (tw₀ g))) = true) : 4 ⊢ ι g ≈ ιs (RL.Rs (tw₀ g)) := by
  have := faithful f₃ m [g] (RL.Rs (tw₀ g)) hg ht (eqF_sound 4 _ _ hs)
  rwa [show ιs [g] = ι g from mul_one (ι g)] at this

/-- A letter that a three-wire step (idle wire `m`) turns into letters
translated before. -/
theorem viaN (g : PG) (m : Wire) (us : List PG) (w : Word (Sch 16))
    (hg : every (avoids m) [g] = true) (hu : every (avoids m) us = true)
    (hs : eqF 4 (semPs [g]) (semPs us) = true) (e : 4 ⊢ ιs us ≈ ιs (RL.Rs w)) :
    4 ⊢ ι g ≈ ιs (RL.Rs w) := by
  have := (Narrow3.narrowP m [g] us hg hu (eqF_sound 4 _ _ hs)).trans e
  rwa [show ιs [g] = ι g from mul_one (ι g)] at this
'''

TWL1 = r'''def twL₁ : List PG → Word (Sch 16)
  | [] => 1
  | g :: u => tw₁ g * twL₁ u

inductive Oks₁ : List PG → Prop
  | nil : Oks₁ []
  | cons {g : PG} {u : List PG} : 4 ⊢ ι g ≈ ιs (RL.Rs (tw₁ g)) → Oks₁ u → Oks₁ (g :: u)

theorem okL₁ : ∀ u : List PG, Oks₁ u → 4 ⊢ ιs u ≈ ιs (RL.Rs (twL₁ u))
  | [], .nil => Derivable.refl _
  | g :: u, .cons e es => by
    show 4 ⊢ ι g * ιs u ≈ ιs (RL.Rs (tw₁ g * twL₁ u))
    rw [RL.Rs_mul, ιs_append]
    exact e.mul (okL₁ u es)
'''

END = r'''end Letters

/-! ## Completeness -/

/-- Two words of placed letters with the same function are equal. -/
theorem complete (f₃ : Faithful 3) (u v : List PG) (e : semPs u ≐ semPs v) : 4 ⊢ ιs u ≈ ιs v :=
  RL.complete (R_rel f₃) tw (tw_ok f₃) u v e

/-- Two circuits on four wires with the same function are equal. -/
theorem complete₄ (f₃ : Faithful 3) {u v : Circ 4} (e : sem u ≐ sem v) : 4 ⊢ u ≈ v := by
  have at_ : ∀ w : Circ 4, semPs (pg w) ≐ sem w := fun w =>
    feq_trans (feq_sym (ιs_sem (pg w))) (feq_sym (sound (pg_ok w)))
  have e' : semPs (pg u) ≐ semPs (pg v) := feq_trans (at_ u) (feq_trans e (feq_sym (at_ v)))
  exact (pg_ok u).trans ((complete f₃ (pg u) (pg v) e').trans (pg_ok v).symm)

end QCert.XCXCCX4bit.Four'''

if __name__ == '__main__':
    gen()
