/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lafont's Lemmas 7 and 8: every circuit reduces to its canonical form

Translation of `Examples/Groups/Alternating/Normalization.agda`: every
circuit reduces to its canonical form by the rules of Fig. 10.

The canonical forms of Lemma 6 are the coset normal forms of the tower
`𝔄₀ ⊆ 𝔄₁ ⊆ …`: one on `n + 1` wires is one on `n` wires, shifted up,
followed by a stairs (`NF`, `inv_nf`).  The coset action `ract` pushes a
generator through a stairs: `sec c * of g` is a circuit one wire up followed
by a stairs (`ract_sound`).  Its clauses are the rules of Fig. 10, one for
each shape of stairs that a cycle on the bottom wires can meet, and Lemma 7,
which carries a circuit two wires up through the first cycle of a stairs:
`ω * shift (shift w)` is `shift (conjs w) * ω` (`conj_pass`, from `rule₁`).
`nf` runs the action from the trivial coset and recurses on the residual,
one wire up, and `inv_nf_nf` is Lemma 8: a circuit is congruent to its
canonical form, in any theory where the seven rules hold.

That is all the syntax the presentation needs.  That `nf` respects the
congruence is not proved here, by checking the action against every
relation: it follows, as in the paper, from soundness and Lemma 6
(`UniqueNormalForm`), in `Completeness`.

**Deviations from the Agda.**

* The Agda's `conj*` (`conj ʷ`) is `conjs`, the monoid homomorphism
  `FreeMonoid.lift conj`; `racts` (`ract ᵗ`, the stateful traversal of
  `Word.Base`) is a recursion on the list of letters (`ractL`), and the
  three clauses of `_ᵗ` are the equations `racts_of`, `racts_one`,
  `racts_mul`.  `inv-nf∘nf≈id` is `inv_nf_nf`.
* Associativity and the units are those of the free monoid: where the Agda
  chains `assoc` steps, the proofs reason in the quotient monoid of the
  congruence (`CircuitProp.cl`).  The clauses of `ract_sound` that the Agda
  proves by the unit laws or `by-assoc` alone are equalities of words
  (`derives_of_eq rfl`), and those it proves by `by-assoc-and rule` are the
  rule itself, its two sides being the clause's words.
* The inductions on a word (`conj_pass`, `racts_sound`, `width₀`) are on its
  letters (`FreeMonoid.inductionOn'`), the Agda's on the tree; the letter
  case of `conj_pass` is `conj_pass_gen`.  On no wires a circuit is the
  empty word itself (`width₀_eq`).
* The Agda's module parameter `rules : Fig10 T` is an argument of each
  lemma.
-/
import QCert.Alt16RevCir.Lib.Alternating.Cosets
import QCert.Alt16RevCir.Lib.Alternating.Rules

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit CircuitProp

variable {n : ℕ}

/-! ## Conjugation by `ω`, one wire down -/

/-- `conj g` is the image of `g` under conjugation by `ω`, read one wire
down: `ω * of g.up.up ≈ shift (conj g) * ω`.  For a cycle on the bottom
wires this is `rule₁`; anything higher commutes with `ω`. -/
def conj : {n : ℕ} → Gn (n + 1) → Circ (n + 2)
  | _, .gate0 g => nomatch g
  | _, .gate1 g => nomatch g
  | _, .gate2 g => nomatch g
  | _, .gate3 .ω_gate => shift ω * shift ω * ω * shift ω
  | _, .up g => FreeMonoid.of g.up.up

/-- The Agda's `conj*`. -/
def conjs : Circ (n + 1) →* Circ (n + 2) := FreeMonoid.lift conj

@[simp] theorem conjs_of (g : Gn (n + 1)) : conjs (FreeMonoid.of g) = conj g :=
  FreeMonoid.lift_eval_of _ _

/-! ## The coset action -/

/-- `ract c g` is a residual `b` and a coset `c'` with
`sec c * of g ≈ shift b * sec c'`.  A shifted generator passes a stairs one
cycle at a time and comes out conjugated (Lemma 7); a cycle on the bottom
wires meets the first cycles of the stairs, and the rule of Fig. 10 that
applies depends on how many there are before the stairs ends. -/
def ract : {n : ℕ} → C n → Gn (n + 1) → Circ n × C n
  | _, _, .gate0 g => nomatch g
  | _, _, .gate1 g => nomatch g
  | _, _, .gate2 g => nomatch g
  | _, .ε, .gate3 .ω_gate => (1, .ωc .ε)
  | _, .ε, .up g => (FreeMonoid.of g, .ε)
  | _, .ωω, .gate3 .ω_gate => (1, .ε)                                          -- rule₇
  | _, .ωω, .up g => (no_gen₂ g).elim
  | _, .ωc c, .up g => (conjs (ract c g).1, .ωc (ract c g).2)
  | 2, .ωc .ε, .gate3 .ω_gate => (1, .ωω)
  | _ + 3, .ωc .ε, .gate3 .ω_gate => (ω, .ωc (.ωc .ε))                         -- rule₄
  | _, .ωc .ωω, .gate3 .ω_gate => (ω * ω, .ωc .ωω)                             -- rule₆
  | _, .ωc (.ωc .ε), .gate3 .ω_gate => (ω * ω, .ε)                             -- rule₃
  | _, .ωc (.ωc .ωω), .gate3 .ω_gate => (ω, .ωc (.ωc .ωω))                     -- rule₅
  | _, .ωc (.ωc (.ωc c)), .gate3 .ω_gate => (shift ω, .ωc (.ωc (.ωc c)))       -- rule₂

/-- The action on a list of letters, threading the coset left to right and
multiplying the residuals. -/
def ractL : C n → List (Gn (n + 1)) → Circ n × C n
  | c, [] => (1, c)
  | c, g :: l => ((ract c g).1 * (ractL (ract c g).2 l).1, (ractL (ract c g).2 l).2)

/-- The action on circuits. -/
def racts (c : C n) (w : Circ (n + 1)) : Circ n × C n := ractL c (FreeMonoid.toList w)

theorem racts_one (c : C n) : racts c 1 = (1, c) := rfl

theorem racts_of (c : C n) (g : Gn (n + 1)) : racts c (FreeMonoid.of g) = ract c g := by
  show ((ract c g).1 * 1, (ract c g).2) = ract c g
  rw [mul_one]

theorem ractL_append (c : C n) (l l' : List (Gn (n + 1))) :
    ractL c (l ++ l') =
      ((ractL c l).1 * (ractL (ractL c l).2 l').1, (ractL (ractL c l).2 l').2) := by
  induction l generalizing c with
  | nil => simp [ractL]
  | cons g l ih => simp only [List.cons_append, ractL, ih, mul_assoc]

theorem racts_mul (c : C n) (w v : Circ (n + 1)) :
    racts c (w * v) = ((racts c w).1 * (racts (racts c w).2 v).1, (racts (racts c w).2 v).2) :=
  ractL_append c _ _

/-! ## Canonical forms -/

/-- The canonical forms on `n` wires: a stairs for each wire. -/
def NF : ℕ → Type
  | 0 => Unit
  | n + 1 => NF n × C n

/-- A canonical form on the top `n` wires, then a stairs. -/
def inv_nf : {n : ℕ} → NF n → Circ n
  | 0, _ => 1
  | _ + 1, (x, c) => shift (inv_nf x) * sec c

theorem inv_nf_zero (x : NF 0) : inv_nf x = 1 := rfl

theorem inv_nf_succ (x : NF n) (c : C n) :
    inv_nf (n := n + 1) (x, c) = shift (inv_nf x) * sec c := rfl

/-- Push the circuit through the trivial coset, then normalise the residual
on the top wires. -/
def nf : {n : ℕ} → Circ n → NF n
  | 0, _ => ()
  | _ + 1, w => (nf (racts .ε w).1, (racts .ε w).2)

theorem nf_succ (w : Circ (n + 1)) :
    nf w = ((nf (racts .ε w).1, (racts .ε w).2) : NF (n + 1)) := rfl

/-! ## Lemmas 7 and 8, in a theory with the rules of Fig. 10 -/

/-- Equal words are congruent. -/
theorem derives_of_eq {T : Theory} {w v : Circ n} (h : w = v) : Derives T n w v :=
  h ▸ Derivable.refl w

/-- On no wires every circuit is empty. -/
theorem width₀_eq (w : Circ 0) : w = 1 := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w _ => exact (no_gen₀ g).elim

/-- The Agda's `width₀`. -/
theorem width₀ {T : Theory} (w : Circ 0) : Derives T 0 w 1 := derives_of_eq (width₀_eq w)

/-- The clause of `rule₂`, in the quotient monoid: the stairs `x` above the
first three cycles commutes with the cycle `a` that arrives (`hx`), and
`rule₂` (`hr`) carries it through them. -/
private theorem rule₂_step {M : Type*} [Monoid M] {a b c x : M} (hx : x * a = a * x)
    (hr : a * b * c * a = c * a * b * c) :
    a * (b * (c * x)) * a = c * (a * (b * (c * x))) := by
  calc a * (b * (c * x)) * a = a * b * c * (x * a) := by simp only [mul_assoc]
    _ = a * b * c * a * x := by rw [hx]; simp only [mul_assoc]
    _ = c * (a * (b * (c * x))) := by rw [hr]; simp only [mul_assoc]

section Rules

variable {T : Theory} (rules : Fig10 T)

include rules

/-- Lemma 7 at a letter. -/
theorem conj_pass_gen : ∀ {n : ℕ} (g : Gn (n + 1)),
    Derives T (n + 3) (ω * FreeMonoid.of g.up.up) (shift (conj g) * ω)
  | _, .gate0 g => nomatch g
  | _, .gate1 g => nomatch g
  | _, .gate2 g => nomatch g
  | _, .gate3 .ω_gate => rules.rule₁
  | _, .up g => (Derivable.of (Lift.comm3 .ω_gate g)).symm

/-- Lemma 7, one cycle at a time: `ω` passes a circuit two wires up, which
comes out conjugated. -/
theorem conj_pass (w : Circ (n + 1)) :
    Derives T (n + 3) (ω * shift (shift w)) (shift (conjs w) * ω) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    have a := cl_eq.2 (conj_pass_gen rules g)
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, map_mul, map_mul, map_mul, shift_of, shift_of, conjs_of, cl_mul, cl_mul, cl_mul,
      cl_mul, ← mul_assoc, a, mul_assoc, ih, mul_assoc]

/-- The coset action is sound: each clause is one rule of Fig. 10, Lemma 7
or the unit laws. -/
theorem ract_sound : ∀ {n : ℕ} (c : C n) (g : Gn (n + 1)),
    Derives T (n + 1) (sec c * FreeMonoid.of g) (shift (ract c g).1 * sec (ract c g).2)
  | _, _, .gate0 g => nomatch g
  | _, _, .gate1 g => nomatch g
  | _, _, .gate2 g => nomatch g
  | _, .ε, .gate3 .ω_gate => derives_of_eq rfl
  | _, .ε, .up _ => derives_of_eq rfl
  | _, .ωω, .gate3 .ω_gate => rules.rule₇
  | _, .ωω, .up g => (no_gen₂ g).elim
  | _, .ωc c, .up g => by
    apply cl_eq.1
    have ih := cl_eq.2 (lemma_cong_up (ract_sound c g))
    have p := cl_eq.2 (conj_pass rules (ract c g).1)
    rw [map_mul, map_mul, shift_of, cl_mul, cl_mul] at ih
    rw [cl_mul, cl_mul] at p
    show cl T _ (ω * shift (sec c) * FreeMonoid.of g.up) =
      cl T _ (shift (conjs (ract c g).1) * (ω * shift (sec (ract c g).2)))
    rw [cl_mul, cl_mul, cl_mul, cl_mul, mul_assoc, ih, ← mul_assoc, p, mul_assoc]
  | 2, .ωc .ε, .gate3 .ω_gate => derives_of_eq rfl
  | _ + 3, .ωc .ε, .gate3 .ω_gate => rules.rule₄
  | _, .ωc .ωω, .gate3 .ω_gate => rules.rule₆
  | _, .ωc (.ωc .ε), .gate3 .ω_gate => rules.rule₃
  | _, .ωc (.ωc .ωω), .gate3 .ω_gate => rules.rule₅
  | _, .ωc (.ωc (.ωc (n := k) c)), .gate3 .ω_gate => by
    apply cl_eq.1
    have x := cl_eq.2 (comm_gate₃_w (R := T) Gate.ω_gate (sec c))
    have r := cl_eq.2 (rules.rule₂ (n := k))
    rw [cl_mul, cl_mul] at x
    rw [cl_mul, cl_mul, cl_mul, cl_mul, cl_mul, cl_mul] at r
    show cl T _ (ω * shift (ω * shift (ω * shift (sec c))) * ω) =
      cl T _ (shift (shift ω) * (ω * shift (ω * shift (ω * shift (sec c)))))
    simp only [map_mul, cl_mul]
    exact rule₂_step x r

/-- The action on circuits is sound. -/
theorem racts_sound (c : C n) (w : Circ (n + 1)) :
    Derives T (n + 1) (sec c * w) (shift (racts c w).1 * sec (racts c w).2) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => rw [racts_one, mul_one, map_one, one_mul]
  | mul_of g w ih =>
    have a := cl_eq.2 (ract_sound rules c g)
    have b := ih (ract c g).2
    rw [cl_mul, cl_mul] at a b
    rw [racts_mul, racts_of, map_mul, cl_mul, cl_mul, cl_mul, cl_mul, ← mul_assoc, a, mul_assoc,
      b, mul_assoc]

/-- Lemma 8: every circuit is congruent to its canonical form (the Agda's
`inv-nf∘nf≈id`). -/
theorem inv_nf_nf : ∀ {n : ℕ} (w : Circ n), Derives T n (inv_nf (nf w)) w
  | 0, w => (width₀ w).symm
  | n + 1, w => by
    have h₁ := lemma_cong_up (inv_nf_nf (racts .ε w).1)
    have h₂ := racts_sound rules .ε w
    rw [sec_ε, one_mul] at h₂
    exact (h₁.mul (Derivable.refl (sec (racts .ε w).2))).trans h₂.symm

end Rules

end QCert.Alt16RevCir.Alternating
