/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# PROPs: the swap as structure

Translation of the parts of `Circuit/Prop.agda` that `Alt16-RevCir`
uses, with the lemmas of `Circuit/Base.agda`'s `Lift-Relation`
they rest on (`lemma-cong↑`, `comm-gate₁-w↑`, `comm-gate₂-w↑↑`,
`comm-gate₃-w↑↑↑`, `Central-Scalars` with `Single-Scalar`).

`QCert.Circuit` presents a PRO: `Lift R` closes a family of rules `R` under
the structural rules (shifting, the interchange of gates on disjoint wires,
scalars on every wire).  A PROP adds a symmetry: one two-wire gate of the
family is designated the swap `σ` (`HasSwap`, the Agda's module parameter
`Ex-gate`), and `Sym` states the rules that make it a symmetry: `σ` is an
involution (`σ_inv`) and natural in every generator (`σ_nat₁`, `σ_nat₂`,
`σ_nat₃`; at the swap itself `σ_nat₂` is the Yang–Baxter equation).  A
gate-specific relation `SRel` is lifted by `PropRel` (the Agda's
`Lift-To-Prop`): its rules (`srel`) beside the swap rules (`σrel`), under
the structural rules, and `Der SRel n w v` is the congruence it generates
at width `n` (the Agda's `n ⊢ w ≈ v`).

Naturality at a generator gives naturality at a circuit (`nat₀` … `nat₄`),
and so an equation between `k`-wire circuits, `k ≤ 4`, holds on the bottom
`k` wires of every wider circuit (`pad₀` … `pad₄`, `pad`).

Conventions.  Words are the framework's `FreeMonoid`, read in diagram order
here (`w * v` is `w` followed by `v`), as the Agda's.  The Agda's widening
`w ↓ᵏ n : Circuit (k + n)` is the framework's `Circuit.pad n w : Circuit (n + k)`
(and `x ↧ᵏ n` is `Gen.pad n x`), `w ↑` is `Circuit.shift w` and `g ↥` is
`Gen.up g`.  The Agda's widths `₁₊ k + n` are written `n + k + 1`, and
`₂₊ n` is `n + 2`.  `σ[ k ]` and `σ⁻[ k ]` are `σc k` and `σcInv k`; the
Agda's `σ-inv`, `σ-nat₁`, … are `σ_inv`, `σ_nat₁`, …, and `lemma-cong↑` is
`lemma_cong_up`.

**Deviation from the Agda.**  Associativity and the units are those of the
free monoid, so the proofs reason in the quotient monoid of the congruence
(`cl`), where derivability is equality, instead of chaining `assoc` steps.
-/
import QCert.Circuit.Basic

namespace QCert.Alt16RevCir.CircuitProp

open QCert QCert.Circuit

/-! ## The quotient monoid of a theory -/

section Quot

variable {Gate : ℕ → Type}

/-- The class of a circuit modulo the theory `Lift R` at width `n`. -/
def cl (R : CRel Gate) (n : ℕ) (w : Circuit Gate n) : (conGen (Lift R n)).Quotient :=
  (conGen (Lift R n)).mk' w

variable {R : CRel Gate} {n : ℕ}

theorem cl_eq {w v : Circuit Gate n} : cl R n w = cl R n v ↔ Derives R n w v :=
  (conGen (Lift R n)).eq

theorem cl_mul (w v : Circuit Gate n) : cl R n (w * v) = cl R n w * cl R n v :=
  map_mul (conGen (Lift R n)).mk' w v

theorem cl_one : cl R n (1 : Circuit Gate n) = 1 := map_one (conGen (Lift R n)).mk'

end Quot

/-! ## From `Circuit.Base`: the structural rules at circuits -/

section Base

variable {Gate : ℕ → Type} {R : CRel Gate}

/-- The congruence at width `n` lifts to width `n + 1` (the Agda's
`lemma-cong↑`). -/
theorem lemma_cong_up {n : ℕ} {w v : Circuit Gate n} (d : Derives R n w v) :
    Derives R (n + 1) (shift w) (shift v) := by
  let c : Con (Circuit Gate n) := (conGen (Lift R (n + 1))).comap shift (map_mul shift)
  have : conGen (Lift R n) ≤ c := Con.conGen_le fun x y r => Derivable.of (Lift.shift r)
  exact this d

/-- A one-wire gate at the bottom commutes with a circuit shifted up past it
(the Agda's `comm-gate₁-w↑`). -/
theorem comm_gate₁_w {n : ℕ} (g : Gate 1) (w : Circuit Gate n) :
    Derives R (n + 1) (shift w * g1 g) (g1 g * shift w) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have a : cl R (n + 1) (FreeMonoid.of x.up * g1 g) = cl R (n + 1) (g1 g * FreeMonoid.of x.up) :=
      cl_eq.2 (Derivable.of (Lift.comm1 g x))
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, shift_of, cl_mul, cl_mul, cl_mul, cl_mul, mul_assoc, ih, ← mul_assoc, a,
      mul_assoc]

/-- The Agda's `comm-gate₂-w↑↑`. -/
theorem comm_gate₂_w {n : ℕ} (g : Gate 2) (w : Circuit Gate n) :
    Derives R (n + 2) (shift (shift w) * g2 g) (g2 g * shift (shift w)) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have a : cl R (n + 2) (FreeMonoid.of x.up.up * g2 g) =
        cl R (n + 2) (g2 g * FreeMonoid.of x.up.up) :=
      cl_eq.2 (Derivable.of (Lift.comm2 g x))
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, map_mul, shift_of, shift_of, cl_mul, cl_mul, cl_mul, cl_mul, mul_assoc, ih,
      ← mul_assoc, a, mul_assoc]

/-- The Agda's `comm-gate₃-w↑↑↑`. -/
theorem comm_gate₃_w {n : ℕ} (g : Gate 3) (w : Circuit Gate n) :
    Derives R (n + 3) (shift (shift (shift w)) * g3 g) (g3 g * shift (shift (shift w))) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have a : cl R (n + 3) (FreeMonoid.of x.up.up.up * g3 g) =
        cl R (n + 3) (g3 g * FreeMonoid.of x.up.up.up) :=
      cl_eq.2 (Derivable.of (Lift.comm3 g x))
    rw [cl_mul, cl_mul] at a ih
    rw [map_mul, map_mul, map_mul, shift_of, shift_of, shift_of, cl_mul, cl_mul, cl_mul, cl_mul,
      mul_assoc, ih, ← mul_assoc, a, mul_assoc]

/-- A scalar shifted up is the scalar, at any width. -/
private theorem scalar_up {n : ℕ} (h : Gate 0) :
    Derives R (n + 1) (FreeMonoid.of (Gen.gate0 h).up) (g0 h) :=
  Derivable.of (Lift.scalar h)

/-- `Central-Scalars` with `Single-Scalar`: when the scalars are all equal,
a scalar commutes with every generator (the Agda's `comm₀`). -/
theorem comm₀ (one : ∀ h h' : Gate 0, h = h') (h : Gate 0) :
    ∀ {n : ℕ} (g : Gen Gate n),
      Derives R n (FreeMonoid.of g * g0 h) (g0 h * FreeMonoid.of g)
  | _, .gate0 h' => by rw [one h h']
  | _, @Gen.gate1 _ m h₁ =>
    have e := scalar_up (R := R) (n := m) h
    (((Derivable.refl _).mul e.symm).trans (Derivable.of (Lift.comm1 h₁ (Gen.gate0 h))).symm).trans
      (e.mul (Derivable.refl _))
  | _, @Gen.gate2 _ m h₂ =>
    have e : Derives R (m + 2) (FreeMonoid.of (Gen.gate0 h).up.up) (g0 h) :=
      (lemma_cong_up (scalar_up (R := R) (n := m) h)).trans (scalar_up h)
    (((Derivable.refl _).mul e.symm).trans (Derivable.of (Lift.comm2 h₂ (Gen.gate0 h))).symm).trans
      (e.mul (Derivable.refl _))
  | _, @Gen.gate3 _ m h₃ =>
    have e : Derives R (m + 3) (FreeMonoid.of (Gen.gate0 h).up.up.up) (g0 h) :=
      ((lemma_cong_up (lemma_cong_up (scalar_up (R := R) (n := m) h))).trans
        (lemma_cong_up (scalar_up h))).trans (scalar_up h)
    (((Derivable.refl _).mul e.symm).trans (Derivable.of (Lift.comm3 h₃ (Gen.gate0 h))).symm).trans
      (e.mul (Derivable.refl _))
  | _, @Gen.up _ m g =>
    have e := scalar_up (R := R) (n := m) h
    (((Derivable.refl _).mul e.symm).trans (lemma_cong_up (comm₀ one h g))).trans
      (e.mul (Derivable.refl _))

end Base

/-! ## The swap, and the cycles built from it -/

/-- `Circuit.Prop`'s second parameter: the two-wire gate designated the
swap. -/
class HasSwap (Gate : ℕ → Type) where
  ex : Gate 2

variable {Gate : ℕ → Type} [HasSwap Gate]

/-- The swap of wires `0` and `1`. -/
abbrev σ {n : ℕ} : Circuit Gate (n + 2) := g2 HasSwap.ex

/-- `σ[ k ]` carries wire `k` down to wire `0`, and wires `0 … k − 1` up one,
by swapping it down a wire at a time: Mac Lane's `τ(k,1)`. -/
def σc : (k : ℕ) → {n : ℕ} → Circuit Gate (n + k + 1)
  | 0, _ => 1
  | 1, _ => σ
  | k + 2, _ => shift (σc (k + 1)) * σ

/-- `σ⁻[ k ]`, the same swaps in the other order, carries wire `0` up to
wire `k`: `τ(1,k)`, the inverse of `σ[ k ]`. -/
def σcInv : (k : ℕ) → {n : ℕ} → Circuit Gate (n + k + 1)
  | 0, _ => 1
  | 1, _ => σ
  | k + 2, _ => σ * shift (σcInv (k + 1))

/-! ## The swap rules -/

/-- The swap rules (Clément's (f) at a generator and (g)): the swap is an
involution, and a `k`-wire gate followed by `σ[ k ]` is `σ[ k ]` followed by
the gate one wire up. -/
inductive Sym : CRel Gate
  | σ_inv {n : ℕ} : Sym (n + 2) (σ * σ) 1
  | σ_nat₁ {n : ℕ} (h : Gate 1) : Sym (n + 2) (g1 h * σc 1) (σc 1 * shift (g1 h))
  | σ_nat₂ {n : ℕ} (h : Gate 2) : Sym (n + 3) (g2 h * σc 2) (σc 2 * shift (g2 h))
  | σ_nat₃ {n : ℕ} (h : Gate 3) : Sym (n + 4) (g3 h * σc 3) (σc 3 * shift (g3 h))

/-! ## A family's relation, with the swap rules and the structural rules -/

/-- `Lift-To-Prop`'s `_Prop,_===_`: the swap rules (`σrel`) beside the
family's (`srel`).  The structural rules are `QCert.Lift`'s on top. -/
inductive PropRel (SRel : CRel Gate) : CRel Gate
  | σrel {n : ℕ} {w v : Circuit Gate n} : Sym n w v → PropRel SRel n w v
  | srel {n : ℕ} {w v : Circuit Gate n} : SRel n w v → PropRel SRel n w v

/-- The Agda's `_VRel,_===_`: the family's rules and the swap rules under the
structural rules. -/
abbrev VRel (SRel : CRel Gate) : CRel Gate := Lift (PropRel SRel)

/-- The congruence generated, at each width (the Agda's `n ⊢ w ≈ v`). -/
abbrev Der (SRel : CRel Gate) (n : ℕ) (w v : Circuit Gate n) : Prop :=
  Derives (PropRel SRel) n w v

variable {SRel : CRel Gate}

/-- A swap rule, as an equation. -/
theorem sym_rule {n : ℕ} {w v : Circuit Gate n} (s : Sym n w v) : Der SRel n w v :=
  Derivable.of (Lift.rule (PropRel.σrel s))

/-- A rule of the family, as an equation (the Agda's `axiom (srel (srel r))`). -/
theorem srel_rule {n : ℕ} {w v : Circuit Gate n} (s : SRel n w v) : Der SRel n w v :=
  Derivable.of (Lift.rule (PropRel.srel s))

/-! ### The swap -/

theorem σ_invol {n : ℕ} : Der SRel (n + 2) (σ * σ) 1 := sym_rule Sym.σ_inv

theorem yang_baxter {n : ℕ} :
    Der SRel (n + 3) (σ * (shift σ * σ)) (shift σ * σ * shift σ) :=
  sym_rule (Sym.σ_nat₂ HasSwap.ex)

/-! ### Scalars -/

/-- A generator written `d` wires higher (the Agda's `_↥ᵏ_`). -/
def upN {m : ℕ} (g : Gen Gate m) : (d : ℕ) → Gen Gate (m + d)
  | 0 => g
  | d + 1 => (upN g d).up

/-- A scalar written at any depth is the scalar (`ω↑=ω`, shifted). -/
theorem ω_up {m : ℕ} (h : Gate 0) :
    ∀ d : ℕ, Der SRel (m + d) (FreeMonoid.of (upN (Gen.gate0 (n := m) h) d)) (g0 h)
  | 0 => Derivable.refl _
  | d + 1 => (lemma_cong_up (ω_up h d)).trans (Derivable.of (Lift.scalar h))

/-- A scalar passes a swap: shifted up out of its way, it is `comm₂`. -/
theorem ω_σ {n : ℕ} (h : Gate 0) : Der SRel (n + 2) (g0 h * σ) (σ * g0 h) :=
  have e := ω_up (SRel := SRel) (m := n) h 2
  ((e.symm.mul (Derivable.refl _)).trans (Derivable.of (Lift.comm2 HasSwap.ex (Gen.gate0 h)))).trans
    ((Derivable.refl _).mul e)

private theorem ω_σc_step (h : Gate 0) {M : ℕ} (c : Circuit Gate (M + 1))
    (ih : Der SRel (M + 1) (g0 h * c) (c * g0 h)) :
    Der SRel (M + 2) (g0 h * (shift c * σ)) (shift c * σ * g0 h) := by
  apply cl_eq.1
  have e : cl (PropRel SRel) (M + 2) (FreeMonoid.of (Gen.gate0 h).up) = cl _ (M + 2) (g0 h) :=
    cl_eq.2 (Derivable.of (Lift.scalar h))
  have s : cl (PropRel SRel) (M + 2) (shift (g0 h * c)) = cl _ (M + 2) (shift (c * g0 h)) :=
    cl_eq.2 (lemma_cong_up ih)
  have t : cl (PropRel SRel) (M + 2) (g0 h * σ) = cl _ (M + 2) (σ * g0 h) := cl_eq.2 (ω_σ h)
  rw [map_mul, map_mul, shift_of, cl_mul, cl_mul] at s
  rw [cl_mul, cl_mul] at t
  rw [cl_mul, cl_mul, cl_mul, cl_mul, ← e, ← mul_assoc, s, mul_assoc, e, t, ← mul_assoc]

/-- … and so every cycle. -/
theorem ω_σc (h : Gate 0) : ∀ (k : ℕ) {n : ℕ},
    Der SRel (n + k + 1) (g0 h * σc k) (σc k * g0 h)
  | 0, _ => by
    show Der SRel _ (g0 h * 1) (1 * g0 h)
    rw [mul_one, one_mul]
  | 1, _ => ω_σ h
  | k + 2, _ => ω_σc_step h (σc (k + 1)) (ω_σc h (k + 1))

/-! ### Naturality at a letter -/

/-- What slides past `σ[ k + 1 ]` slides one wire up past `σ[ k + 2 ]`. -/
private theorem σ_shift {m : ℕ} (c : Circuit Gate (m + 1)) (a : Gen Gate (m + 1)) (b : Gen Gate m)
    (p : Der SRel (m + 1) (FreeMonoid.of a * c) (c * shift (FreeMonoid.of b))) :
    Der SRel (m + 2) (FreeMonoid.of a.up * (shift c * σ))
      ((shift c * σ) * FreeMonoid.of b.up.up) := by
  apply cl_eq.1
  have s : cl (PropRel SRel) (m + 2) (shift (FreeMonoid.of a * c)) =
      cl _ (m + 2) (shift (c * shift (FreeMonoid.of b))) := cl_eq.2 (lemma_cong_up p)
  have t : cl (PropRel SRel) (m + 2) (FreeMonoid.of b.up.up * σ) =
      cl _ (m + 2) (σ * FreeMonoid.of b.up.up) :=
    cl_eq.2 (Derivable.of (Lift.comm2 HasSwap.ex b))
  rw [map_mul, map_mul, shift_of, shift_of, shift_of, cl_mul, cl_mul] at s
  rw [cl_mul, cl_mul] at t
  rw [cl_mul, cl_mul, cl_mul, cl_mul, ← mul_assoc, s, mul_assoc, t, mul_assoc]

/-- A one-wire gate passes any cycle: it commutes with the shifted part and
meets `σ-nat₁` at the last swap. -/
private theorem gate₁_σ {m : ℕ} (c : Circuit Gate (m + 1)) (h : Gate 1) :
    Der SRel (m + 2) (g1 h * (shift c * σ)) ((shift c * σ) * FreeMonoid.of (Gen.gate1 h).up) := by
  apply cl_eq.1
  have s : cl (PropRel SRel) (m + 2) (shift c * g1 h) = cl _ (m + 2) (g1 h * shift c) :=
    cl_eq.2 (comm_gate₁_w h c)
  have t : cl (PropRel SRel) (m + 2) (g1 h * σ) =
      cl _ (m + 2) (σ * FreeMonoid.of (Gen.gate1 h).up) :=
    cl_eq.2 (sym_rule (Sym.σ_nat₁ h))
  rw [cl_mul, cl_mul] at s t
  rw [cl_mul, cl_mul, cl_mul, cl_mul, ← mul_assoc, ← s, mul_assoc, t, mul_assoc]

/-- A scalar comes out one wire up because it is the same there. -/
private theorem gate₀_σ (k : ℕ) {n : ℕ} (h : Gate 0) :
    Der SRel (n + k + 1) (g0 h * σc k) (σc k * FreeMonoid.of (Gen.gate0 h).up) :=
  (ω_σc h k).trans ((Derivable.refl _).mul (Derivable.of (Lift.scalar h)).symm)

/-- A two-wire gate commutes with the top swap of `σ[ 3 ]` and meets `σ-nat₂`
at the other two. -/
private theorem gate₂_σ3 {m : ℕ} (h : Gate 2) :
    Der SRel (m + 4) (g2 h * (shift (shift σ * σ) * σ))
      ((shift (shift σ * σ) * σ) * FreeMonoid.of (Gen.gate2 h).up) :=
  have c : Der SRel (m + 4) (g2 h * shift (shift σ)) (shift (shift σ) * g2 h) :=
    (Derivable.of (Lift.comm2 h (Gen.gate2 HasSwap.ex))).symm
  have t : Der SRel (m + 4) (g2 h * (shift σ * σ))
      ((shift σ * σ) * FreeMonoid.of (Gen.gate2 h).up) :=
    sym_rule (Sym.σ_nat₂ h)
  (c.mul (Derivable.refl (shift σ * σ))).trans ((Derivable.refl (shift (shift σ))).mul t)

/-- A two-wire gate passes `σ[ 4 ]`: it commutes with `σ[ 2 ]` two wires up
and meets `σ-nat₂` at the rest. -/
private theorem gate₂_σ4 {m : ℕ} (h : Gate 2) :
    Der SRel (m + 5) (g2 h * (shift (shift (σc 2)) * σc 2))
      ((shift (shift (σc 2)) * σc 2) * FreeMonoid.of (Gen.gate2 h).up) := by
  have c : Der SRel (m + 5) (g2 h * shift (shift (σc 2))) (shift (shift (σc 2)) * g2 h) :=
    (comm_gate₂_w (R := PropRel SRel) (n := m + 3) h (σc 2)).symm
  have t : Der SRel (m + 5) (g2 h * σc 2) (σc 2 * FreeMonoid.of (Gen.gate2 h).up) :=
    sym_rule (Sym.σ_nat₂ h)
  rw [← mul_assoc, mul_assoc (shift (shift (σc 2)))]
  refine (c.mul (Derivable.refl _)).trans ?_
  rw [mul_assoc]
  exact (Derivable.refl _).mul t

/-- A three-wire gate commutes with the top swap of `σ[ 4 ]` and meets
`σ-nat₃` at the rest. -/
private theorem gate₃_σ4 {m : ℕ} (h : Gate 3) :
    Der SRel (m + 5) (g3 h * (shift (shift (shift σ)) * σc 3))
      ((shift (shift (shift σ)) * σc 3) * FreeMonoid.of (Gen.gate3 h).up) :=
  have c : Der SRel (m + 5) (g3 h * shift (shift (shift σ))) (shift (shift (shift σ)) * g3 h) :=
    (Derivable.of (Lift.comm3 h (Gen.gate2 HasSwap.ex))).symm
  have t : Der SRel (m + 5) (g3 h * σc 3) (σc 3 * FreeMonoid.of (Gen.gate3 h).up) :=
    sym_rule (Sym.σ_nat₃ h)
  (c.mul (Derivable.refl (σc 3))).trans ((Derivable.refl (shift (shift (shift σ)))).mul t)

theorem natg₀ {n : ℕ} : ∀ x : Gen Gate 0,
    Der SRel (n + 1) (FreeMonoid.of (x.pad (n + 1)) * σc 0)
      (σc 0 * shift (FreeMonoid.of (x.pad n)))
  | .gate0 h => gate₀_σ 0 h

theorem natg₁ {n : ℕ} : ∀ x : Gen Gate 1,
    Der SRel (n + 2) (FreeMonoid.of (x.pad (n + 1)) * σc 1)
      (σc 1 * shift (FreeMonoid.of (x.pad n)))
  | .gate0 h => gate₀_σ 1 h
  | .gate1 h => sym_rule (Sym.σ_nat₁ h)
  | .up (.gate0 h) =>
    have e := ω_up (SRel := SRel) (m := n + 1) h 1
    have e' := ω_up (SRel := SRel) (m := n) h 2
    ((e.mul (Derivable.refl _)).trans (ω_σ h)).trans ((Derivable.refl _).mul e'.symm)

theorem natg₂ {n : ℕ} : ∀ x : Gen Gate 2,
    Der SRel (n + 3) (FreeMonoid.of (x.pad (n + 1)) * σc 2)
      (σc 2 * shift (FreeMonoid.of (x.pad n)))
  | .gate0 h => gate₀_σ 2 h
  | .gate1 h => gate₁_σ (σc 1) h
  | .gate2 h => sym_rule (Sym.σ_nat₂ h)
  | .up x => σ_shift (σc 1) _ _ (natg₁ x)

theorem natg₃ {n : ℕ} : ∀ x : Gen Gate 3,
    Der SRel (n + 4) (FreeMonoid.of (x.pad (n + 1)) * σc 3)
      (σc 3 * shift (FreeMonoid.of (x.pad n)))
  | .gate0 h => gate₀_σ 3 h
  | .gate1 h => gate₁_σ (σc 2) h
  | .gate2 h => gate₂_σ3 h
  | .gate3 h => sym_rule (Sym.σ_nat₃ h)
  | .up x => σ_shift (σc 2) _ _ (natg₂ x)

theorem natg₄ {n : ℕ} : ∀ x : Gen Gate 4,
    Der SRel (n + 5) (FreeMonoid.of (x.pad (n + 1)) * σc 4)
      (σc 4 * shift (FreeMonoid.of (x.pad n)))
  | .gate0 h => gate₀_σ 4 h
  | .gate1 h => gate₁_σ (σc 3) h
  | .gate2 h => by
    have e : (σc 4 : Circuit Gate (n + 4 + 1)) = shift (shift (σc 2)) * σc 2 := by
      simp only [σc, map_mul, mul_assoc]
    rw [e]; exact gate₂_σ4 h
  | .gate3 h => by
    have e : (σc 4 : Circuit Gate (n + 4 + 1)) = shift (shift (shift σ)) * σc 3 := by
      simp only [σc, map_mul, mul_assoc]
    rw [e]; exact gate₃_σ4 h
  | .up x => σ_shift (σc 3) _ _ (natg₃ x)

/-! ### Naturality at a circuit -/

/-- A word slides past `c` when each of its letters does. -/
private theorem slide {k m : ℕ} (c : Circuit Gate (m + 1)) (f : Gen Gate k → Gen Gate (m + 1))
    (g : Gen Gate k → Gen Gate m)
    (p : ∀ x, Der SRel (m + 1) (FreeMonoid.of (f x) * c) (c * shift (FreeMonoid.of (g x))))
    (w : Circuit Gate k) :
    Der SRel (m + 1) (FreeMonoid.map f w * c) (c * shift (FreeMonoid.map g w)) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    have px := cl_eq.2 (p x)
    rw [cl_mul, cl_mul] at px ih
    rw [map_mul, map_mul, map_mul, FreeMonoid.map_of, FreeMonoid.map_of, cl_mul, cl_mul, cl_mul,
      cl_mul, mul_assoc, ih, ← mul_assoc, px, mul_assoc]

theorem nat₀ {n : ℕ} (w : Circuit Gate 0) :
    Der SRel (n + 1) (Circuit.pad (n + 1) w * σc 0) (σc 0 * shift (Circuit.pad n w)) :=
  slide (k := 0) (m := n + 0) (σc 0) (Gen.pad (n + 1)) (Gen.pad n) natg₀ w

theorem nat₁ {n : ℕ} (w : Circuit Gate 1) :
    Der SRel (n + 2) (Circuit.pad (n + 1) w * σc 1) (σc 1 * shift (Circuit.pad n w)) :=
  slide (k := 1) (m := n + 1) (σc 1) (Gen.pad (n + 1)) (Gen.pad n) natg₁ w

theorem nat₂ {n : ℕ} (w : Circuit Gate 2) :
    Der SRel (n + 3) (Circuit.pad (n + 1) w * σc 2) (σc 2 * shift (Circuit.pad n w)) :=
  slide (k := 2) (m := n + 2) (σc 2) (Gen.pad (n + 1)) (Gen.pad n) natg₂ w

theorem nat₃ {n : ℕ} (w : Circuit Gate 3) :
    Der SRel (n + 4) (Circuit.pad (n + 1) w * σc 3) (σc 3 * shift (Circuit.pad n w)) :=
  slide (k := 3) (m := n + 3) (σc 3) (Gen.pad (n + 1)) (Gen.pad n) natg₃ w

theorem nat₄ {n : ℕ} (w : Circuit Gate 4) :
    Der SRel (n + 5) (Circuit.pad (n + 1) w * σc 4) (σc 4 * shift (Circuit.pad n w)) :=
  slide (k := 4) (m := n + 4) (σc 4) (Gen.pad (n + 1)) (Gen.pad n) natg₄ w

/-! ### The inverse cycles -/

private theorem σσInv_step {M : ℕ} (c c' : Circuit Gate (M + 1))
    (ih : Der SRel (M + 1) (c * c') 1) :
    Der SRel (M + 2) ((shift c * σ) * (σ * shift c')) 1 := by
  apply cl_eq.1
  have s : cl (PropRel SRel) (M + 2) (shift (c * c')) = cl _ (M + 2) (shift 1) :=
    cl_eq.2 (lemma_cong_up ih)
  have t : cl (PropRel SRel) (M + 2) (σ * σ) = cl _ (M + 2) 1 := cl_eq.2 σ_invol
  rw [map_mul, map_one, cl_mul, cl_one] at s
  rw [cl_mul, cl_one] at t
  rw [cl_mul, cl_mul, cl_mul, cl_one, mul_assoc, ← mul_assoc (cl _ _ σ), t, one_mul, s]

private theorem σInvσ_step {M : ℕ} (c c' : Circuit Gate (M + 1))
    (ih : Der SRel (M + 1) (c' * c) 1) :
    Der SRel (M + 2) ((σ * shift c') * (shift c * σ)) 1 := by
  apply cl_eq.1
  have s : cl (PropRel SRel) (M + 2) (shift (c' * c)) = cl _ (M + 2) (shift 1) :=
    cl_eq.2 (lemma_cong_up ih)
  have t : cl (PropRel SRel) (M + 2) (σ * σ) = cl _ (M + 2) 1 := cl_eq.2 σ_invol
  rw [map_mul, map_one, cl_mul, cl_one] at s
  rw [cl_mul, cl_one] at t
  rw [cl_mul, cl_mul, cl_mul, cl_one, mul_assoc, ← mul_assoc (cl _ _ (shift c')), s, one_mul, t]

theorem σσInv : ∀ (k : ℕ) {n : ℕ}, Der SRel (n + k + 1) (σc k * σcInv k) 1
  | 0, _ => by
    show Der SRel _ (1 * 1) 1
    rw [mul_one]
  | 1, _ => σ_invol
  | k + 2, _ => σσInv_step (σc (k + 1)) (σcInv (k + 1)) (σσInv (k + 1))

theorem σInvσ : ∀ (k : ℕ) {n : ℕ}, Der SRel (n + k + 1) (σcInv k * σc k) 1
  | 0, _ => by
    show Der SRel _ (1 * 1) 1
    rw [mul_one]
  | 1, _ => σ_invol
  | k + 2, _ => σInvσ_step (σc (k + 1)) (σcInv (k + 1)) (σInvσ (k + 1))

/-! ### An equation on the bottom wires of a wider circuit -/

/-- `a ≈ b` from `a` and `b` each passing `c` to `a′` and `b′`, `a′ ≈ b′`, and
a right inverse of `c`. -/
private theorem conj_back {n : ℕ} {a b a' b' c c' : Circuit Gate n}
    (pa : Der SRel n (a * c) (c * a')) (pb : Der SRel n (b * c) (c * b'))
    (cc : Der SRel n (c * c') 1) (e : Der SRel n a' b') : Der SRel n a b := by
  apply cl_eq.1
  have pa := cl_eq.2 pa
  have pb := cl_eq.2 pb
  have cc := cl_eq.2 cc
  have e := cl_eq.2 e
  rw [cl_mul, cl_mul] at pa pb
  rw [cl_mul, cl_one] at cc
  calc cl _ n a = cl _ n a * (cl _ n c * cl _ n c') := by rw [cc, mul_one]
    _ = cl _ n c * cl _ n a' * cl _ n c' := by rw [← mul_assoc, pa]
    _ = cl _ n c * cl _ n b' * cl _ n c' := by rw [e]
    _ = cl _ n b * (cl _ n c * cl _ n c') := by rw [← pb, mul_assoc]
    _ = cl _ n b := by rw [cc, mul_one]

private theorem heq_index {α : ℕ → Type} {a b : ℕ} (h : a = b) (f : ∀ t, α t) :
    HEq (f a) (f b) := by
  subst h; rfl

omit [HasSwap Gate] in
private theorem heq_up {a b : ℕ} (hab : a = b) {x : Gen Gate a} {y : Gen Gate b} (h : HEq x y) :
    HEq x.up y.up := by
  subst hab; cases h; rfl

omit [HasSwap Gate] in
private theorem heq_of_mul {a b : ℕ} (hab : a = b) {x : Gen Gate a} {y : Gen Gate b}
    {w : Circuit Gate a} {v : Circuit Gate b} (h : HEq x y) (h' : HEq w v) :
    HEq (FreeMonoid.of x * w) (FreeMonoid.of y * v) := by
  subst hab; cases h; cases h'; rfl

omit [HasSwap Gate] in
/-- Widening by no wires changes nothing (the Agda's `↧0₀` … `↧0₄`, at every
width). -/
theorem gen_pad_zero : ∀ {k : ℕ} (x : Gen Gate k), HEq (x.pad 0) x
  | _, @Gen.gate0 _ m c => heq_index (Nat.zero_add m) (fun t => (Gen.gate0 c : Gen Gate t))
  | _, @Gen.gate1 _ m c => heq_index (Nat.zero_add m) (fun t => (Gen.gate1 c : Gen Gate (t + 1)))
  | _, @Gen.gate2 _ m c => heq_index (Nat.zero_add m) (fun t => (Gen.gate2 c : Gen Gate (t + 2)))
  | _, @Gen.gate3 _ m c => heq_index (Nat.zero_add m) (fun t => (Gen.gate3 c : Gen Gate (t + 3)))
  | _, @Gen.up _ m x => heq_up (Nat.zero_add m) (gen_pad_zero x)

omit [HasSwap Gate] in
theorem circuit_pad_zero {k : ℕ} (w : Circuit Gate k) : HEq (Circuit.pad 0 w) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact heq_index (Nat.zero_add k) (fun t => (1 : Circuit Gate t))
  | mul_of x w ih =>
    rw [map_mul]
    exact heq_of_mul (Nat.zero_add k) (gen_pad_zero x) ih

/-- An equation read at an equal width. -/
private theorem der_cast {a b : ℕ} (h : a = b) {w v : Circuit Gate a} {w' v' : Circuit Gate b}
    (hw : HEq w w') (hv : HEq v v') (d : Der SRel a w v) : Der SRel b w' v' := by
  subst h; cases hw; cases hv; exact d

theorem pad₀ {w v : Circuit Gate 0} (p : Der SRel 0 w v) :
    ∀ n, Der SRel (n + 0) (Circuit.pad n w) (Circuit.pad n v)
  | 0 => der_cast (Nat.zero_add 0).symm (circuit_pad_zero w).symm (circuit_pad_zero v).symm p
  | n + 1 => conj_back (nat₀ w) (nat₀ v) (σσInv 0) (lemma_cong_up (pad₀ p n))

theorem pad₁ {w v : Circuit Gate 1} (p : Der SRel 1 w v) :
    ∀ n, Der SRel (n + 1) (Circuit.pad n w) (Circuit.pad n v)
  | 0 => der_cast (Nat.zero_add 1).symm (circuit_pad_zero w).symm (circuit_pad_zero v).symm p
  | n + 1 => conj_back (nat₁ w) (nat₁ v) (σσInv 1) (lemma_cong_up (pad₁ p n))

theorem pad₂ {w v : Circuit Gate 2} (p : Der SRel 2 w v) :
    ∀ n, Der SRel (n + 2) (Circuit.pad n w) (Circuit.pad n v)
  | 0 => der_cast (Nat.zero_add 2).symm (circuit_pad_zero w).symm (circuit_pad_zero v).symm p
  | n + 1 => conj_back (nat₂ w) (nat₂ v) (σσInv 2) (lemma_cong_up (pad₂ p n))

theorem pad₃ {w v : Circuit Gate 3} (p : Der SRel 3 w v) :
    ∀ n, Der SRel (n + 3) (Circuit.pad n w) (Circuit.pad n v)
  | 0 => der_cast (Nat.zero_add 3).symm (circuit_pad_zero w).symm (circuit_pad_zero v).symm p
  | n + 1 => conj_back (nat₃ w) (nat₃ v) (σσInv 3) (lemma_cong_up (pad₃ p n))

theorem pad₄ {w v : Circuit Gate 4} (p : Der SRel 4 w v) :
    ∀ n, Der SRel (n + 4) (Circuit.pad n w) (Circuit.pad n v)
  | 0 => der_cast (Nat.zero_add 4).symm (circuit_pad_zero w).symm (circuit_pad_zero v).symm p
  | n + 1 => conj_back (nat₄ w) (nat₄ v) (σσInv 4) (lemma_cong_up (pad₄ p n))

/-- All five at once. -/
theorem pad : ∀ {k : ℕ} {w v : Circuit Gate k}, k ≤ 4 → Der SRel k w v →
    ∀ n, Der SRel (n + k) (Circuit.pad n w) (Circuit.pad n v)
  | 0, _, _, _, p, n => pad₀ p n
  | 1, _, _, _, p, n => pad₁ p n
  | 2, _, _, _, p, n => pad₂ p n
  | 3, _, _, _, p, n => pad₃ p n
  | 4, _, _, _, p, n => pad₄ p n
  | _ + 5, _, _, hk, _, _ => absurd hk (by omega)

end QCert.Alt16RevCir.CircuitProp
