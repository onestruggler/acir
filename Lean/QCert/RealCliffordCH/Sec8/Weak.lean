/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: weakening and the semantic step (Lemma 5.1)

The proofs of Lemmas 8.7 and 8.8 on `n` wires take completeness on every
smaller width as a hypothesis (`IH n`).  This is the paper's Lemma 5.1, and
it is the only way equations on fewer wires enter: an `n`-wire derivation
may replace a window of the circuit that acts on fewer wires by any other
such window with the same semantics.

* Weakening: a derivation on `k` wires holds on the bottom `k` wires of any
  wider circuit (`derivable_pad`, from `Minimality`), moved up
  (`derivable_shift`), and with one idle wire on top (`derivable_padTop`).
  `padTop` is `Circuit.pad 1` with the width written `n + 1` rather than
  `1 + n`.
* The semantic step: two circuits idle on the bottom wire (`shift a`,
  `shift b`) or on the top wire (`padTop a`, `padTop b`) are equal as soon
  as their semantics agree (`sem_step_shift`, `sem_step_top`); on the
  bottom `k < n` wires likewise (`sem_step_pad`).
* The window step: a window `w` that a circuit `c` with inverse `c'`
  conjugates to a circuit idle on the bottom wire (`c' w c ≈ shift a`) may
  be replaced by any window `v` with the same semantics that the same `c`
  conjugates to such a circuit (`window`).  This is how a step of the paper
  on wires that are not the bottom ones, brought there by a swap network,
  becomes a single semantic step.
-/
import QCert.RealCliffordCH.Sec8.Statement
import QCert.RealCliffordCH.Soundness
import QCert.RealCliffordCH.Grouplike
import QCert.Minimality.Engine

namespace QCert.RealCliffordCH.Sec8

open Circuit Matrix

/-- Completeness on every width below `n` (Lemma 5.1). -/
def IH (n : ℕ) : Prop := ∀ k < n, CompleteAt k

theorem IH.mono {n m : ℕ} (h : IH n) (hm : m ≤ n) : IH m := fun k hk => h k (by omega)

/-! ## Derivations as a congruence -/

section Congr

variable {N : ℕ}

theorem dmul {a b c d : Circ N} (h : Derivable (theory N) a b) (h' : Derivable (theory N) c d) :
    Derivable (theory N) (a * c) (b * d) := h.mul h'

theorem dctx (u v : Circ N) {a b : Circ N} (h : Derivable (theory N) a b) :
    Derivable (theory N) (u * a * v) (u * b * v) :=
  ((Derivable.refl u).mul h).mul (Derivable.refl v)

theorem dleft (u : Circ N) {a b : Circ N} (h : Derivable (theory N) a b) :
    Derivable (theory N) (u * a) (u * b) := (Derivable.refl u).mul h

theorem dright (v : Circ N) {a b : Circ N} (h : Derivable (theory N) a b) :
    Derivable (theory N) (a * v) (b * v) := h.mul (Derivable.refl v)

/-- An equation of the theory holds in the semantics. -/
theorem sem_of_derivable {a b : Circ N} (h : Derivable (theory N) a b) :
    S.sem N a = S.sem N b :=
  derivable_sound (fun _ _ r => sound N r) h

/-- An identity decided over ℚ(√2) holds in the semantics. -/
theorem sem_of_eval {a b : Circ N} (h : opsQ.eval N a = opsQ.eval N b) : S.sem N a = S.sem N b :=
  S.sem_eq_of_eval QSqrt2.toR opsQ toOps_eq h

end Congr

/-! ## Weakening -/

/-- A generator with one idle wire on top. -/
def Gen.padTop : {n : ℕ} → Gen Gate n → Gen Gate (n + 1)
  | _, .gate0 c => .gate0 c
  | _, .gate1 g => .gate1 g
  | _, .gate2 g => .gate2 g
  | _, .gate3 g => .gate3 g
  | _, .up g => .up (Gen.padTop g)

/-- A circuit with one idle wire on top: `Circuit.pad 1` with the width
written `n + 1`. -/
def padTop {n : ℕ} : Circ n →* Circ (n + 1) := FreeMonoid.map Gen.padTop

@[simp] theorem padTop_of {n : ℕ} (g : Gen Gate n) :
    padTop (FreeMonoid.of g) = FreeMonoid.of (Gen.padTop g) := rfl

theorem Gen.pad_one_heq {n : ℕ} (g : Gen Gate n) : HEq (g.pad 1) (Gen.padTop g) := by
  induction g with
  | @gate0 m c =>
    exact Minimality.heq_index (Nat.add_comm 1 m) (fun t => (Gen.gate0 c : Gen Gate t))
  | @gate1 m c =>
    exact Minimality.heq_index (Nat.add_comm 1 m) (fun t => (Gen.gate1 c : Gen Gate (t + 1)))
  | @gate2 m c =>
    exact Minimality.heq_index (Nat.add_comm 1 m) (fun t => (Gen.gate2 c : Gen Gate (t + 2)))
  | @gate3 m c =>
    exact Minimality.heq_index (Nat.add_comm 1 m) (fun t => (Gen.gate3 c : Gen Gate (t + 3)))
  | @up m g ih => exact Minimality.heq_up (Nat.add_comm 1 m) ih

theorem pad_one_heq {n : ℕ} (w : Circ n) : HEq (Circuit.pad 1 w) (padTop w) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one, map_one]
    exact Minimality.heq_index (Nat.add_comm 1 n) (fun t => (1 : Circ t))
  | mul_of g w ih =>
    rw [map_mul, map_mul]
    exact Minimality.heq_mul (Nat.add_comm 1 n)
      (Minimality.heq_of (Nat.add_comm 1 n) (Gen.pad_one_heq g)) ih

/-- Moving a derivation along an equality of widths. -/
theorem derivable_cast {a b : ℕ} (h : a = b) {w v : Circ a} {w' v' : Circ b}
    (hw : HEq w w') (hv : HEq v v') (d : Derivable (theory a) w v) :
    Derivable (theory b) w' v' := by
  subst h; cases hw; cases hv; exact d

/-- A derivation on the bottom `k` wires of `m + k` wires. -/
theorem derivable_pad (m : ℕ) {k : ℕ} {w v : Circ k} (d : Derivable (theory k) w v) :
    Derivable (theory (m + k)) (Circuit.pad m w) (Circuit.pad m v) :=
  Minimality.derivable_pad m d

/-- A derivation with an idle wire on top. -/
theorem derivable_padTop {n : ℕ} {w v : Circ n} (d : Derivable (theory n) w v) :
    Derivable (theory (n + 1)) (padTop w) (padTop v) :=
  derivable_cast (Nat.add_comm 1 n) (pad_one_heq w) (pad_one_heq v) (derivable_pad 1 d)

/-! ## The semantic step -/

/-- Lemma 5.1 below the bottom wire: two circuits idle on wire 0 are equal
when their semantics agree. -/
theorem sem_step_shift {N : ℕ} (ih : IH (N + 1)) {a b : Circ N} (h : S.sem N a = S.sem N b) :
    Derivable (theory (N + 1)) (shift a) (shift b) :=
  derivable_shift (ih N (Nat.lt_succ_self N) a b h)

/-- Lemma 5.1 above the top wire. -/
theorem sem_step_top {N : ℕ} (ih : IH (N + 1)) {a b : Circ N} (h : S.sem N a = S.sem N b) :
    Derivable (theory (N + 1)) (padTop a) (padTop b) :=
  derivable_padTop (ih N (Nat.lt_succ_self N) a b h)

/-- Lemma 5.1 on the bottom `k` of `m + k` wires, `m ≥ 1`. -/
theorem sem_step_pad {m k : ℕ} (ih : IH (m + k)) (hm : 0 < m) {a b : Circ k}
    (h : S.sem k a = S.sem k b) : Derivable (theory (m + k)) (Circuit.pad m a) (Circuit.pad m b) :=
  derivable_pad m (ih k (by omega) a b h)

/-- A fixed-width equation on `K` wires on the bottom wires of `m + K` wires:
by Lemma 5.1 when `m ≥ 1`, by its own derivation `h0` when `m = 0`.  This
is the form in which the equations of Appendices D.1–D.4 are used. -/
theorem small_of {K : ℕ} {l r : Circ K} (hsem : S.sem K l = S.sem K r)
    (h0 : IH K → Derivable (theory K) l r) (m : ℕ) (ih : IH (m + K)) :
    Derivable (theory (m + K)) (Circuit.pad m l) (Circuit.pad m r) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact derivable_pad 0 (h0 (ih.mono (by omega)))
  · exact sem_step_pad ih hm hsem

/-! ## The window step -/

theorem onTop_one_injective {R : Type*} [CommRing R] {d n : ℕ} [NeZero d] {M M' : Op R d n}
    (h : onTop 1 M = onTop 1 M') : M = M' := by
  ext x y
  have := congrFun (congrFun h ((split d n 1).symm (fun _ => 0, x)))
    ((split d n 1).symm (fun _ => 0, y))
  simpa [onTop_apply] using this

theorem sem_shift_injective {N : ℕ} {a b : Circ N}
    (h : S.sem (N + 1) (shift a) = S.sem (N + 1) (shift b)) : S.sem N a = S.sem N b := by
  rw [S.sem_shift, S.sem_shift] at h
  exact Subtype.ext (onTop_one_injective (congrArg Subtype.val h))

/-- The window step.  `c` and `c'` are inverse (typically a swap network and
its reverse), and conjugating the windows `w` and `v` by them gives circuits
idle on the bottom wire.  Then `w` and `v` are equal as soon as they have
the same semantics. -/
theorem window {N : ℕ} (ih : IH (N + 1)) (c c' : Circ (N + 1))
    (hcc : Derivable (theory (N + 1)) (c * c') 1) {w v : Circ (N + 1)} {a b : Circ N}
    (hw : Derivable (theory (N + 1)) (c' * w * c) (shift a))
    (hv : Derivable (theory (N + 1)) (c' * v * c) (shift b))
    (h : S.sem (N + 1) w = S.sem (N + 1) v) : Derivable (theory (N + 1)) w v := by
  have hsa : S.sem (N + 1) (shift a) = S.sem (N + 1) (shift b) := by
    rw [← sem_of_derivable hw, ← sem_of_derivable hv, map_mul, map_mul, map_mul, map_mul, h]
  have hab : Derivable (theory (N + 1)) (c' * w * c) (c' * v * c) :=
    hw.trans ((sem_step_shift ih (sem_shift_injective hsa)).trans hv.symm)
  have e : ∀ x : Circ (N + 1), Derivable (theory (N + 1)) x (c * (c' * x * c) * c') := by
    intro x
    have h1 : Derivable (theory (N + 1)) (c * (c' * x * c) * c') ((c * c') * x * (c * c')) := by
      simp only [mul_assoc]; exact Derivable.refl _
    refine Derivable.symm (h1.trans ?_)
    have := dmul (dmul hcc (Derivable.refl x)) hcc
    simpa using this
  exact (e w).trans ((dctx c c' hab).trans (e v).symm)

/-- The window step with the semantic hypothesis one wire down: the windows
conjugated to `shift a` and `shift b` with `a`, `b` of the same semantics. -/
theorem window' {N : ℕ} (ih : IH (N + 1)) (c c' : Circ (N + 1))
    (hcc : Derivable (theory (N + 1)) (c * c') 1) {w v : Circ (N + 1)} {a b : Circ N}
    (hw : Derivable (theory (N + 1)) (c' * w * c) (shift a))
    (hv : Derivable (theory (N + 1)) (c' * v * c) (shift b))
    (h : S.sem N a = S.sem N b) : Derivable (theory (N + 1)) w v := by
  refine window ih c c' hcc hw hv ?_
  have e : ∀ x : Circ (N + 1), Derivable (theory (N + 1)) x (c * (c' * x * c) * c') := by
    intro x
    have h1 : Derivable (theory (N + 1)) (c * (c' * x * c) * c') ((c * c') * x * (c * c')) := by
      simp only [mul_assoc]; exact Derivable.refl _
    refine Derivable.symm (h1.trans ?_)
    have := dmul (dmul hcc (Derivable.refl x)) hcc
    simpa using this
  rw [sem_of_derivable ((e w).trans (dctx c c' hw)), sem_of_derivable ((e v).trans (dctx c c' hv)),
    map_mul, map_mul, map_mul, map_mul, S.sem_shift, S.sem_shift, h]

/-! ## Conjugation helpers -/

section ConjHelpers

variable {N : ℕ}

/-- `b a` is inverted by `a b` when `a`, `b` are involutions. -/
theorem inv_pair {a b : Circ N} (ha : Derivable (theory N) (a * a) 1)
    (hb : Derivable (theory N) (b * b) 1) : Derivable (theory N) (b * a * (a * b)) 1 := by
  have e : b * a * (a * b) = b * (a * a) * b := by simp only [mul_assoc]
  rw [e]
  have := dmul (dmul (Derivable.refl b) ha) (Derivable.refl b)
  rw [mul_one] at this
  exact this.trans hb

/-- Conjugating two conjugated windows by the inverse of the conjugator. -/
theorem conj_two {c c' A B : Circ N} (h : Derivable (theory N) (c' * c) 1) :
    Derivable (theory N) (c' * (c * A * c' * (c * B * c')) * c) (A * B) := by
  have e : c' * (c * A * c' * (c * B * c')) * c = (c' * c) * A * (c' * c) * B * (c' * c) := by
    simp only [mul_assoc]
  rw [e]
  have := dmul (dmul (dmul (dmul h (Derivable.refl A)) h) (Derivable.refl B)) h
  simpa only [one_mul, mul_one] using this

end ConjHelpers

end QCert.RealCliffordCH.Sec8
