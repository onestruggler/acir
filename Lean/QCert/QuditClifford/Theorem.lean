/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits in odd prime dimension: Theorem 4.10

Bian, Li, Ross, van de Wetering and Zhao (arXiv:2609.40106), Theorem 4.10:
for every odd prime `p`, the rules of Figure 1 are sound and complete for
`n`-qudit Clifford circuits — they only equate circuits that implement the
same linear map, and circuits that implement the same linear map are equal
by the rules.  With every generator invertible modulo the rules, this is
`theorem_4_10`: the rules present the group of operators the circuits
denote (`IsSubPresentationOf`), the matrix semantics being part of the
statement.

`g` is the generator of `ℤ_p^*` chosen in Figure 1; soundness holds for any
`g ≠ 0`, completeness needs `g` to generate.  Soundness of every rule is
proved (Proposition A.28), (C2) and (C3) through Gauss's evaluation of the
quadratic Gauss sum (`QCert.gauss_sum_sign`); the remaining `sorry`s are
listed in `README.md`.
-/
import QCert.QuditClifford.GaussScalar

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

/-- Proposition A.28: every rule of Figure 1 holds for the matrices of
Definition 2.11. -/
theorem rule_sound (hp2 : p ≠ 2) (g : ZMod p) (hg : g ≠ 0) {k : ℕ} {w v : Circ k}
    (h : Rule p g k w v) : sem p k w = sem p k v := by
  cases h with
  | C0 => exact sound_C0 p
  | C1 => exact sound_C1 p
  | C2 => exact sound_C2 p hp2
  | C3 k => exact sound_C3 p hp2 hg k
  | C4 => exact sound_C4 p hp2 g hg
  | C5 => exact sound_C5 p
  | C6 => exact sound_C6 p
  | C7 => exact sound_C7 p hp2
  | C8 => exact sound_C8 p
  | C9 => exact sound_C9 p hp2 g hg
  | C10 => exact sound_C10 p hp2
  | C11 => exact sound_C11 p hp2
  | C12 => exact sound_C12 p hp2
  | C13 => exact sound_C13 p hp2
  | C14 => exact sound_C14 p hp2
  | C15 => exact sound_C15 p hp2

/-- The rules and the structural rules hold at every width. -/
theorem theory_sound (hp2 : p ≠ 2) (g : ZMod p) (hg : g ≠ 0) {n : ℕ} {w v : Circ n}
    (h : Theory p g n w v) : sem p n w = sem p n v :=
  (gateSem p).lift_sound ((gateSem p).padded_sound fun _ _ _ h => rule_sound p hp2 g hg h) n w v h

/-- **Theorem 4.10, soundness**: the rules only equate circuits that
implement the same linear map. -/
theorem sound (hp2 : p ≠ 2) (g : ZMod p) (hg : g ≠ 0) {n : ℕ} {w v : Circ n}
    (h : Derives (Padded (Rule p g)) n w v) : sem p n w = sem p n v :=
  derivable_sound (fun _ _ h => theory_sound p hp2 g hg h) h

/-- **Theorem 4.10, completeness**: two `n`-qudit circuits that implement the
same linear map are equal by the rules of Figure 1, for `g` a generator of
`ℤ_p^*`. -/
theorem complete (hp2 : p ≠ 2) (g : ZMod p) (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a)
    {n : ℕ} {w v : Circ n} (h : sem p n w = sem p n v) : Derives (Padded (Rule p g)) n w v := by
  sorry

theorem derives_shift (g : ZMod p) {n : ℕ} {w v : Circ n} (h : Derives (Padded (Rule p g)) n w v) :
    Derives (Padded (Rule p g)) (n + 1) (Circuit.shift w) (Circuit.shift v) := by
  have : conGen (Theory p g n) ≤ (conGen (Theory p g (n + 1))).comap Circuit.shift (map_mul _) :=
    Con.conGen_le fun a b hab => ConGen.Rel.of _ _ (Lift.shift hab)
  exact this h

theorem derives_rule (g : ZMod p) {n k : ℕ} {w v : Circ k} (h : Rule p g k w v) :
    Derives (Padded (Rule p g)) (n + k) (Circuit.pad n w) (Circuit.pad n v) :=
  Derivable.of (Lift.rule (Padded.pad n h))

/-- Every generator has an inverse modulo the rules: `(-ω)^{2p-1}`,
`S^{p-1}`, `CZ^{p-1}` by (C0), (C1), (C6), and `H³`. -/
theorem exists_inverse (g : ZMod p) : {n : ℕ} → (x : Gen Gate n) →
    ∃ w, Derives (Padded (Rule p g)) n (w * FreeMonoid.of x) 1
  | n, .gate0 .negω => ⟨FreeMonoid.of (Gen.gate0 Gate.negω) ^ (2 * p - 1), by
      rw [← pow_succ, Nat.sub_add_cancel (by have := hp.out.one_lt; omega)]
      have h := derives_rule p g (n := n) Rule.C0
      rw [map_pow, map_one] at h
      exact h⟩
  | n + 1, .gate1 .S => ⟨FreeMonoid.of (Gen.gate1 Gate.S) ^ (p - 1), by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
      have h := derives_rule p g (n := n) Rule.C1
      rw [map_pow, map_one] at h
      exact h⟩
  | n + 2, .gate2 .CZ => ⟨FreeMonoid.of (Gen.gate2 Gate.CZ) ^ (p - 1), by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
      have h := derives_rule p g (n := n) Rule.C6
      rw [map_pow, map_one] at h
      exact h⟩
  | n + 1, .gate1 .H => ⟨FreeMonoid.of (Gen.gate1 Gate.H) ^ 3, by
      -- `H⁴ = 1` (Corollary A.8), derivable from (C0), (C2) and (C3)
      sorry⟩
  | _, .gate3 x => nomatch x
  | _, .up x => by
    obtain ⟨w, hw⟩ := exists_inverse g x
    refine ⟨Circuit.shift w, ?_⟩
    have := derives_shift p g hw
    rwa [map_mul, map_one, Circuit.shift_of] at this

/-- Every generator is invertible modulo the rules. -/
theorem grouplike (g : ZMod p) (n : ℕ) : Grouplike (Theory p g n) := fun x => exists_inverse p g x

/-- A generator of `ℤ_p^*` is not `0`. -/
theorem ne_zero_of_generates (hp2 : p ≠ 2) (g : ZMod p)
    (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a) : g ≠ 0 := by
  haveI : Fact (2 < p) := ⟨by have := hp.out.two_le; omega⟩
  intro h0
  obtain ⟨k, hk⟩ := hg (-1) (neg_ne_zero.mpr one_ne_zero)
  rw [h0] at hk
  rcases k with _ | k
  · rw [pow_zero] at hk; exact ZMod.neg_one_ne_one hk.symm
  · rw [zero_pow (Nat.succ_ne_zero k)] at hk; exact neg_ne_zero.mpr one_ne_zero hk.symm

/-- **Theorem 4.10**: for every odd prime `p` and generator `g` of `ℤ_p^*`,
the rules of Figure 1 with the structural rules are sound and complete for
`n`-qudit Clifford circuits, at every `n`: they present the group of
operators that the circuits denote. -/
theorem theorem_4_10 (hp2 : p ≠ 2) (g : ZMod p) (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a)
    (n : ℕ) : IsSubPresentationOf (Theory p g n) ((gateSem p).gen (n := n)) where
  grouplike := grouplike p g n
  sound _ _ h := theory_sound p hp2 g (ne_zero_of_generates p hp2 g hg) h
  complete _ _ h := complete p hp2 g hg h

end QCert.QuditClifford
