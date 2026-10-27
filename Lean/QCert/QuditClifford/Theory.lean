/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits: soundness and invertibility

Soundness of every rule of Figure 1 (Proposition A.28) and of the
structural rules, and invertibility of every generator modulo the rules
(`grouplike`), the half of Theorem 4.10 that needs no normal form.  The
generator inverses: `(-ω)^{2p-1}`, `S^{p-1}`, `CZ^{p-1}` by (C0), (C1),
(C6), and `H³` by `H_pow_four`, a derivation of `H⁴ = 1` (Corollary A.8).
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

theorem derives_shift (g : ZMod p) {n : ℕ} {w v : Circ n} (h : Derives (Padded (Rule p g)) n w v) :
    Derives (Padded (Rule p g)) (n + 1) (Circuit.shift w) (Circuit.shift v) := by
  have : conGen (Theory p g n) ≤ (conGen (Theory p g (n + 1))).comap Circuit.shift (map_mul _) :=
    Con.conGen_le fun a b hab => ConGen.Rel.of _ _ (Lift.shift hab)
  exact this h

theorem derives_rule (g : ZMod p) {n k : ℕ} {w v : Circ k} (h : Rule p g k w v) :
    Derives (Padded (Rule p g)) (n + k) (Circuit.pad n w) (Circuit.pad n v) :=
  Derivable.of (Lift.rule (Padded.pad n h))

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

theorem derives_pow (g : ZMod p) {n : ℕ} {w v : Circ n} (h : Derives (Padded (Rule p g)) n w v)
    (k : ℕ) : Derives (Padded (Rule p g)) n (w ^ k) (v ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/-- The scalar `-ω` commutes with every generator, by the structural rules. -/
theorem scalar_comm (g : ZMod p) : {n : ℕ} → (x : Gen Gate n) →
    Derives (Padded (Rule p g)) n (FreeMonoid.of (Gen.gate0 Gate.negω) * FreeMonoid.of x)
      (FreeMonoid.of x * FreeMonoid.of (Gen.gate0 Gate.negω))
  | _, .gate0 .negω => Derivable.refl _
  | n + 1, .gate1 h => by
    have hs : Derives (Padded (Rule p g)) (n + 1) (FreeMonoid.of (Gen.gate0 Gate.negω))
        (FreeMonoid.of (Gen.gate0 (n := n) Gate.negω).up) :=
      (Derivable.of (Lift.scalar Gate.negω)).symm
    exact ((hs.mul (Derivable.refl _)).trans (Derivable.of (Lift.comm1 h _))).trans
      ((Derivable.refl _).mul hs.symm)
  | n + 2, .gate2 h => by
    have hs1 : Derives (Padded (Rule p g)) (n + 2) (FreeMonoid.of (Gen.gate0 Gate.negω))
        (FreeMonoid.of (Gen.gate0 (n := n + 1) Gate.negω).up) :=
      (Derivable.of (Lift.scalar Gate.negω)).symm
    have hs2 := derives_shift p g (n := n + 1)
      (Derivable.of (Γ := Lift (Padded (Rule p g)) (n + 1)) (Lift.scalar (n := n) Gate.negω)).symm
    rw [Circuit.shift_of, Circuit.shift_of] at hs2
    have hs := hs1.trans hs2
    exact ((hs.mul (Derivable.refl _)).trans (Derivable.of (Lift.comm2 h _))).trans
      ((Derivable.refl _).mul hs.symm)
  | _, .gate3 h => nomatch h
  | n + 1, .up y => by
    have hs : Derives (Padded (Rule p g)) (n + 1) (FreeMonoid.of (Gen.gate0 Gate.negω))
        (FreeMonoid.of (Gen.gate0 (n := n) Gate.negω).up) :=
      (Derivable.of (Lift.scalar Gate.negω)).symm
    have ih := derives_shift p g (scalar_comm g y)
    rw [map_mul, map_mul, Circuit.shift_of, Circuit.shift_of] at ih
    exact ((hs.mul (Derivable.refl _)).trans ih).trans ((Derivable.refl _).mul hs.symm)

theorem scalar_pow_comm (g : ZMod p) {n : ℕ} (k : ℕ) (w : Circ n) :
    Derives (Padded (Rule p g)) n (FreeMonoid.of (Gen.gate0 Gate.negω) ^ k * w)
      (w * FreeMonoid.of (Gen.gate0 Gate.negω) ^ k) := by
  have h1 : ∀ w : Circ n, Derives (Padded (Rule p g)) n (FreeMonoid.of (Gen.gate0 Gate.negω) * w)
      (w * FreeMonoid.of (Gen.gate0 Gate.negω)) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => rw [mul_one, one_mul]
    | mul_of x w ih =>
      rw [← mul_assoc]
      refine ((scalar_comm p g x).mul (Derivable.refl w)).trans ?_
      rw [mul_assoc, mul_assoc]
      exact (Derivable.refl _).mul ih
  induction k with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ k ih =>
    rw [pow_succ, mul_assoc]
    refine ((Derivable.refl _).mul (h1 w)).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact ih.mul (Derivable.refl _)

/-- A generator of `ℤ_p^*` has `g^{(p-1)/2} = -1`. -/
theorem pow_half_eq_neg_one (hp2 : p ≠ 2) (g : ZMod p)
    (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a) : g ^ ((p - 1) / 2) = -1 := by
  have hg0 : g ≠ 0 := ne_zero_of_generates p hp2 g hg
  have hodd := hp.out.odd_of_ne_two hp2
  have hsq : (g ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩),
      ZMod.pow_card_sub_one_eq_one hg0]
  rw [sq] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exfalso
    obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
      rw [ZMod.ringChar_zmod_n]; exact hp2)
    have hb0 : b ≠ 0 := fun h0 => hb (h0 ▸ ⟨0, by simp⟩)
    obtain ⟨k, rfl⟩ := hg b hb0
    apply hb
    have hp1 : p % 2 = 1 := Nat.odd_iff.mp hodd
    rw [ZMod.euler_criterion p hb0, show p / 2 = (p - 1) / 2 by omega, ← pow_mul, mul_comm,
      pow_mul, h, one_pow]
  · exact h

/-- `H⁴ = 1` (Corollary A.8) is derivable: `H² = M_{-1} (-1)^{(p-1)/2}` by
(C2), `M_{-1} = M_g^{(p-1)/2}` and `M_{-1}² = M_g^{p-1} = M_1 = M_g^0 = 1`
by (C3), and `(-1)^{p-1} = 1` by (C0). -/
theorem H_pow_four (hp2 : p ≠ 2) (g : ZMod p) (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a)
    (n : ℕ) : Derives (Padded (Rule p g)) (n + 1) (FreeMonoid.of (Gen.gate1 Gate.H) ^ 4) 1 := by
  have hg0 : g ≠ 0 := ne_zero_of_generates p hp2 g hg
  have hodd := hp.out.odd_of_ne_two hp2
  have hm2 : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by obtain ⟨k, hk⟩ := hodd; omega
  -- (C2): `H² = (-ω)^{p (p-1)/2} M_{-1}`
  have h2 : Derives (Padded (Rule p g)) (n + 1) (FreeMonoid.of (Gen.gate1 Gate.H) ^ 2)
      (FreeMonoid.of (Gen.gate0 Gate.negω) ^ (p * ((p - 1) / 2)) *
        Circuit.pad n (M p (-1))) := by
    have := derives_rule p g (n := n) Rule.C2
    rw [seq_def, map_mul, map_pow, map_pow, neg1, map_pow, ← pow_mul] at this
    exact this
  -- `((-ω)^{p (p-1)/2})² = 1` by (C0)
  have hε : Derives (Padded (Rule p g)) (n + 1)
      (FreeMonoid.of (Gen.gate0 Gate.negω) ^ (p * ((p - 1) / 2)) *
        FreeMonoid.of (Gen.gate0 Gate.negω) ^ (p * ((p - 1) / 2))) 1 := by
    have h0 := derives_rule p g (n := n + 1) Rule.C0
    rw [map_pow, map_one] at h0
    have := derives_pow p g h0 ((p - 1) / 2)
    rw [one_pow, ← pow_mul] at this
    rw [← pow_add, show p * ((p - 1) / 2) + p * ((p - 1) / 2) = 2 * p * ((p - 1) / 2) by ring]
    exact this
  -- `M_{-1}² = 1` by (C3)
  have hMM : Derives (Padded (Rule p g)) (n + 1)
      (Circuit.pad n (M p (-1)) * Circuit.pad n (M p (-1))) 1 := by
    have hj := pow_half_eq_neg_one p hp2 g hg
    have hval : ∀ k : ℕ, k < p → ((k : ZMod p)).val = k := fun k hk => by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    have c3 : ∀ k : ℕ, k < p → Derives (Padded (Rule p g)) (n + 1)
        (Circuit.pad n (M p g) ^ k) (Circuit.pad n (M p (g ^ k))) := by
      intro k hk
      have := derives_rule p g (n := n) (Rule.C3 (k : ZMod p))
      rw [map_pow, hval k hk] at this
      exact this
    have hpos := hp.out.pos
    have hlt1 : (p - 1) / 2 < p := by omega
    have hlt2 : p - 1 < p := by omega
    have e1 := c3 ((p - 1) / 2) hlt1
    rw [hj] at e1
    have e2 := c3 (p - 1) hlt2
    rw [ZMod.pow_card_sub_one_eq_one hg0] at e2
    have e3 := c3 0 hp.out.pos
    rw [pow_zero, pow_zero] at e3
    refine (e1.symm.mul e1.symm).trans ?_
    rw [← pow_add, hm2]
    exact e2.trans e3.symm
  have hcomm := (scalar_pow_comm p g (n := n + 1) (p * ((p - 1) / 2))
    (Circuit.pad n (M p (-1)))).symm
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  refine (h2.mul h2).trans ?_
  rw [mul_assoc, ← mul_assoc (Circuit.pad n (M p (-1)))]
  refine ((Derivable.refl _).mul (hcomm.mul (Derivable.refl _))).trans ?_
  rw [mul_assoc, ← mul_assoc (FreeMonoid.of (Gen.gate0 Gate.negω) ^ (p * ((p - 1) / 2)))]
  exact (hε.mul hMM).trans (by rw [mul_one])

/-- Every generator has an inverse modulo the rules: `(-ω)^{2p-1}`,
`S^{p-1}`, `CZ^{p-1}` by (C0), (C1), (C6), and `H³` by `H_pow_four`. -/
theorem exists_inverse (hp2 : p ≠ 2) (g : ZMod p)
    (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a) : {n : ℕ} → (x : Gen Gate n) →
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
      rw [← pow_succ]; exact H_pow_four p hp2 g hg n⟩
  | _, .gate3 x => nomatch x
  | _, .up x => by
    obtain ⟨w, hw⟩ := exists_inverse hp2 g hg x
    refine ⟨Circuit.shift w, ?_⟩
    have := derives_shift p g hw
    rwa [map_mul, map_one, Circuit.shift_of] at this

/-- Every generator is invertible modulo the rules. -/
theorem grouplike (hp2 : p ≠ 2) (g : ZMod p) (hg : ∀ a : ZMod p, a ≠ 0 → ∃ k : ℕ, g ^ k = a)
    (n : ℕ) : Grouplike (Theory p g n) := fun x => exists_inverse p hp2 g hg x

end QCert.QuditClifford
