/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Generators on disjoint wires commute

`comm_apart`: in any theory `Lift R`, two generators acting on disjoint wires
commute, and so does a scalar with every generator (when all scalars are
equal).  This is the interchange law, derived from the structural rules
`Lift.comm1`–`comm3`, `Lift.scalar` and `Lift.shift`.
-/
import QCert.Minimality.Engine

namespace QCert.Minimality

open Circuit

variable {Gate : ℕ → Type}

/-- The wires a generator acts on, `lo ≤ i < hi`; `none` for a scalar. -/
def Gen.span : {n : ℕ} → Gen Gate n → Option (ℕ × ℕ)
  | _, .gate0 _ => none
  | _, .gate1 _ => some (0, 1)
  | _, .gate2 _ => some (0, 2)
  | _, .gate3 _ => some (0, 3)
  | _, .up g => (Gen.span g).map fun p => (p.1 + 1, p.2 + 1)

/-- Two generators on disjoint wires (a scalar is apart from everything). -/
def Gen.apart {n : ℕ} (g h : Gen Gate n) : Bool :=
  match Gen.span g, Gen.span h with
  | some (a, b), some (c, d) => b ≤ c || d ≤ a
  | _, _ => true

section Comm

variable {R : CRel Gate}

/-- A scalar moved up is the scalar. -/
theorem scalar_up_derivable {n : ℕ} (c : Gate 0) :
    Derivable (Lift R (n + 1)) (FreeMonoid.of (Gen.gate0 c).up) (g0 c) :=
  Derivable.of (Lift.scalar c)

/-- A generator without wires (a scalar, possibly moved up) is a scalar. -/
theorem span_none_scalar : ∀ {n : ℕ} (g : Gen Gate n), Gen.span g = none →
    ∃ c : Gate 0, Derivable (Lift R n) (FreeMonoid.of g) (g0 c)
  | _, .gate0 c, _ => ⟨c, Derivable.refl _⟩
  | _, .up g, h => by
    simp only [Gen.span, Option.map_eq_none_iff] at h
    obtain ⟨c, hc⟩ := span_none_scalar g h
    exact ⟨c, (derivable_shift hc).trans (scalar_up_derivable c)⟩

theorem scalar_up2 {n : ℕ} (c : Gate 0) :
    Derivable (Lift R (n + 2)) (g0 c) (FreeMonoid.of (Gen.gate0 c).up.up) := by
  have h1 : Derivable (Lift R (n + 2)) (FreeMonoid.of (Gen.gate0 c).up.up)
      (FreeMonoid.of (Gen.gate0 c).up) := derivable_shift (scalar_up_derivable (n := n) c)
  exact (h1.trans (scalar_up_derivable c)).symm

theorem scalar_up3 {n : ℕ} (c : Gate 0) :
    Derivable (Lift R (n + 3)) (g0 c) (FreeMonoid.of (Gen.gate0 c).up.up.up) := by
  have h1 := derivable_shift (R := R) (scalar_up2 (n := n) c).symm
  rw [Circuit.shift_of, Circuit.shift_of] at h1
  exact (h1.trans (scalar_up_derivable c)).symm

/-- A scalar commutes with every generator (all scalars being equal). -/
theorem scalar_comm (hsc : ∀ c c' : Gate 0, c = c') (c : Gate 0) :
    ∀ {n : ℕ} (h : Gen Gate n),
      Derivable (Lift R n) (g0 c * FreeMonoid.of h) (FreeMonoid.of h * g0 c)
  | _, .gate0 c' => by rw [hsc c c']
  | _, @Gen.gate1 _ m g => by
    have e := (scalar_up_derivable (R := R) (n := m) c).symm
    refine (e.mul (Derivable.refl _)).trans ?_
    refine (Derivable.of (Lift.comm1 g (Gen.gate0 c))).trans ?_
    exact (Derivable.refl _).mul (scalar_up_derivable c)
  | _, @Gen.gate2 _ m g => by
    have e := scalar_up2 (R := R) (n := m) c
    refine (e.mul (Derivable.refl _)).trans ?_
    refine (Derivable.of (Lift.comm2 g (Gen.gate0 c))).trans ?_
    exact (Derivable.refl _).mul e.symm
  | _, @Gen.gate3 _ m g => by
    have e := scalar_up3 (R := R) (n := m) c
    refine (e.mul (Derivable.refl _)).trans ?_
    refine (Derivable.of (Lift.comm3 g (Gen.gate0 c))).trans ?_
    exact (Derivable.refl _).mul e.symm
  | _, @Gen.up _ m h => by
    have e := (scalar_up_derivable (R := R) (n := m) c).symm
    have s := derivable_shift (R := R) (scalar_comm hsc c h)
    rw [map_mul, map_mul, Circuit.shift_of, Circuit.shift_of] at s
    exact (e.mul (Derivable.refl _)).trans (s.trans ((Derivable.refl _).mul e.symm))

/-- A generator without wires commutes with every generator. -/
theorem none_comm (hsc : ∀ c c' : Gate 0, c = c') {n : ℕ} (g h : Gen Gate n)
    (hg : Gen.span g = none) :
    Derivable (Lift R n) (FreeMonoid.of g * FreeMonoid.of h)
      (FreeMonoid.of h * FreeMonoid.of g) := by
  obtain ⟨c, hc⟩ := span_none_scalar (R := R) g hg
  exact (hc.mul (Derivable.refl _)).trans
    ((scalar_comm hsc c h).trans ((Derivable.refl _).mul hc.symm))

theorem span_up_eq {n : ℕ} (g : Gen Gate n) (a b : ℕ) (h : Gen.span g.up = some (a, b)) :
    ∃ a₁ b₁, Gen.span g = some (a₁, b₁) ∧ a = a₁ + 1 ∧ b = b₁ + 1 := by
  simp only [Gen.span, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨a₁, b₁⟩, h1, rfl, rfl⟩ := h
  exact ⟨a₁, b₁, h1, rfl, rfl⟩

theorem bottom_comm1 {m : ℕ} (c : Gate 1) (h : Gen Gate (m + 1)) (a b : ℕ)
    (hs : Gen.span h = some (a, b)) (hka : 1 ≤ a) :
    Derivable (Lift R (m + 1)) (g1 c * FreeMonoid.of h) (FreeMonoid.of h * g1 c) := by
  cases h with
  | up h₀ => exact (Derivable.of (Lift.comm1 c h₀)).symm
  | gate0 _ => simp [Gen.span] at hs
  | gate1 _ => simp [Gen.span] at hs; omega
  | gate2 _ => simp [Gen.span] at hs; omega
  | gate3 _ => simp [Gen.span] at hs; omega

theorem bottom_comm2 {m : ℕ} (c : Gate 2) (h : Gen Gate (m + 2)) (a b : ℕ)
    (hs : Gen.span h = some (a, b)) (hka : 2 ≤ a) :
    Derivable (Lift R (m + 2)) (g2 c * FreeMonoid.of h) (FreeMonoid.of h * g2 c) := by
  cases h with
  | up h₁ =>
    cases h₁ with
    | up h₀ => exact (Derivable.of (Lift.comm2 c h₀)).symm
    | gate0 _ => simp [Gen.span] at hs
    | gate1 _ => simp [Gen.span] at hs; omega
    | gate2 _ => simp [Gen.span] at hs; omega
    | gate3 _ => simp [Gen.span] at hs; omega
  | gate0 _ => simp [Gen.span] at hs
  | gate1 _ => simp [Gen.span] at hs; omega
  | gate2 _ => simp [Gen.span] at hs; omega
  | gate3 _ => simp [Gen.span] at hs; omega

theorem bottom_comm3 {m : ℕ} (c : Gate 3) (h : Gen Gate (m + 3)) (a b : ℕ)
    (hs : Gen.span h = some (a, b)) (hka : 3 ≤ a) :
    Derivable (Lift R (m + 3)) (g3 c * FreeMonoid.of h) (FreeMonoid.of h * g3 c) := by
  cases h with
  | up h₁ =>
    cases h₁ with
    | up h₂ =>
      cases h₂ with
      | up h₀ => exact (Derivable.of (Lift.comm3 c h₀)).symm
      | gate0 _ => simp [Gen.span] at hs
      | gate1 _ => simp [Gen.span] at hs; omega
      | gate2 _ => simp [Gen.span] at hs; omega
      | gate3 _ => simp [Gen.span] at hs; omega
    | gate0 _ => simp [Gen.span] at hs
    | gate1 _ => simp [Gen.span] at hs; omega
    | gate2 _ => simp [Gen.span] at hs; omega
    | gate3 _ => simp [Gen.span] at hs; omega
  | gate0 _ => simp [Gen.span] at hs
  | gate1 _ => simp [Gen.span] at hs; omega
  | gate2 _ => simp [Gen.span] at hs; omega
  | gate3 _ => simp [Gen.span] at hs; omega

theorem lo_of_apart {n : ℕ} {k : ℕ} {h : Gen Gate n} {a b : ℕ}
    (hs : Gen.span h = some (a, b)) (hd : k ≤ a ∨ b ≤ 0) : k ≤ a := by
  rcases hd with hd | hd
  · exact hd
  · exfalso
    induction h generalizing a b with
    | gate0 _ => simp [Gen.span] at hs
    | gate1 _ => simp [Gen.span] at hs; omega
    | gate2 _ => simp [Gen.span] at hs; omega
    | gate3 _ => simp [Gen.span] at hs; omega
    | up h ih =>
      obtain ⟨a₁, b₁, -, rfl, rfl⟩ := span_up_eq h a b hs
      omega

/-- Generators on disjoint wires commute. -/
theorem comm_apart (hsc : ∀ c c' : Gate 0, c = c') :
    ∀ {n : ℕ} (g h : Gen Gate n), Gen.apart g h = true →
      Derivable (Lift R n) (FreeMonoid.of g * FreeMonoid.of h)
        (FreeMonoid.of h * FreeMonoid.of g)
  | n, g, h, hgh => by
    cases hsg : Gen.span g with
    | none => exact none_comm hsc g h hsg
    | some p =>
      cases hsh : Gen.span h with
      | none => exact (none_comm hsc h g hsh).symm
      | some q =>
        obtain ⟨a, b⟩ := p
        obtain ⟨c, d⟩ := q
        have hd : b ≤ c ∨ d ≤ a := by
          simpa [Gen.apart, hsg, hsh] using hgh
        cases g with
        | gate0 _ => simp [Gen.span] at hsg
        | gate1 x =>
          simp only [Gen.span, Option.some.injEq, Prod.mk.injEq] at hsg
          obtain ⟨rfl, rfl⟩ := hsg
          exact bottom_comm1 x h c d hsh (lo_of_apart hsh hd)
        | gate2 x =>
          simp only [Gen.span, Option.some.injEq, Prod.mk.injEq] at hsg
          obtain ⟨rfl, rfl⟩ := hsg
          exact bottom_comm2 x h c d hsh (lo_of_apart hsh hd)
        | gate3 x =>
          simp only [Gen.span, Option.some.injEq, Prod.mk.injEq] at hsg
          obtain ⟨rfl, rfl⟩ := hsg
          exact bottom_comm3 x h c d hsh (lo_of_apart hsh hd)
        | up g₁ =>
          cases h with
          | gate0 _ => simp [Gen.span] at hsh
          | gate1 y =>
            simp only [Gen.span, Option.some.injEq, Prod.mk.injEq] at hsh
            obtain ⟨rfl, rfl⟩ := hsh
            exact (bottom_comm1 y _ a b hsg (lo_of_apart hsg hd.symm)).symm
          | gate2 y =>
            simp only [Gen.span, Option.some.injEq, Prod.mk.injEq] at hsh
            obtain ⟨rfl, rfl⟩ := hsh
            exact (bottom_comm2 y _ a b hsg (lo_of_apart hsg hd.symm)).symm
          | gate3 y =>
            simp only [Gen.span, Option.some.injEq, Prod.mk.injEq] at hsh
            obtain ⟨rfl, rfl⟩ := hsh
            exact (bottom_comm3 y _ a b hsg (lo_of_apart hsg hd.symm)).symm
          | up h₁ =>
            obtain ⟨a₁, b₁, hg₁, rfl, rfl⟩ := span_up_eq g₁ a b hsg
            obtain ⟨c₁, d₁, hh₁, rfl, rfl⟩ := span_up_eq h₁ c d hsh
            have : Gen.apart g₁ h₁ = true := by
              simp only [Gen.apart, hg₁, hh₁, Bool.or_eq_true, decide_eq_true_eq]
              omega
            exact derivable_shift (comm_apart hsc g₁ h₁ this)

end Comm

end QCert.Minimality
