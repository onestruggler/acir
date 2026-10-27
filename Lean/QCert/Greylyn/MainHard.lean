/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: Subcases 4.3 and 4.4 of the Main Lemma

The one configuration of the basic edge `X_[a,a+1]` that the thesis treats
separately: the pivot column has the odd entries `α < a` as its first two
and `a + 1` is odd too.  With `n ≤ 4` (the only place the dimension is
used) this forces `n = 4`, `α = 0`, `a = 1`, pivot `3` and all four entries
odd (`square_X_hard`); so the edge is `X_[1,2]` and the syllables of `s`
and `r = X_[1,2] s` are `N = H_[0,1] ωᵐ_[0]` and `N' = H_[0,1] ω^φ_[0]`.

Subcase 4.4 reduces to Subcase 4.3 by diagonal phases.  Here the phases
are chosen once and for all so that the square closes exactly:
`E = ω^{e}_[0] ω^{e}_[1] ω^{f}_[2] ω^{g}_[3]` makes the four entries of the
numerator `≡ 1 (mod δ³)` after `N` (`e ≡ -h`, `e + m ≡ -ι`, `f ≡ -ℓ`,
`g ≡ -τ` modulo `4` for the residues `ι, h, ℓ, τ`), and the phases on the
side of `r` are those of `E` with the indices `1, 2` exchanged, which needs
`f + φ ≡ e + m (mod 8)`.  The thesis' phases (`-h, -h, -ℓ, -τ` and
`-ℓ, -ℓ, -h, -τ`) give exponents `m - h` and `φ - ℓ` on the first entry,
which agree modulo `4` but not always modulo `8` (residues `ι, h, ℓ = 1, 0,
3`: `ω³` against `ω⁷`), so its square does not always commute.  Then, with
the entries `1 + δ³ aᵢ` and `S = a₀ + a₁ + a₂ + a₃`:

* Subcase 4.3.1, `S ≡ 0 (mod δ²)`: (31), the path
  `H_[2,3] H_[0,2] H_[1,3] X_[1,2] H_[1,3] H_[0,2] H_[2,3]`;
* Subcase 4.3.2, `S ≡ δ (mod δ²)`: (32), the path
  `H_[2,3] H_[1,2] H_[0,3] X_[1,3] H_[0,3] H_[1,2] H_[2,3]`;
* Subcase 4.3.3, `S` odd: impossible by Lemma 39.

The square is assembled from its faces (`hard_alg`, with (31) or (32) as
`coreA`, `coreB`).  Every state on the path `G₀`, besides its two ends, has
a pivot column at exponent `k - 1`; the thesis checks the states `t'`,
`t''`, `q'`, `q''`, but not the two between the `H`'s of `H_[2,4] H_[1,3]`
(resp. `H_[1,4] H_[2,3]`), which are checked here too.  The first four
states are read off from the start of the path and the last four from its
end, backwards, each `H` being an involution (`allBelow_path`, `vside`).
-/
import QCert.Greylyn.MainH
import QCert.Greylyn.Technical

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

section

variable {n : ℕ}

theorem FirstTwo.below {w : Fin n → ZOmega} {x y : Fin n} (hf : FirstTwo w x y) :
    ∀ i, i < y → i ≠ x → ¬ IsOdd (w i) := by
  intro i hi hix
  rcases lt_trichotomy i x with h | h | h
  · exact hf.2.2.2.1 i h
  · exact absurd h hix
  · exact hf.2.2.2.2 i h hi

theorem FirstTwo.mk' {w : Fin n → ZOmega} {x y : Fin n} (hxy : x < y) (hx : IsOdd (w x))
    (hy : IsOdd (w y)) (h : ∀ i, i < y → i ≠ x → ¬ IsOdd (w i)) : FirstTwo w x y :=
  ⟨hxy, hx, hy, fun i hi => h i (hi.trans hxy) (ne_of_lt hi),
    fun i h1 h2 => h i h2 (ne_of_gt h1)⟩

theorem hasNum_Xswap {v : Fin n → ℂ} {k : ℕ} {u : Fin n → ZOmega} (h : HasNum v k u)
    {a b : Fin n} (hab : a ≠ b) :
    HasNum (twoLevel a b Xmat *ᵥ v) k (fun i => u (Equiv.swap a b i)) := by
  intro i
  rw [twoLevel_X_mulVec hab, Equiv.symm_swap]
  exact h _

end

/-! ### Words on four indices -/

theorem lt01 : (0 : Fin 4) < 1 := by decide
theorem lt02 : (0 : Fin 4) < 2 := by decide
theorem lt03 : (0 : Fin 4) < 3 := by decide
theorem lt12 : (1 : Fin 4) < 2 := by decide
theorem lt13 : (1 : Fin 4) < 3 := by decide
theorem lt23 : (2 : Fin 4) < 3 := by decide

/-- `ω^{a₀}_[0] ω^{a₁}_[1] ω^{a₂}_[2] ω^{a₃}_[3]`. -/
def Ph (a0 a1 a2 a3 : ℕ) : Word (Gen 4) := ω 0 ^ a0 * ω 1 ^ a1 * ω 2 ^ a2 * ω 3 ^ a3

/-- The path of Subcase 4.3.1. -/
def G0A : Word (Gen 4) :=
  H 2 3 lt23 * H 0 2 lt02 * H 1 3 lt13 * X 1 2 lt12 *
    H 1 3 lt13 * H 0 2 lt02 * H 2 3 lt23

/-- The path of Subcase 4.3.2. -/
def G0B : Word (Gen 4) :=
  H 2 3 lt23 * H 1 2 lt12 * H 0 3 lt03 * X 1 3 lt13 *
    H 0 3 lt03 * H 1 2 lt12 * H 2 3 lt23

/-- `ω^{a₀}_[0] ω^{a₁}_[1] ω^{a₂}_[2] ω^{a₃}_[3]` in `Pres 4`. -/
def Dω (a0 a1 a2 a3 : ℕ) : Pres 4 := gω 0 ^ a0 * gω 1 ^ a1 * gω 2 ^ a2 * gω 3 ^ a3

theorem cl_Ph (a0 a1 a2 a3 : ℕ) : cl (Ph a0 a1 a2 a3) = Dω a0 a1 a2 a3 := by
  simp [Ph, Dω, map_mul, map_pow, cl_ω]

theorem cωω {i j : Fin 4} (h : i ≠ j) (a b : ℕ) : Commute (gω i ^ a) (gω j ^ b) :=
  c_ωωpow h a b

theorem Dω_mul0 (a0 a1 a2 a3 c : ℕ) : Dω a0 a1 a2 a3 * gω 0 ^ c = Dω (a0 + c) a1 a2 a3 := by
  simp only [Dω, mul_assoc]
  rw [(cωω (by decide) a3 c).eq, (cωω (by decide) a2 c).left_comm,
    (cωω (by decide) a1 c).left_comm, ← mul_assoc (gω 0 ^ a0), ← pow_add]

theorem Dω_mul1 (a0 a1 a2 a3 c : ℕ) : Dω a0 a1 a2 a3 * gω 1 ^ c = Dω a0 (a1 + c) a2 a3 := by
  simp only [Dω, mul_assoc]
  rw [(cωω (by decide) a3 c).eq, (cωω (by decide) a2 c).left_comm,
    ← mul_assoc (gω 1 ^ a1), ← pow_add]

theorem Dω_mul2 (a0 a1 a2 a3 c : ℕ) : Dω a0 a1 a2 a3 * gω 2 ^ c = Dω a0 a1 (a2 + c) a3 := by
  simp only [Dω, mul_assoc]
  rw [(cωω (by decide) a3 c).eq, ← mul_assoc (gω 2 ^ a2), ← pow_add]

theorem Dω_mul3 (a0 a1 a2 a3 c : ℕ) : Dω a0 a1 a2 a3 * gω 3 ^ c = Dω a0 a1 a2 (a3 + c) := by
  simp only [Dω, mul_assoc]
  rw [← pow_add]

theorem Dω_mul_Dω (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) :
    Dω a0 a1 a2 a3 * Dω b0 b1 b2 b3 = Dω (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  show Dω a0 a1 a2 a3 * (gω 0 ^ b0 * gω 1 ^ b1 * gω 2 ^ b2 * gω 3 ^ b3) = _
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Dω_mul0, Dω_mul1, Dω_mul2, Dω_mul3]

theorem Dω_congr {a0 a1 a2 a3 b0 b1 b2 b3 : ℕ} (h0 : a0 % 8 = b0 % 8) (h1 : a1 % 8 = b1 % 8)
    (h2 : a2 % 8 = b2 % 8) (h3 : a3 % 8 = b3 % 8) : Dω a0 a1 a2 a3 = Dω b0 b1 b2 b3 := by
  simp only [Dω, gω_pow_congr _ h0, gω_pow_congr _ h1, gω_pow_congr _ h2, gω_pow_congr _ h3]

theorem Dω_zero : Dω 0 0 0 0 = 1 := by simp [Dω]

/-- `X_[1,2]` exchanges the phases on `1` and `2`. -/
theorem gX12_Dω (a0 a1 a2 a3 : ℕ) :
    gX 1 2 lt12 * Dω a0 a1 a2 a3 = Dω a0 a2 a1 a3 * gX 1 2 lt12 := by
  have s0 : SemiconjBy (gX 1 2 lt12) (gω 0 ^ a0) (gω 0 ^ a0) :=
    ((c_ωX (by decide) (by decide) (by decide)).pow_left a0).symm
  have s1 : SemiconjBy (gX 1 2 lt12) (gω 1 ^ a1) (gω 2 ^ a1) :=
    (s_Xωj (by decide)).pow_right a1
  have s2 : SemiconjBy (gX 1 2 lt12) (gω 2 ^ a2) (gω 1 ^ a2) :=
    (s_Xωk (by decide)).pow_right a2
  have s3 : SemiconjBy (gX 1 2 lt12) (gω 3 ^ a3) (gω 3 ^ a3) :=
    ((c_ωX (by decide) (by decide) (by decide)).pow_left a3).symm
  have := (((s0.mul_right s1).mul_right s2).mul_right s3).eq
  simp only [Dω]
  rw [this, mul_assoc (gω 0 ^ a0) (gω 2 ^ a1), (cωω (i := 2) (j := 1) (by decide) a1 a2).eq,
    ← mul_assoc]

/-- Phases equal on `0` and `1` commute with `H_[0,1]`. -/
theorem Dω_H01 (a a2 a3 : ℕ) :
    Dω a a a2 a3 * gH 0 1 lt01 = gH 0 1 lt01 * Dω a a a2 a3 := by
  have c01 : Commute (gω 0 ^ a * gω 1 ^ a) (gH 0 1 lt01) := c_ω2Hpow (by decide) a
  have c2 : Commute (gω 2 ^ a2) (gH 0 1 lt01) :=
    (c_ωH (by decide) (by decide) (by decide)).pow_left a2
  have c3 : Commute (gω 3 ^ a3) (gH 0 1 lt01) :=
    (c_ωH (by decide) (by decide) (by decide)).pow_left a3
  exact ((c01.mul_left c2).mul_left c3).eq

/-- `G₀ H_[0,1] ≈ H_[0,1] X_[1,2]` for the path of Subcase 4.3.1, from (31). -/
theorem coreA : cl G0A * gH 0 1 lt01 = gH 0 1 lt01 * gX 1 2 lt12 := by
  have h31 := e31 (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
  simp only [G0A, map_mul, cl_H, cl_X]
  have e : gH 2 3 lt23 * gH 0 2 lt02 * gH 1 3 lt13 * gX 1 2 lt12 *
      gH 1 3 lt13 * gH 0 2 lt02 * gH 2 3 lt23 =
      gH 2 3 lt23 * (gH 0 2 lt02 * gH 1 3 lt13 * gX 1 2 lt12 *
        gH 1 3 lt13 * gH 0 2 lt02) * gH 2 3 lt23 := by
    simp only [mul_assoc]
  rw [e, ← h31]
  have hsq : gH 2 3 lt23 * gH 2 3 lt23 = 1 := gH_sq _
  have hsq' : gH 0 1 lt01 * gH 0 1 lt01 = 1 := gH_sq _
  calc gH 2 3 lt23 * (gH 2 3 lt23 * gH 0 1 lt01 * gX 1 2 lt12 * gH 0 1 lt01 * gH 2 3 lt23) * gH 2 3 lt23 *
        gH 0 1 lt01
        = (gH 2 3 lt23 * gH 2 3 lt23) * gH 0 1 lt01 * gX 1 2 lt12 * gH 0 1 lt01 * (gH 2 3 lt23 * gH 2 3 lt23) *
          gH 0 1 lt01 := by simp only [mul_assoc]
    _ = gH 0 1 lt01 * gX 1 2 lt12 * (gH 0 1 lt01 * gH 0 1 lt01) := by
          rw [hsq, one_mul, mul_one]; simp only [mul_assoc]
    _ = gH 0 1 lt01 * gX 1 2 lt12 := by rw [hsq', mul_one]

/-- `G₀ H_[0,1] ≈ H_[0,1] X_[1,2]` for the path of Subcase 4.3.2, from (32). -/
theorem coreB : cl G0B * gH 0 1 lt01 = gH 0 1 lt01 * gX 1 2 lt12 := by
  have h32 := e32 (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
  simp only [G0B, map_mul, cl_H, cl_X]
  have e : gH 2 3 lt23 * gH 1 2 lt12 * gH 0 3 lt03 * gX 1 3 lt13 *
      gH 0 3 lt03 * gH 1 2 lt12 * gH 2 3 lt23 =
      gH 2 3 lt23 * (gH 1 2 lt12 * gH 0 3 lt03 * gX 1 3 lt13 *
        gH 0 3 lt03 * gH 1 2 lt12) * gH 2 3 lt23 := by
    simp only [mul_assoc]
  rw [e, ← h32]
  have hsq : gH 2 3 lt23 * gH 2 3 lt23 = 1 := gH_sq _
  have hsq' : gH 0 1 lt01 * gH 0 1 lt01 = 1 := gH_sq _
  calc gH 2 3 lt23 * (gH 2 3 lt23 * gH 0 1 lt01 * gX 1 2 lt12 * gH 0 1 lt01 * gH 2 3 lt23) * gH 2 3 lt23 *
        gH 0 1 lt01
        = (gH 2 3 lt23 * gH 2 3 lt23) * gH 0 1 lt01 * gX 1 2 lt12 * gH 0 1 lt01 * (gH 2 3 lt23 * gH 2 3 lt23) *
          gH 0 1 lt01 := by simp only [mul_assoc]
    _ = gH 0 1 lt01 * gX 1 2 lt12 * (gH 0 1 lt01 * gH 0 1 lt01) := by
          rw [hsq, one_mul, mul_one]; simp only [mul_assoc]
    _ = gH 0 1 lt01 * gX 1 2 lt12 := by rw [hsq', mul_one]

/-- The algebra of the square of Subcase 4.4: from the faces, `N' x ≈ G' N`
with `G' = Eᵣ⁻¹ G₀ E`. -/
theorem hard_alg {M : Type*} [Monoid M] {H X Om Op Es Ef Dr Er Di G0 : M}
    (F1 : Es * H = H * Es) (Fcore : G0 * H = H * X) (Fs : Es * Om = Ef)
    (F3 : X * Ef = Dr * X) (Fc : Dr = Er * Op) (F4 : Er * H = H * Er) (F5 : Di * Er = 1) :
    H * Op * X = Di * G0 * Es * (H * Om) := by
  calc H * Op * X = (Di * Er) * H * Op * X := by rw [F5, one_mul]
    _ = Di * (Er * H) * Op * X := by simp only [mul_assoc]
    _ = Di * H * (Er * Op) * X := by rw [F4]; simp only [mul_assoc]
    _ = Di * H * (X * Ef) := by rw [← Fc, F3]; simp only [mul_assoc]
    _ = Di * (H * X) * (Es * Om) := by rw [Fs]; simp only [mul_assoc]
    _ = Di * G0 * (H * Es) * Om := by rw [← Fcore]; simp only [mul_assoc]
    _ = Di * G0 * Es * (H * Om) := by rw [← F1]; simp only [mul_assoc]


/-- Half of the square: `G₀ E (H_[0,1] ω^m_[0]) ≈ H_[0,1] D X_[1,2]`. -/
theorem hard_half {M : Type*} [Monoid M] {H X Om Es Ef Dr G0 : M}
    (F1 : Es * H = H * Es) (Fcore : G0 * H = H * X) (Fs : Es * Om = Ef)
    (F3 : X * Ef = Dr * X) : G0 * Es * (H * Om) = H * Dr * X := by
  calc G0 * Es * (H * Om) = G0 * (Es * H) * Om := by simp only [mul_assoc]
    _ = (G0 * H) * (Es * Om) := by rw [F1]; simp only [mul_assoc]
    _ = H * (X * Ef) := by rw [Fcore, Fs]; simp only [mul_assoc]
    _ = H * Dr * X := by rw [F3]; simp only [mul_assoc]

/-! ### Matrices of words and levels along paths -/

theorem matOf_of_cl {m : ℕ} {w v : Word (Gen m)} (h : cl w = cl v) : matOf w = matOf v :=
  derivable_sound (sem := mat) (fun _ _ h => matOf_sound h) (derivable_iff.2 h)

theorem Hmat_invol {m : ℕ} {i j : Fin m} (h : i < j) (v : Fin m → ℂ) :
    twoLevel i j Hmat *ᵥ (twoLevel i j Hmat *ᵥ v) = v := by
  have e : matOf (H i j h * H i j h) = matOf (1 : Word (Gen m)) :=
    matOf_of_cl (by rw [map_mul, cl_H, gH_sq, map_one])
  calc twoLevel i j Hmat *ᵥ (twoLevel i j Hmat *ᵥ v) = matOf (H i j h * H i j h) *ᵥ v := by
        rw [matOf_mul_mulVec, matOf_H]
    _ = v := by rw [e, map_one, one_mulVec]

theorem allBelow_cons {m : ℕ} {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St m} {y : Gen m} {w : Word (Gen m)}
    (hw : AllBelow L t w) (hy : level (⟪FreeMonoid.of y * w⟫ * t) < L) :
    AllBelow L t (FreeMonoid.of y * w) := by
  refine AllBelow.mul hw (AllBelow.letter (hw 1 w (one_mul w).symm) ?_)
  rwa [map_mul, FreeMonoid.lift_eval_of, mul_assoc] at hy

theorem allL_Ph (a0 a1 a2 a3 : ℕ) :
    AllL (fun y => IsXω y ∧ ∀ i ∈ gidx y, i ≤ (3 : Fin 4)) (Ph a0 a1 a2 a3) := by
  have le3 : ∀ q : Fin 4, q ≤ 3 := by decide
  have h : ∀ j : Fin 4, AllL (fun y => IsXω y ∧ ∀ i ∈ gidx y, i ≤ (3 : Fin 4)) (ω j) :=
    fun j => AllL.of ⟨trivial, fun i _ => le3 i⟩
  exact ((((h 0).pow a0).mul ((h 1).pow a1)).mul ((h 2).pow a2)).mul ((h 3).pow a3)

/-- The paths of Subcases 4.3.1 and 4.3.2:
`H_[2,3] H_[i,j] H_[k,l] x H_[k,l] H_[i,j] H_[2,3]`. -/
def path (i j k l : Fin 4) (hij : i < j) (hkl : k < l) (x : Gen 4) : Word (Gen 4) :=
  H 2 3 lt23 * H i j hij * H k l hkl * FreeMonoid.of x * H k l hkl * H i j hij * H 2 3 lt23

theorem G0A_eq : G0A = path 0 2 1 3 lt02 lt13 (Gen.X 1 2 lt12) := rfl
theorem G0B_eq : G0B = path 1 2 0 3 lt12 lt03 (Gen.X 1 3 lt13) := rfl

/-- The levels along a path: its first four states are those along
`H_[k,l] H_[i,j] H_[2,3]` from `T`, its last four those along the same word
from the end `v₇` of the path (each `H` being an involution). -/
theorem allBelow_path {s : St 4} (hs : IsPivot s 3) {T : St 4} {i j k l : Fin 4} (hij : i < j)
    (hkl : k < l) (x : Gen 4) {v7 : Fin 4 → ℂ}
    (hc7 : matOf (path i j k l hij hkl x) *ᵥ col T 3 = v7)
    (h0 : prof (col T 3) < prof (col s 3))
    (h1 : prof (twoLevel 2 3 Hmat *ᵥ col T 3) < prof (col s 3))
    (h2 : prof (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ col T 3)) < prof (col s 3))
    (h3 : prof (twoLevel k l Hmat *ᵥ (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ col T 3))) <
      prof (col s 3))
    (h7 : prof v7 < prof (col s 3))
    (h6 : prof (twoLevel 2 3 Hmat *ᵥ v7) < prof (col s 3))
    (h5 : prof (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ v7)) < prof (col s 3))
    (h4 : prof (twoLevel k l Hmat *ᵥ (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ v7))) <
      prof (col s 3)) :
    AllBelow (level s) T (path i j k l hij hkl x) := by
  have le3 : ∀ q : Fin 4, q ≤ 3 := by decide
  have lv : ∀ w : Word (Gen 4), prof (matOf w *ᵥ col T 3) < prof (col s 3) →
      level (⟪w⟫ * T) < level s := fun w hw =>
    level_lt_of_cols hs (fun q hq => absurd hq (not_lt.2 (le3 q)))
      (Or.inr (by rw [col_mul, sm_lift]; exact hw))
  simp only [path, matOf_mul_mulVec, matOf_H] at hc7
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = matOf (FreeMonoid.of x) *ᵥ (twoLevel k l Hmat *ᵥ (twoLevel i j Hmat *ᵥ
      (twoLevel 2 3 Hmat *ᵥ col T 3))) := ⟨_, rfl⟩
  rw [← hQ] at hc7
  have e6 : twoLevel i j Hmat *ᵥ (twoLevel k l Hmat *ᵥ Q) = twoLevel 2 3 Hmat *ᵥ v7 := by
    rw [← hc7, Hmat_invol lt23]
  have e5 : twoLevel k l Hmat *ᵥ Q = twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ v7) := by
    rw [← e6, Hmat_invol hij]
  have e4 : Q = twoLevel k l Hmat *ᵥ (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ v7)) := by
    rw [← e5, Hmat_invol hkl]
  have e : path i j k l hij hkl x = H 2 3 lt23 * (H i j hij * (H k l hkl * (FreeMonoid.of x *
      (H k l hkl * (H i j hij * (H 2 3 lt23 * 1)))))) := by
    simp only [path, mul_assoc, mul_one]
  rw [e]
  refine allBelow_cons (allBelow_cons (allBelow_cons (allBelow_cons (allBelow_cons
    (allBelow_cons (allBelow_cons (AllBelow.one' ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · simpa using lv 1 (by simpa using h0)
  all_goals
    refine lv _ ?_
    simp only [matOf_mul_mulVec, matOf_H, map_one, one_mulVec]
  · exact h1
  · exact h2
  · exact h3
  · rw [← hQ, e4]; exact h4
  · rw [← hQ, e5]; exact h5
  · rw [← hQ, e6]; exact h6
  · rw [← hQ, hc7]; exact h7

/-! ### Numerators along the paths -/

/-- `D = 2/δ³ = δ u₂`. -/
def Dc : ZOmega := δz * u2

theorem δz_cube_Dc : δz ^ 3 * Dc = 1 + 1 := by rw [Dc, two_eq_δz_pow_four]; ring

theorem δz_sq_dvd_two_mul (x : ZOmega) : δz ^ 2 ∣ (1 + 1) * x :=
  ⟨δz ^ 2 * u2 * x, by rw [two_eq_δz_pow_four]; ring⟩

theorem δz_dvd_two_mul (x : ZOmega) : δz ∣ (1 + 1) * x :=
  ⟨δz ^ 3 * u2 * x, by rw [two_eq_δz_pow_four]; ring⟩

theorem δz_sq_dvd_Dc_sub : δz ^ 2 ∣ Dc - δz := by
  obtain ⟨q, hq⟩ := (dvd_δz_iff (u2 - 1)).2 (by
    have := isOdd_u2; unfold IsOdd at this ⊢
    simp only [a_sub, b_sub, c_sub, d_sub, a_one, b_one, c_one, d_one]; omega)
  exact ⟨q, by rw [Dc]; linear_combination δz * hq⟩

theorem δz_dvd_Dc : δz ∣ Dc := ⟨u2, rfl⟩

theorem not_δz_sq_dvd_δz : ¬ δz ^ 2 ∣ δz := by
  rw [δz_sq_dvd_iff]; decide

/-- `ηz` is a unit: `ηz ω⁷ (√2 - 1) = 1`. -/
theorem ηz_mul_inv : ηz * (ωz ^ 7 * (s2z - 1)) = 1 := by decide +kernel

theorem dvd_of_ηz_mul {x : ZOmega} {d : ZOmega} (h : d ∣ ηz * x) : d ∣ x := by
  have : x = (ωz ^ 7 * (s2z - 1)) * (ηz * x) := by
    rw [← mul_assoc, mul_comm (ωz ^ 7 * (s2z - 1)), ηz_mul_inv, one_mul]
  rw [this]; exact Dvd.dvd.mul_left h _

theorem isOdd_of_dvd_sub {x y : ZOmega} (hx : IsOdd x) (h : δz ∣ x - y) : IsOdd y := by
  by_contra hy
  have hy' := (dvd_δz_iff y).2 hy
  exact (dvd_δz_iff x).1 (by have := dvd_add h hy'; rwa [sub_add_cancel] at this) hx

theorem not_sq_dvd_of_odd {x : ZOmega} (hx : IsOdd x) : ¬ δz ^ 2 ∣ x := fun h =>
  (dvd_δz_iff x).1 (dvd_trans (dvd_pow_self δz two_ne_zero) h) hx

theorem eq_one_add_of_res {x : ZOmega} (hx : IsOdd x) (hr : res x = 0) :
    ∃ a, x = 1 + δz ^ 3 * a := by
  obtain ⟨q, hq⟩ := dvd_sub_ωz_pow_res hx
  rw [hr, pow_zero] at hq
  exact ⟨q, by linear_combination hq⟩

/-- A phase making an odd entry `≡ 1 (mod δ³)`. -/
theorem res_W {x : ZOmega} (hx : IsOdd x) {c : ℕ} (hc : (res x + c) % 4 = 0) :
    ∃ a, ωz ^ c * x = 1 + δz ^ 3 * a := by
  obtain ⟨h1, h2⟩ := res_ωz_pow_mul hx c
  exact eq_one_add_of_res h1 (h2.trans hc)

/-- The three classes of `S` modulo `δ²` that can occur: `0`, `δ`, odd. -/
theorem cls3 (S : ZOmega) : δz ^ 2 ∣ S ∨ δz ^ 2 ∣ S - δz ∨ IsOdd S := by
  rw [δz_sq_dvd_iff, δz_sq_dvd_iff]
  unfold IsOdd
  simp only [a_sub, b_sub, c_sub, d_sub]
  have : δz.a = 1 ∧ δz.b = 1 ∧ δz.c = 0 ∧ δz.d = 0 := ⟨rfl, rfl, rfl, rfl⟩
  omega

/-- The four `δ`-quotients after `H_[0,1]` and `H_[2,3]` (Subcase 4.3):
`D + a₀ + a₁, a₀ - a₁, D + a₂ + a₃, a₂ - a₃`. -/
def cvec (a : Fin 4 → ZOmega) : Fin 4 → ZOmega :=
  ![Dc + a 0 + a 1, a 0 - a 1, Dc + a 2 + a 3, a 2 - a 3]

theorem hasNum_Ph {v : Fin 4 → ℂ} {K : ℕ} {w : Fin 4 → ZOmega} (h : HasNum v K w)
    (a0 a1 a2 a3 : ℕ) :
    HasNum (matOf (Ph a0 a1 a2 a3) *ᵥ v) K (fun i => ωz ^ (![a0, a1, a2, a3] i) * w i) := by
  have h4 := hasNum_ω (hasNum_ω (hasNum_ω (hasNum_ω h 3 a3) 2 a2) 1 a1) 0 a0
  simp only [Ph, matOf_mul_mulVec, matOf_ωpow]
  intro i
  rw [h4 i]
  congr 1
  fin_cases i <;> simp

/-- `H_[0,1]` on a numerator with entries `1 + δ³ aᵢ`. -/
theorem hasNum_H01_res {v : Fin 4 → ℂ} {K : ℕ} {W a : Fin 4 → ZOmega} (h : HasNum v K W)
    (hW : ∀ i, W i = 1 + δz ^ 3 * a i) :
    HasNum (twoLevel 0 1 Hmat *ᵥ v) K (Function.update (Function.update W 0
      (ηz * δz * (Dc + a 0 + a 1))) 1 (ηz * δz * (a 0 - a 1))) :=
  hasNum_H_red h (a := 0) (b := 1) (by decide)
    (by rw [hW, hW]; linear_combination (-1 : ZOmega) * δz_cube_Dc)
    (by rw [hW, hW]; ring)

/-- After `H_[0,1]`, only the entries `2, 3` are odd. -/
theorem card_oddSet_H01 {W : Fin 4 → ZOmega} (x y : ZOmega) :
    (oddSet (Function.update (Function.update W 0 (ηz * δz * x)) 1 (ηz * δz * y))).card ≤ 2 := by
  have hsub : oddSet (Function.update (Function.update W 0 (ηz * δz * x)) 1 (ηz * δz * y)) ⊆
      {2, 3} := by
    intro i hi
    rw [mem_oddSet] at hi
    have key : ∀ i : Fin 4, i ∉ ({2, 3} : Finset (Fin 4)) → i = 0 ∨ i = 1 := by decide
    by_contra hni
    rcases key i hni with rfl | rfl
    · rw [upd2_fst (a := (0 : Fin 4)) (b := 1) (by decide)] at hi
      exact not_isOdd_ηz_δz_mul x hi
    · rw [upd2_snd] at hi
      exact not_isOdd_ηz_δz_mul y hi
  exact (Finset.card_le_card hsub).trans (by decide)

/-- `H_[2,3]` after `H_[0,1]`: the numerator `ηz cᵢ` at one exponent less. -/
theorem hasNum_H23 {v : Fin 4 → ℂ} {kk : ℕ} {W a : Fin 4 → ZOmega}
    (h : HasNum v (kk + 1) (Function.update (Function.update W 0
      (ηz * δz * (Dc + a 0 + a 1))) 1 (ηz * δz * (a 0 - a 1))))
    (hW2 : W 2 = 1 + δz ^ 3 * a 2) (hW3 : W 3 = 1 + δz ^ 3 * a 3) :
    HasNum (twoLevel 2 3 Hmat *ᵥ v) kk (fun i => ηz * cvec a i) := by
  have h2 := hasNum_H_red h (a := 2) (b := 3) (by decide) (d1 := Dc + a 2 + a 3)
    (d2 := a 2 - a 3)
    (by rw [upd2_other (a := 0) (b := 1) (c := 2) (by decide) (by decide),
          upd2_other (a := 0) (b := 1) (c := 3) (by decide) (by decide), hW2, hW3]
        linear_combination (-1 : ZOmega) * δz_cube_Dc)
    (by rw [upd2_other (a := 0) (b := 1) (c := 2) (by decide) (by decide),
          upd2_other (a := 0) (b := 1) (c := 3) (by decide) (by decide), hW2, hW3]
        ring)
  refine h2.pred _ fun i => ?_
  fin_cases i <;> simp [cvec] <;> ring

/-- The states along `H_[k,l] H_[i,j] H_[2,3]` from a column of the shape
reached after `H_[0,1]`: the first at exponent `k + 1` with two odd entries,
the others at exponent `k`, given the classes of `cᵢ ± cⱼ`, `c_k ± c_l`. -/
theorem vside {P : ℕ ×ₗ ℕ} {kk : ℕ} {v : Fin 4 → ℂ} {W a : Fin 4 → ZOmega}
    (hv : HasNum v (kk + 1) (Function.update (Function.update W 0
      (ηz * δz * (Dc + a 0 + a 1))) 1 (ηz * δz * (a 0 - a 1))))
    (hW2 : W 2 = 1 + δz ^ 3 * a 2) (hW3 : W 3 = 1 + δz ^ 3 * a 3)
    (hP2 : ∀ (v' : Fin 4 → ℂ) (w' : Fin 4 → ZOmega), HasNum v' (kk + 1) w' →
      (oddSet w').card ≤ 2 → prof v' < P)
    (hP1 : ∀ (v' : Fin 4 → ℂ) (w' : Fin 4 → ZOmega), HasNum v' kk w' → prof v' < P)
    {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i)
    (hlj : l ≠ j)
    (h1 : δz ^ 2 ∣ cvec a i + cvec a j) (h2 : δz ^ 2 ∣ cvec a i - cvec a j)
    (h3 : δz ^ 2 ∣ cvec a k + cvec a l) (h4 : δz ^ 2 ∣ cvec a k - cvec a l) :
    prof v < P ∧ prof (twoLevel 2 3 Hmat *ᵥ v) < P ∧
      prof (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ v)) < P ∧
      prof (twoLevel k l Hmat *ᵥ (twoLevel i j Hmat *ᵥ (twoLevel 2 3 Hmat *ᵥ v))) < P := by
  have s1 := hasNum_H23 hv hW2 hW3
  obtain ⟨σ1, hσ1⟩ := h1
  obtain ⟨σ2, hσ2⟩ := h2
  obtain ⟨σ3, hσ3⟩ := h3
  obtain ⟨σ4, hσ4⟩ := h4
  have s2 := hasNum_H_gen s1 hij 2 le_rfl (e1 := ηz * σ1) (e2 := ηz * σ2)
    (by show ηz * cvec a i + ηz * cvec a j = δz ^ 2 * (ηz * σ1)
        linear_combination ηz * hσ1)
    (by show ηz * cvec a i - ηz * cvec a j = δz ^ 2 * (ηz * σ2)
        linear_combination ηz * hσ2)
  have s3 := hasNum_H_gen s2 hkl 2 le_rfl (e1 := ηz * σ3) (e2 := ηz * σ4)
    (by rw [upd2_other hki hkj, upd2_other hli hlj]
        show δz ^ (2 - 2) * (ηz * cvec a k) + δz ^ (2 - 2) * (ηz * cvec a l) =
          δz ^ 2 * (ηz * σ3)
        rw [Nat.sub_self, pow_zero]
        linear_combination ηz * hσ3)
    (by rw [upd2_other hki hkj, upd2_other hli hlj]
        show δz ^ (2 - 2) * (ηz * cvec a k) - δz ^ (2 - 2) * (ηz * cvec a l) =
          δz ^ 2 * (ηz * σ4)
        rw [Nat.sub_self, pow_zero]
        linear_combination ηz * hσ4)
  exact ⟨hP2 v _ hv (card_oddSet_H01 _ _), hP1 _ _ s1, hP1 _ _ s2, hP1 _ _ s3⟩

/-! ### The classes of `S` -/

/-- Subcase 4.3.1, `S ≡ 0 (mod δ²)`: the pairs `0, 2` and `1, 3`. -/
theorem caseA_divs {a : Fin 4 → ZOmega} (hS : δz ^ 2 ∣ a 0 + a 1 + a 2 + a 3) :
    δz ^ 2 ∣ cvec a 0 + cvec a 2 ∧ δz ^ 2 ∣ cvec a 0 - cvec a 2 ∧
      δz ^ 2 ∣ cvec a 1 + cvec a 3 ∧ δz ^ 2 ∣ cvec a 1 - cvec a 3 := by
  have t := δz_sq_dvd_two_mul
  refine ⟨?_, ?_, ?_, ?_⟩
  · show δz ^ 2 ∣ (Dc + a 0 + a 1) + (Dc + a 2 + a 3)
    rw [show (Dc + a 0 + a 1) + (Dc + a 2 + a 3) = (a 0 + a 1 + a 2 + a 3) + (1 + 1) * Dc by
      ring]
    exact dvd_add hS (t _)
  · show δz ^ 2 ∣ (Dc + a 0 + a 1) - (Dc + a 2 + a 3)
    rw [show (Dc + a 0 + a 1) - (Dc + a 2 + a 3) = (a 0 + a 1 + a 2 + a 3) -
      (1 + 1) * (a 2 + a 3) by ring]
    exact dvd_sub hS (t _)
  · show δz ^ 2 ∣ (a 0 - a 1) + (a 2 - a 3)
    rw [show (a 0 - a 1) + (a 2 - a 3) = (a 0 + a 1 + a 2 + a 3) - (1 + 1) * (a 1 + a 3) by
      ring]
    exact dvd_sub hS (t _)
  · show δz ^ 2 ∣ (a 0 - a 1) - (a 2 - a 3)
    rw [show (a 0 - a 1) - (a 2 - a 3) = (a 0 + a 1 + a 2 + a 3) - (1 + 1) * (a 1 + a 2) by
      ring]
    exact dvd_sub hS (t _)

/-- Subcase 4.3.2, `S ≡ δ (mod δ²)`: the pairs `1, 2` and `0, 3`. -/
theorem caseB_divs {a : Fin 4 → ZOmega} (hS : δz ^ 2 ∣ a 0 + a 1 + a 2 + a 3 - δz) :
    δz ^ 2 ∣ cvec a 1 + cvec a 2 ∧ δz ^ 2 ∣ cvec a 1 - cvec a 2 ∧
      δz ^ 2 ∣ cvec a 0 + cvec a 3 ∧ δz ^ 2 ∣ cvec a 0 - cvec a 3 := by
  have t := δz_sq_dvd_two_mul
  have hD := δz_sq_dvd_Dc_sub
  refine ⟨?_, ?_, ?_, ?_⟩
  · show δz ^ 2 ∣ (a 0 - a 1) + (Dc + a 2 + a 3)
    rw [show (a 0 - a 1) + (Dc + a 2 + a 3) = (a 0 + a 1 + a 2 + a 3 - δz) + (Dc - δz) +
      (1 + 1) * (δz - a 1) by ring]
    exact dvd_add (dvd_add hS hD) (t _)
  · show δz ^ 2 ∣ (a 0 - a 1) - (Dc + a 2 + a 3)
    rw [show (a 0 - a 1) - (Dc + a 2 + a 3) = (a 0 + a 1 + a 2 + a 3 - δz) - (Dc - δz) -
      (1 + 1) * (a 1 + a 2 + a 3) by ring]
    exact dvd_sub (dvd_sub hS hD) (t _)
  · show δz ^ 2 ∣ (Dc + a 0 + a 1) + (a 2 - a 3)
    rw [show (Dc + a 0 + a 1) + (a 2 - a 3) = (a 0 + a 1 + a 2 + a 3 - δz) + (Dc - δz) +
      (1 + 1) * (δz - a 3) by ring]
    exact dvd_add (dvd_add hS hD) (t _)
  · show δz ^ 2 ∣ (Dc + a 0 + a 1) - (a 2 - a 3)
    rw [show (Dc + a 0 + a 1) - (a 2 - a 3) = (a 0 + a 1 + a 2 + a 3 - δz) + (Dc - δz) +
      (1 + 1) * (δz - a 2) by ring]
    exact dvd_add (dvd_add hS hD) (t _)

/-- Subcase 4.3.3, `S` odd: the four entries `ηz cᵢ` lie in four different
classes modulo `δ²`, which Lemma 39 rules out. -/
theorem cvec_classes {a : Fin 4 → ZOmega} (hS : IsOdd (a 0 + a 1 + a 2 + a 3)) :
    ∀ i j : Fin 4, i ≠ j → ¬ δz ^ 2 ∣ ηz * cvec a i - ηz * cvec a j := by
  have nD : ∀ y : ZOmega, ¬ δz ^ 2 ∣ Dc + (1 + 1) * y := by
    intro y h
    apply not_δz_sq_dvd_δz
    have := dvd_sub (dvd_sub h (δz_sq_dvd_two_mul y)) δz_sq_dvd_Dc_sub
    rwa [show Dc + (1 + 1) * y - (1 + 1) * y - (Dc - δz) = δz by ring] at this
  have nO : ∀ z : ZOmega, δz ∣ z → ¬ δz ^ 2 ∣ (a 0 + a 1 + a 2 + a 3) - z := fun z hz =>
    not_sq_dvd_of_odd (isOdd_of_dvd_sub hS (by rw [sub_sub_cancel]; exact hz))
  have n01 : ¬ δz ^ 2 ∣ cvec a 0 - cvec a 1 := by
    show ¬ δz ^ 2 ∣ (Dc + a 0 + a 1) - (a 0 - a 1)
    rw [show (Dc + a 0 + a 1) - (a 0 - a 1) = Dc + (1 + 1) * a 1 by ring]; exact nD _
  have n23 : ¬ δz ^ 2 ∣ cvec a 2 - cvec a 3 := by
    show ¬ δz ^ 2 ∣ (Dc + a 2 + a 3) - (a 2 - a 3)
    rw [show (Dc + a 2 + a 3) - (a 2 - a 3) = Dc + (1 + 1) * a 3 by ring]; exact nD _
  have n02 : ¬ δz ^ 2 ∣ cvec a 0 - cvec a 2 := by
    show ¬ δz ^ 2 ∣ (Dc + a 0 + a 1) - (Dc + a 2 + a 3)
    rw [show (Dc + a 0 + a 1) - (Dc + a 2 + a 3) = (a 0 + a 1 + a 2 + a 3) -
      (1 + 1) * (a 2 + a 3) by ring]
    exact nO _ (δz_dvd_two_mul _)
  have n03 : ¬ δz ^ 2 ∣ cvec a 0 - cvec a 3 := by
    show ¬ δz ^ 2 ∣ (Dc + a 0 + a 1) - (a 2 - a 3)
    rw [show (Dc + a 0 + a 1) - (a 2 - a 3) = (a 0 + a 1 + a 2 + a 3) -
      ((1 + 1) * a 2 - Dc) by ring]
    exact nO _ (dvd_sub (δz_dvd_two_mul _) δz_dvd_Dc)
  have n12 : ¬ δz ^ 2 ∣ cvec a 1 - cvec a 2 := by
    show ¬ δz ^ 2 ∣ (a 0 - a 1) - (Dc + a 2 + a 3)
    rw [show (a 0 - a 1) - (Dc + a 2 + a 3) = (a 0 + a 1 + a 2 + a 3) -
      ((1 + 1) * (a 1 + a 2 + a 3) + Dc) by ring]
    exact nO _ (dvd_add (δz_dvd_two_mul _) δz_dvd_Dc)
  have n13 : ¬ δz ^ 2 ∣ cvec a 1 - cvec a 3 := by
    show ¬ δz ^ 2 ∣ (a 0 - a 1) - (a 2 - a 3)
    rw [show (a 0 - a 1) - (a 2 - a 3) = (a 0 + a 1 + a 2 + a 3) -
      (1 + 1) * (a 1 + a 2) by ring]
    exact nO _ (δz_dvd_two_mul _)
  have key : ∀ i j : Fin 4, i < j → ¬ δz ^ 2 ∣ cvec a i - cvec a j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact n01 | exact n02 | exact n03 | exact n12 | exact n13 | exact n23
  intro i j hij hd
  rw [← mul_sub] at hd
  have hd' := dvd_of_ηz_mul hd
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hd'
  · exact key j i h (dvd_sub_comm.1 hd')

/-! ### The square -/

set_option maxHeartbeats 4000000 in
/-- Subcases 4.3 and 4.4 on four indices, all entries of the pivot column
odd: the square closes with `G' = E_r⁻¹ G₀ E` (`hard_alg`), `G₀` the path
(31) or (32) according to the class of `S` (Subcases 4.3.1, 4.3.2;
Subcase 4.3.3 is impossible by Lemma 39). -/
theorem square_hard4 {s : St 4} (hp : IsPivot s 3) {k : ℕ} {u : Fin 4 → ZOmega}
    (hu : HasNum (col s 3) (k + 1) u) (hl : lde (col s 3) = k + 1) (hodd : ∀ i, IsOdd (u i)) :
    Square s (Gen.X 1 2 lt12) := by
  have hk : 0 < lde (col s 3) := by omega
  have le3 : ∀ q : Fin 4, q ≤ 3 := by decide
  have vac : ∀ (t : St 4) (q : Fin 4), 3 < q → col t q = ev q :=
    fun _ q hq => absurd hq (not_lt.2 (le3 q))
  -- the profiles below that of `s`
  have hcard : (oddSet u).card = 4 := by
    rw [Finset.eq_univ_of_forall fun i => mem_oddSet.2 (hodd i), Finset.card_univ,
      Fintype.card_fin]
  have hP2 : ∀ (v' : Fin 4 → ℂ) (w' : Fin 4 → ZOmega), HasNum v' (k + 1) w' →
      (oddSet w').card ≤ 2 → prof v' < prof (col s 3) := fun v' w' hv' hc =>
    prof_lt_of hu hl (Nat.succ_pos k) hv' (by omega)
  have hP1 : ∀ (v' : Fin 4 → ℂ) (w' : Fin 4 → ZOmega), HasNum v' k w' →
      prof v' < prof (col s 3) := by
    intro v' w' hv'
    have := lde_le hv'
    rw [prof, prof]
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (show lde v' < lde (col s 3) by omega))
  -- the syllables of `s` and `r = X_[1,2] s`
  have below01 : ∀ i : Fin 4, i < 1 → i ≠ 0 → False := by decide
  have hf : FirstTwo u 0 1 :=
    FirstTwo.mk' lt01 (hodd 0) (hodd 1) fun i hi hi0 => (below01 i hi hi0).elim
  have hsyl := syl_H_of' hp hu (Nat.succ_pos k) hf lt01
  have sw0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have sw1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have sw2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have sw3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have hcolr : col (sem 4 (Gen.X 1 2 lt12) * s) 3 = twoLevel 1 2 Xmat *ᵥ col s 3 := by
    rw [col_mul, sm_sem]; rfl
  have hur : HasNum (col (sem 4 (Gen.X 1 2 lt12) * s) 3) (k + 1)
      (fun i => u (Equiv.swap 1 2 i)) := by
    rw [hcolr]; exact hasNum_Xswap hu (by decide)
  have hodd' : ∀ i, IsOdd (u (Equiv.swap 1 2 i)) := fun i => hodd _
  have hr : IsPivot (sem 4 (Gen.X 1 2 lt12) * s) 3 :=
    isPivot_mul hp (fun i _ => le3 i) (by
      rw [← sm_sem, ← col_mul]
      exact ne_ev_of_hasNum hur (Nat.succ_pos k) ⟨0, hodd' 0⟩ 3)
  have hfr : FirstTwo (fun i => u (Equiv.swap 1 2 i)) 0 1 :=
    FirstTwo.mk' lt01 (hodd' 0) (hodd' 1) fun i hi hi0 => (below01 i hi hi0).elim
  have hsylr := syl_H_of' hr hur (Nat.succ_pos k) hfr lt01
  simp only [sw0, sw1] at hsylr
  -- the phases
  obtain ⟨m, hm⟩ : ∃ m, zexp (u 0) (u 1) = m := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, zexp (u 0) (u 2) = φ := ⟨_, rfl⟩
  rw [hm] at hsyl
  rw [hφ] at hsylr
  have r0 := res_lt (u 0)
  have r1 := res_lt (u 1)
  have r2 := res_lt (u 2)
  have r3 := res_lt (u 3)
  unfold zexp at hm hφ
  obtain ⟨e', he'⟩ : ∃ e, (4 - res (u 1)) % 4 = e := ⟨_, rfl⟩
  obtain ⟨f3, hf3⟩ : ∃ f, (4 - res (u 3)) % 4 = f := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f, (e' + m + 8 - φ) % 8 = f := ⟨_, rfl⟩
  obtain ⟨b0, hb0⟩ := res_W (hodd 0) (c := e' + m) (by omega)
  obtain ⟨b1, hb1⟩ := res_W (hodd 1) (c := e') (by omega)
  obtain ⟨b2, hb2⟩ := res_W (hodd 2) (c := f2) (by omega)
  obtain ⟨b3, hb3⟩ := res_W (hodd 3) (c := f3) (by omega)
  -- the faces in `Pres 4`
  have F1 := Dω_H01 e' f2 f3
  have Fs := Dω_mul0 e' e' f2 f3 m
  have F3 := gX12_Dω (e' + m) e' f2 f3
  have hDr : Dω (e' + m) f2 e' f3 = Dω (f2 + φ) f2 e' f3 := Dω_congr (by omega) rfl rfl rfl
  have Fc : Dω (e' + m) f2 e' f3 = Dω f2 f2 e' f3 * gω 0 ^ φ :=
    hDr.trans (Dω_mul0 _ _ _ _ _).symm
  have F4 := Dω_H01 f2 e' f3
  have F5 : Dω (8 - f2) (8 - f2) (8 - e') (8 - f3) * Dω f2 f2 e' f3 = 1 := by
    rw [Dω_mul_Dω, ← Dω_zero]; exact Dω_congr (by omega) (by omega) (by omega) (by omega)
  -- the column after `E N` (`t₀` side)
  have hW : ∀ i, ωz ^ (![e' + m, e', f2, f3] i) * u i = 1 + δz ^ 3 * ![b0, b1, b2, b3] i := by
    intro i; fin_cases i
    · exact hb0
    · exact hb1
    · exact hb2
    · exact hb3
  have hclT0 : cl (Ph e' e' f2 f3 * (H 0 1 lt01 * ω 0 ^ m)) =
      cl (H 0 1 lt01 * Ph (e' + m) e' f2 f3) := by
    simp only [map_mul, map_pow, cl_Ph, cl_H, cl_ω]
    rw [← mul_assoc, F1, mul_assoc, Fs]
  have hT0col : col (⟪Ph e' e' f2 f3⟫ * (⟪syl s⟫ * s)) 3 =
      twoLevel 0 1 Hmat *ᵥ (matOf (Ph (e' + m) e' f2 f3) *ᵥ col s 3) := by
    rw [col_mul, col_mul, sm_lift, sm_lift, ← matOf_mul_mulVec, hsyl, matOf_of_cl hclT0,
      matOf_mul_mulVec, matOf_H]
  have hT0 := hasNum_H01_res (hasNum_Ph hu (e' + m) e' f2 f3) hW
  rw [← hT0col] at hT0
  -- the column after `E_r N'` (`q` side)
  have hWr : ∀ i, ωz ^ (![f2 + φ, f2, e', f3] i) * u (Equiv.swap 1 2 i) =
      1 + δz ^ 3 * ![b0, b2, b1, b3] i := by
    intro i; fin_cases i
    · show ωz ^ (f2 + φ) * u (Equiv.swap 1 2 0) = 1 + δz ^ 3 * b0
      rw [sw0, ωz_pow_mod (f2 + φ), show (f2 + φ) % 8 = (e' + m) % 8 by omega, ← ωz_pow_mod]
      exact hb0
    · show ωz ^ f2 * u (Equiv.swap 1 2 1) = 1 + δz ^ 3 * b2
      rw [sw1]; exact hb2
    · show ωz ^ e' * u (Equiv.swap 1 2 2) = 1 + δz ^ 3 * b1
      rw [sw2]; exact hb1
    · show ωz ^ f3 * u (Equiv.swap 1 2 3) = 1 + δz ^ 3 * b3
      rw [sw3]; exact hb3
  have hvr := hasNum_H01_res (hasNum_Ph hur (f2 + φ) f2 e' f3) hWr
  -- the path, by the class of `S` (Subcases 4.3.1–4.3.3)
  obtain ⟨i, j, k', l, hij, hkl, x, hcore, hki, hkj, hli, hlj, d1, d2, d3, d4, q1, q2, q3, q4⟩ :
      ∃ (i j k' l : Fin 4) (hij : i < j) (hkl : k' < l) (x : Gen 4),
        cl (path i j k' l hij hkl x) * gH 0 1 lt01 = gH 0 1 lt01 * gX 1 2 lt12 ∧
        k' ≠ i ∧ k' ≠ j ∧ l ≠ i ∧ l ≠ j ∧
        δz ^ 2 ∣ cvec ![b0, b1, b2, b3] i + cvec ![b0, b1, b2, b3] j ∧
        δz ^ 2 ∣ cvec ![b0, b1, b2, b3] i - cvec ![b0, b1, b2, b3] j ∧
        δz ^ 2 ∣ cvec ![b0, b1, b2, b3] k' + cvec ![b0, b1, b2, b3] l ∧
        δz ^ 2 ∣ cvec ![b0, b1, b2, b3] k' - cvec ![b0, b1, b2, b3] l ∧
        δz ^ 2 ∣ cvec ![b0, b2, b1, b3] i + cvec ![b0, b2, b1, b3] j ∧
        δz ^ 2 ∣ cvec ![b0, b2, b1, b3] i - cvec ![b0, b2, b1, b3] j ∧
        δz ^ 2 ∣ cvec ![b0, b2, b1, b3] k' + cvec ![b0, b2, b1, b3] l ∧
        δz ^ 2 ∣ cvec ![b0, b2, b1, b3] k' - cvec ![b0, b2, b1, b3] l := by
    rcases cls3 (b0 + b1 + b2 + b3) with hA | hB | hC
    · -- Subcase 4.3.1: the path (31)
      obtain ⟨d1, d2, d3, d4⟩ := caseA_divs (a := ![b0, b1, b2, b3]) hA
      obtain ⟨q1, q2, q3, q4⟩ := caseA_divs (a := ![b0, b2, b1, b3]) (by
        show δz ^ 2 ∣ b0 + b2 + b1 + b3
        rw [show b0 + b2 + b1 + b3 = b0 + b1 + b2 + b3 by ring]; exact hA)
      exact ⟨0, 2, 1, 3, lt02, lt13, Gen.X 1 2 lt12, coreA, by decide, by decide, by decide,
        by decide, d1, d2, d3, d4, q1, q2, q3, q4⟩
    · -- Subcase 4.3.2: the path (32)
      obtain ⟨d1, d2, d3, d4⟩ := caseB_divs (a := ![b0, b1, b2, b3]) hB
      obtain ⟨q1, q2, q3, q4⟩ := caseB_divs (a := ![b0, b2, b1, b3]) (by
        show δz ^ 2 ∣ b0 + b2 + b1 + b3 - δz
        rw [show b0 + b2 + b1 + b3 = b0 + b1 + b2 + b3 by ring]; exact hB)
      exact ⟨1, 2, 0, 3, lt12, lt03, Gen.X 1 3 lt13, coreB, by decide, by decide, by decide,
        by decide, d1, d2, d3, d4, q1, q2, q3, q4⟩
    · -- Subcase 4.3.3: impossible (Lemma 39)
      exfalso
      have hS1 : HasNum (col (sem 4 (Gen.H 2 3 lt23) * (⟪Ph e' e' f2 f3⟫ * (⟪syl s⟫ * s))) 3)
          k (fun i => ηz * cvec ![b0, b1, b2, b3] i) := by
        rw [col_mul, sm_sem]; exact hasNum_H23 hT0 (hW 2) (hW 3)
      exact no_four_classes (col_unit _ 3) hS1 (cvec_classes hC)
  -- the end of the path
  have hclr : cl (path i j k' l hij hkl x * Ph e' e' f2 f3 * (H 0 1 lt01 * ω 0 ^ m)) =
      cl (H 0 1 lt01 * Ph (f2 + φ) f2 e' f3 * X 1 2 lt12) := by
    simp only [map_mul, map_pow, cl_Ph, cl_H, cl_ω, cl_X]
    rw [hard_half F1 hcore Fs F3, hDr]
  have hvr_eq : matOf (path i j k' l hij hkl x) *ᵥ col (⟪Ph e' e' f2 f3⟫ * (⟪syl s⟫ * s)) 3 =
      twoLevel 0 1 Hmat *ᵥ (matOf (Ph (f2 + φ) f2 e' f3) *ᵥ
        col (sem 4 (Gen.X 1 2 lt12) * s) 3) := by
    rw [hcolr, col_mul, col_mul, sm_lift, sm_lift, hsyl, ← matOf_mul_mulVec,
      ← matOf_mul_mulVec, matOf_of_cl hclr, matOf_mul_mulVec, matOf_mul_mulVec, matOf_H,
      matOf_X]
  obtain ⟨h0, h1, h2, h3⟩ := vside hT0 (hW 2) (hW 3) hP2 hP1 hij.ne hkl.ne hki hkj hli hlj
    d1 d2 d3 d4
  obtain ⟨h7, h6, h5, h4⟩ := vside hvr (hWr 2) (hWr 3) hP2 hP1 hij.ne hkl.ne hki hkj hli hlj
    q1 q2 q3 q4
  refine sq_gen hr.ne_one hsylr
    (G' := Ph (8 - f2) (8 - f2) (8 - e') (8 - f3) * path i j k' l hij hkl x *
      Ph e' e' f2 f3) ?_ ?_
  · rw [hsyl, derivable_iff]
    simp only [map_mul, map_pow, cl_Ph, cl_H, cl_ω, cl_X]
    exact hard_alg F1 hcore Fs F3 Fc F4 F5
  · refine AllBelow.mul (allBelow_B hp (vac _) (t_below hp hk).2 (allL_Ph _ _ _ _)) ?_
    refine AllBelow.mul (allBelow_path hp hij hkl x hvr_eq h0 h1 h2 h3 h7 h6 h5 h4) ?_
    refine allBelow_B hp (vac _) ?_ (allL_Ph _ _ _ _)
    rw [col_mul, sm_lift, hvr_eq]
    exact h7

section

variable {n : ℕ}

/-- Subcases 4.3 and 4.4: the pivot column has the odd entries `α < a` as
its first two and `b = a + 1` odd.  With `n ≤ 4` this is `n = 4`,
`α = 0`, `a = 1`, `b = 2`, pivot `3`, all four entries odd. -/
theorem square_X_hard (hn : n ≤ 4) {s : St n} (_hs : s ≠ 1) {a b : Fin n} (hab : a < b)
    (hb : (b : ℕ) = a + 1) {p : Fin n} (hp : IsPivot s p) (hbp : b ≤ p) {u : Fin n → ZOmega}
    (hu : HasNum (col s p) (lde (col s p)) u) (hk : 0 < lde (col s p)) {α : Fin n}
    (hf : FirstTwo u α a) (hob : IsOdd (u b)) : Square s (Gen.X a b hab) := by
  have hev : Even (oddSet u).card := even_card_odd (col_unit s p) hu hk
  have hsub : ({α, a, b} : Finset (Fin n)) ⊆ oddSet u := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact mem_oddSet.2 hf.2.1
    · exact mem_oddSet.2 hf.2.2.1
    · exact mem_oddSet.2 hob
  have h3 : ({α, a, b} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.2 ⟨α, a, b, ne_of_lt hf.1, ne_of_lt (hf.1.trans hab), ne_of_lt hab, rfl⟩
  have hle : (oddSet u).card ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hge := Finset.card_le_card hsub
  obtain ⟨r, hr⟩ := hev
  obtain rfl : n = 4 := by omega
  have h4 : (oddSet u).card = 4 := by omega
  have hall : ∀ i, IsOdd (u i) := fun i => mem_oddSet.1 (by
    rw [Finset.eq_univ_of_card (oddSet u) (by rw [h4, Fintype.card_fin])]; exact Finset.mem_univ i)
  have hα : α = 0 := by
    by_contra h
    have key : ∀ x : Fin 4, x ≠ 0 → (0 : Fin 4) < x := by decide
    exact hf.2.2.2.1 0 (key α h) (hall 0)
  subst hα
  have ha : a = 1 := by
    by_contra h
    have key : ∀ x : Fin 4, 0 < x → x ≠ 1 → (0 : Fin 4) < 1 ∧ (1 : Fin 4) < x := by decide
    obtain ⟨h1, h2⟩ := key a hf.1 h
    exact hf.2.2.2.2 1 h1 h2 (hall 1)
  subst ha
  have hb2 : b = 2 := Fin.ext (by rw [hb]; rfl)
  subst hb2
  have hp3 : p = 3 := by
    by_contra h
    have key : ∀ x : Fin 4, 2 ≤ x → x ≠ 3 → x < 3 := by decide
    have h0 := hasNum_zero_of_entry hp hu (key p hbp h)
    have h3' := hall 3
    rw [h0] at h3'
    exact not_isOdd_zero h3'
  subst hp3
  obtain ⟨k, hk'⟩ : ∃ k, lde (col s 3) = k + 1 := ⟨lde (col s 3) - 1, by omega⟩
  rw [hk'] at hu
  exact square_hard4 hp hu hk' hall

end

end

end QCert.Greylyn
