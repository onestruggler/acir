/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of the three-qudit rules (C13)–(C15)

On three qudits the swaps, `CZ` and `CX` of (C13)–(C15) are monomial
operators: permutations of the digits `(t₀, t₁, t₂)` (wire 0 at the
bottom) with phases `ψ(t₁ t₀)`, `ψ(t₂ t₁)`. Each rule is then an equality
of permutations and of phases (Lemma A.27).
-/
import QCert.QuditClifford.Rules

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

theorem sem_bot2 (c : Circ 2) :
    ((sem p 3 (bot2 c) : unitaryGroup (State p 3) ℂ) : Op ℂ p 3) =
      onBottom (n := 1) ((sem p 2 c : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) :=
  congrArg Subtype.val ((gateSem p).sem_pad 1 c)

omit hp in
theorem state3_ext {s t : State p 3} (h0 : s 0 = t 0) (h1 : s 1 = t 1) (h2 : s 2 = t 2) :
    s = t := by
  funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

omit hp in
theorem split21_fst (t : State p 3) : (split p 2 1 t).1 = fun _ => t 0 := by
  funext i; rw [Subsingleton.elim i 0]; rfl

omit hp in
theorem split21_snd (t : State p 3) : (split p 2 1 t).2 = ![t 1, t 2] := by
  funext i; fin_cases i <;> rfl

omit hp in
theorem split12_fst (t : State p 3) : (split p 1 2 t).1 = ![t 0, t 1] := by
  funext i; fin_cases i <;> rfl

omit hp in
theorem split12_snd (t : State p 3) : (split p 1 2 t).2 = fun _ => t 2 := by
  funext i; rw [Subsingleton.elim i 0]; rfl

omit hp in
theorem split21_symm (a : State p 1) (b : State p 2) :
    (split p 2 1).symm (a, b) = ![a 0, b 0, b 1] := by
  funext i; fin_cases i <;> rfl

omit hp in
theorem split12_symm (a : State p 2) (b : State p 1) :
    (split p 1 2).symm (a, b) = ![a 0, a 1, b 0] := by
  funext i; fin_cases i <;> rfl

omit hp in
/-- A two-qudit monomial operator on the top two of three wires. -/
theorem onTop_mono3 (σ : State p 2 → State p 2) (φ : State p 2 → ℂ) :
    onTop 1 (mono p σ φ) = mono p (fun t => ![t 0, σ ![t 1, t 2] 0, σ ![t 1, t 2] 1])
      fun t => φ ![t 1, t 2] := by
  rw [onTop_mono]
  apply mono_ext p
  · intro t; rw [split21_symm, split21_fst, split21_snd]
  · intro t; rw [split21_snd]

omit hp in
/-- A two-qudit monomial operator on the bottom two of three wires. -/
theorem onBottom_mono3 (σ : State p 2 → State p 2) (φ : State p 2 → ℂ) :
    onBottom (n := 1) (mono p σ φ) = mono p (fun t => ![σ ![t 0, t 1] 0, σ ![t 0, t 1] 1, t 2])
      fun t => φ ![t 0, t 1] := by
  rw [onBottom_mono]
  apply mono_ext p
  · intro t; rw [split12_symm, split12_fst, split12_snd]
  · intro t; rw [split12_fst]

theorem sem_SWAP₁₂ (hp2 : p ≠ 2) :
    ((sem p 3 (SWAP₁₂ p) : unitaryGroup (State p 3) ℂ) : Op ℂ p 3) =
      mono p (fun t => ![t 0, t 2, t 1]) fun _ => 1 := by
  rw [SWAP₁₂, sem_top, sem_SWAP p hp2, onTop_mono3]; rfl

theorem sem_SWAP₀₁ (hp2 : p ≠ 2) :
    ((sem p 3 (SWAP₀₁ p) : unitaryGroup (State p 3) ℂ) : Op ℂ p 3) =
      mono p (fun t => ![t 1, t 0, t 2]) fun _ => 1 := by
  rw [SWAP₀₁, sem_bot2, sem_SWAP p hp2, onBottom_mono3]; rfl

theorem sem_CZ₀₁ : ((sem p 3 CZ₀₁ : unitaryGroup (State p 3) ℂ) : Op ℂ p 3) =
    mono p id fun t => ψ p (z p (t 1) * z p (t 0)) := by
  rw [CZ₀₁, sem_bot2, sem_CZ, CZop_mono, onBottom_mono3]
  apply mono_ext p
  · intro t; exact state3_ext p rfl rfl rfl
  · intro t; rfl

theorem sem_CZ₁₂ : ((sem p 3 CZ₁₂ : unitaryGroup (State p 3) ℂ) : Op ℂ p 3) =
    mono p id fun t => ψ p (z p (t 2) * z p (t 1)) := by
  rw [CZ₁₂, sem_top, sem_CZ, CZop_mono, onTop_mono3]
  apply mono_ext p
  · intro t; exact state3_ext p rfl rfl rfl
  · intro t; rfl

theorem sem_CX₂₁ (hp2 : p ≠ 2) : ((sem p 3 CX₂₁ : unitaryGroup (State p 3) ℂ) : Op ℂ p 3) =
    mono p (fun t => ![t 0, t 1 + t 2, t 2]) fun _ => 1 := by
  rw [CX₂₁, sem_top, sem_CX p hp2, onTop_mono3]; rfl

/-- (C13) The braid relation. -/
theorem sound_C13 (hp2 : p ≠ 2) :
    sem p 3 (SWAP₁₂ p ⨾ SWAP₀₁ p ⨾ SWAP₁₂ p) = sem p 3 (SWAP₀₁ p ⨾ SWAP₁₂ p ⨾ SWAP₀₁ p) := by
  apply Subtype.ext
  simp only [seq_def, map_mul, Submonoid.coe_mul, sem_SWAP₁₂ p hp2, sem_SWAP₀₁ p hp2, mono_mul]
  apply mono_ext p
  · intro t; rfl
  · intro t; ring

/-- (C14) `CZ` on the bottom wires passes the two swaps to the top wires. -/
theorem sound_C14 (hp2 : p ≠ 2) :
    sem p 3 (CZ₀₁ ⨾ SWAP₁₂ p ⨾ SWAP₀₁ p) = sem p 3 (SWAP₁₂ p ⨾ SWAP₀₁ p ⨾ CZ₁₂) := by
  apply Subtype.ext
  simp only [seq_def, map_mul, Submonoid.coe_mul, sem_SWAP₁₂ p hp2, sem_SWAP₀₁ p hp2, sem_CZ₀₁,
    sem_CZ₁₂, mono_mul]
  apply mono_ext p
  · intro t; rfl
  · intro t; simp only [Function.comp_apply, one_mul, mul_one]; rfl

/-- (C15) `CX` from the top wire to the middle wire against `CZ` on the bottom
wires: the remote `CZ` makes up the difference. -/
theorem sound_C15 (hp2 : p ≠ 2) :
    sem p 3 (CX₂₁ ⨾ CZ₀₁) = sem p 3 (CZ₀₁ ⨾ CX₂₁ ⨾ CZ₀₂ p) := by
  apply Subtype.ext
  simp only [CZ₀₂, seq_def, map_mul, Submonoid.coe_mul, sem_SWAP₀₁ p hp2,
    sem_CZ₀₁, sem_CZ₁₂, sem_CX₂₁ p hp2, mono_mul]
  apply mono_ext p
  · intro t; rfl
  · intro t
    simp only [Function.comp_apply, id, one_mul, mul_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [← ψ_add, z_add]; congr 1; ring

end

end QCert.QuditClifford
