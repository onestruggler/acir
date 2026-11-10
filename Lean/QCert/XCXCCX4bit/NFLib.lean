/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemmas for the block normal form: subsets, their partition lists, and signs

Translation of `NFLib.agda`.  A subset `S` of `n` states (a predicate) gives
the list of its states in order followed by the others (`ts S`, from
`part`).  That list is distinct (`ts_distinct`); its `k`-th entry is in `S`
exactly when `k` is below the size of `S` (`nth_ts`, the Agda's `‼-ts`); and
the size of a subset is invariant under a permutation of the states
(`weight_perm`).  `frameL xs` is the frame of a list of states, `ε` when
they are not distinct (`frameL_act`).  Signs: a lifted permutation and a
conjugate have the sign of the permutation (`sign_liftN`, `sign_by_liftN`,
`sign_sandwich`); these are stated at a variable width.

**Deviation from the Agda.**  The Agda's `xs ‼ k ≡ just x` is
`xs[k]? = some x`, its `k <ᵇ m` is `decide (k < m)`, and its `Distinct` is
`List.Nodup`; so its decision procedures `avoid?`, `distinct?` and their
completeness (`avoid?-complete`, `distinct?-complete`, `fr`) are Lean's
`Decidable` instances, and `frameL xs = if xs.Nodup then frame xs else 1`.
`‼-total` returns the entry as a subtype (`nth_total`).  `weight_perm` is
the invariance of a Finset sum under a permutation (`Equiv.sum_comp`) and
`sign_liftN` Mathlib's `Equiv.Perm.sign_extendDomain`, where the Agda uses
its own `sum-permute` and `sign-lift₀`.
-/
import QCert.XCXCCX4bit.Coxeter
import QCert.XCXCCX4bit.Lib.Alternating
import Mathlib.Algebra.BigOperators.Fin

namespace QCert.XCXCCX4bit.NFLib

open Symmetric Coxeter Alternating

variable {n m : ℕ}

/-! ## The partition list of a subset -/

/-- One more state below: in `S` it heads the first list, otherwise the
second. -/
def step : Bool → List (Fin n) × List (Fin n) → List (Fin (n + 1)) × List (Fin (n + 1))
  | true, (a, b) => (0 :: a.map Fin.succ, b.map Fin.succ)
  | false, (a, b) => (a.map Fin.succ, 0 :: b.map Fin.succ)

/-- The states of `S` in order, and the others in order. -/
def part : {n : ℕ} → (Fin n → Bool) → List (Fin n) × List (Fin n)
  | 0, _ => ([], [])
  | _ + 1, S => step (S 0) (part fun i => S i.succ)

/-- The states of `S` in order followed by the others. -/
def ts (S : Fin n → Bool) : List (Fin n) := (part S).1 ++ (part S).2

/-- The number of states of `S`. -/
def weight (S : Fin n → Bool) : ℕ := (part S).1.length

theorem part_cong {S S' : Fin n → Bool} (e : ∀ i, S i = S' i) : part S = part S' := by
  rw [funext e]

theorem ts_cong {S S' : Fin n → Bool} (e : ∀ i, S i = S' i) : ts S = ts S' := by
  rw [funext e]

theorem step_length (b : Bool) (p : List (Fin n) × List (Fin n)) :
    (step b p).1.length + (step b p).2.length = p.1.length + p.2.length + 1 := by
  cases b <;> simp [step] <;> omega

theorem part_length : ∀ {n : ℕ} (S : Fin n → Bool), (part S).1.length + (part S).2.length = n
  | 0, _ => rfl
  | n + 1, S => by rw [part, step_length, part_length]

theorem ts_length (S : Fin n → Bool) : (ts S).length = n := by
  rw [ts, List.length_append, part_length]

/-! ## Entries of the lists -/

theorem mem_part₁ : ∀ {n : ℕ} (S : Fin n → Bool) (x : Fin n), x ∈ (part S).1 ↔ S x = true
  | 0, _, x => x.elim0
  | n + 1, S, x => by
    have ih := mem_part₁ (fun i => S i.succ)
    rw [part]
    rcases h0 : S 0 with _ | _ <;> refine Fin.cases ?_ (fun y => ?_) x <;>
      simp [step, h0, ih, Fin.succ_ne_zero]

theorem mem_part₂ : ∀ {n : ℕ} (S : Fin n → Bool) (x : Fin n), x ∈ (part S).2 ↔ S x = false
  | 0, _, x => x.elim0
  | n + 1, S, x => by
    have ih := mem_part₂ (fun i => S i.succ)
    rw [part]
    rcases h0 : S 0 with _ | _ <;> refine Fin.cases ?_ (fun y => ?_) x <;>
      simp [step, h0, ih, Fin.succ_ne_zero]

/-- An entry of the first list is in `S` (the Agda's `‼-in₁`). -/
theorem nth_in₁ (S : Fin n → Bool) (k : ℕ) {x : Fin n} (h : (part S).1[k]? = some x) :
    S x = true :=
  (mem_part₁ S x).1 (List.mem_of_getElem? h)

/-- An entry of the second list is not (the Agda's `‼-in₂`). -/
theorem nth_in₂ (S : Fin n → Bool) (k : ℕ) {x : Fin n} (h : (part S).2[k]? = some x) :
    S x = false :=
  (mem_part₂ S x).1 (List.mem_of_getElem? h)

/-- An entry of a concatenation (the Agda's `‼-++`). -/
theorem nth_append {A : Type*} (xs ys : List A) (k : ℕ) {x : A} (h : (xs ++ ys)[k]? = some x) :
    (k < xs.length ∧ xs[k]? = some x) ∨ (xs.length ≤ k ∧ ys[k - xs.length]? = some x) := by
  by_cases hk : k < xs.length
  · exact Or.inl ⟨hk, by rwa [List.getElem?_append_left hk] at h⟩
  · exact Or.inr ⟨by omega, by rwa [List.getElem?_append_right (by omega)] at h⟩

/-- Every index below the length has an entry (the Agda's `‼-total`). -/
def nth_total {A : Type*} (xs : List A) (k : ℕ) (h : k < xs.length) : {x : A // xs[k]? = some x} :=
  ⟨xs[k], List.getElem?_eq_getElem h⟩

/-- The `k`-th entry of `ts S` is in `S` exactly when `k` is below the
weight (the Agda's `‼-ts`). -/
theorem nth_ts (S : Fin n → Bool) (k : ℕ) {x : Fin n} (h : (ts S)[k]? = some x) :
    S x = decide (k < weight S) := by
  rcases nth_append _ _ k h with ⟨lt, h₁⟩ | ⟨ge, h₂⟩
  · rw [nth_in₁ S k h₁]; simp [weight, lt]
  · rw [nth_in₂ S _ h₂]; simp [weight]; omega

/-! ## The partition list is distinct -/

theorem part_nodup₁ : ∀ {n : ℕ} (S : Fin n → Bool), (part S).1.Nodup
  | 0, _ => List.nodup_nil
  | n + 1, S => by
    have ih := part_nodup₁ (fun i => S i.succ)
    rw [part]
    cases S 0 <;> simp only [step]
    · exact ih.map (Fin.succ_injective _)
    · exact List.nodup_cons.2 ⟨by simp [Fin.succ_ne_zero], ih.map (Fin.succ_injective _)⟩

theorem part_nodup₂ : ∀ {n : ℕ} (S : Fin n → Bool), (part S).2.Nodup
  | 0, _ => List.nodup_nil
  | n + 1, S => by
    have ih := part_nodup₂ (fun i => S i.succ)
    rw [part]
    cases S 0 <;> simp only [step]
    · exact List.nodup_cons.2 ⟨by simp [Fin.succ_ne_zero], ih.map (Fin.succ_injective _)⟩
    · exact ih.map (Fin.succ_injective _)

/-- The Agda's `ts-distinct`. -/
theorem ts_distinct (S : Fin n → Bool) : Distinct (ts S) := by
  refine List.nodup_append.2 ⟨part_nodup₁ S, part_nodup₂ S, ?_⟩
  intro x hx y hy e
  subst e
  rw [mem_part₁] at hx; rw [mem_part₂] at hy
  rw [hx] at hy; cases hy

/-! ## The frame of a list -/

/-- The frame of a list of states (`ε` when they are not distinct): it sends
the state `i` to the `i`-th entry. -/
def frameL (xs : List (Fin n)) : Word (SG n) := if xs.Nodup then frame xs else 1

theorem frameL_act (xs : List (Fin n)) (d : Distinct xs) (i x : Fin n) (h : xs[i.1]? = some x) :
    act (frameL xs) i = x := by
  rw [frameL, if_pos d]; exact frame_act xs d i x h

/-! ## The size of a subset is invariant under permutations -/

theorem weight_sum : ∀ {n : ℕ} (S : Fin n → Bool), weight S = ∑ i, if S i then 1 else 0
  | 0, _ => rfl
  | n + 1, S => by
    rw [Fin.sum_univ_succ, ← weight_sum (fun i => S i.succ)]
    unfold weight; rw [part]
    cases S 0 <;> simp [step]
    all_goals omega

/-- The Agda's `weight-perm`. -/
theorem weight_perm (π : Equiv.Perm (Fin n)) (S : Fin n → Bool) :
    weight (fun i => S (π i)) = weight S := by
  rw [weight_sum, weight_sum]
  exact Equiv.sum_comp π (fun i => if S i then 1 else 0)

/-! ## Signs -/

/-- The Agda's `sign-liftN`. -/
theorem sign_liftN (j : ℕ) (π : Equiv.Perm (Fin m)) : sign (liftN j π) = sign π := by
  unfold sign; rw [liftN_eq_extendDomain, Equiv.Perm.sign_extendDomain]

/-- A permutation that agrees with a lifted one has its sign (the Agda's
`sign-by-liftN`). -/
theorem sign_by_liftN (j : ℕ) (π : Equiv.Perm (Fin (j + m))) (ρ : Equiv.Perm (Fin m))
    (e : ∀ i, π i = liftN j ρ i) : sign π = sign ρ := by
  rw [sign_cong e, sign_liftN]

/-- A permutation between two copies of another has its sign (the Agda's
`sign-sandwich`; its `ρ ∘ₚ (π ∘ₚ ρ)` is `ρ.trans (π.trans ρ)`). -/
theorem sign_sandwich (ρ π : Equiv.Perm (Fin n)) : sign (ρ.trans (π.trans ρ)) = sign π := by
  rw [sign_comp, sign_comp]
  cases sign ρ <;> cases sign π <;> rfl

end QCert.XCXCCX4bit.NFLib
