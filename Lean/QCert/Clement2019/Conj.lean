/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Conjugation by a transposition, and (20), (21) at every placement

From relations (1)–(19) (`ConjLemmas.lean`, on at most four concrete
indices), conjugating by `X[i,j]` renames `i` and `j` in every generator
(`conj_gen`), hence in every word (`conj_word`), as soon as there is a third
index.  So `Rel` is invariant under every permutation of the indices
(`rel_perm`, by induction on a product of transpositions): Clément's (20)
and (21), stated at the first indices, hold at every injective placement,
and the theory `RelK true` of `RelK.lean` is contained in `Rel` (`relK_rel`).
-/
import QCert.Clement2019.ConjLemmas
import QCert.HadamardPi.Soundness
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fintype

namespace QCert.Clement2019

open FreeMonoid

variable {n : ℕ}

/-- A conjugation lemma on concrete indices, moved to `f`. -/
theorem conj_case {m : ℕ} {L : List (Gen m)} {r : Gen m}
    (h : Derivable (RelK false) (ofList L) (ofList [r])) (f : Fin m → Fin n)
    (hf : Function.Injective f) {i j : Fin n} (hij : i ≠ j) {g g' : Gen n}
    (hL : L.map (Gen.map f hf) = [.X i j hij, g, .X i j hij]) (hr : r.map f hf = g') :
    Derivable (RelK false) (X_[i,j] * of g * X_[i,j]) (of g') := by
  have := derC_map f hf h
  rw [hL, List.map_cons, List.map_nil, hr] at this
  exact this

/-- Conjugation by `X[i,j]` exchanges `i` and `j` in a generator (given a third index `o`). -/
theorem conj_gen {i j o : Fin n} (hij : i ≠ j) (hoi : o ≠ i) (hoj : o ≠ j) (g : Gen n) :
    Derivable (RelK false) (X_[i,j] * of g * X_[i,j])
      (of (g.map (Equiv.swap i j) (Equiv.swap i j).injective)) := by
  cases g with
  | Z l =>
    by_cases hli : l = i
    · subst hli
      exact conj_case cj_z0 ![l, j] (by vec_inj) hij rfl (by simp [Gen.map])
    by_cases hlj : l = j
    · subst hlj
      exact conj_case cj_z1 ![i, l] (by vec_inj) hij rfl (by simp [Gen.map])
    · exact conj_case cj_z2 ![i, j, l] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hli hlj])
  | X k l hkl =>
    by_cases hki : k = i
    · subst hki
      by_cases hlj : l = j
      · subst hlj
        exact conj_case cj_x01 ![k, l, o] (by vec_inj) hij rfl (by simp [Gen.map])
      · have hlk : l ≠ k := Ne.symm hkl
        exact conj_case cj_x02 ![k, j, l] (by vec_inj) hij rfl
          (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hlk hlj])
    by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli
        exact conj_case cj_x10 ![l, k, o] (by vec_inj) hij rfl (by simp [Gen.map])
      · have hlk : l ≠ k := Ne.symm hkl
        exact conj_case cj_x12 ![i, k, l] (by vec_inj) hij rfl
          (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hli hlk])
    by_cases hli : l = i
    · subst hli
      exact conj_case cj_x20 ![l, j, k] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hki hkj])
    by_cases hlj : l = j
    · subst hlj
      exact conj_case cj_x21 ![i, l, k] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hki hkj])
    · exact conj_case cj_x23 ![i, j, k, l] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hki hkj,
          Equiv.swap_apply_of_ne_of_ne hli hlj])
  | H k l hkl =>
    by_cases hki : k = i
    · subst hki
      by_cases hlj : l = j
      · subst hlj
        exact conj_case cj_h01 ![k, l, o] (by vec_inj) hij rfl (by simp [Gen.map])
      · have hlk : l ≠ k := Ne.symm hkl
        exact conj_case cj_h02 ![k, j, l] (by vec_inj) hij rfl
          (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hlk hlj])
    by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli
        exact conj_case cj_h10 ![l, k, o] (by vec_inj) hij rfl (by simp [Gen.map])
      · have hlk : l ≠ k := Ne.symm hkl
        exact conj_case cj_h12 ![i, k, l] (by vec_inj) hij rfl
          (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hli hlk])
    by_cases hli : l = i
    · subst hli
      exact conj_case cj_h20 ![l, j, k] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hki hkj])
    by_cases hlj : l = j
    · subst hlj
      exact conj_case cj_h21 ![i, l, k] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hki hkj])
    · exact conj_case cj_h23 ![i, j, k, l] (by vec_inj) hij rfl
        (by simp [Gen.map, Equiv.swap_apply_of_ne_of_ne hki hkj,
          Equiv.swap_apply_of_ne_of_ne hli hlj])

theorem ins_mid {full : Bool} {a b c : Word (Gen n)} (hc : Derivable (RelK full) c 1) :
    Derivable (RelK full) (a * c * b) (a * b) := by
  simpa using ((Derivable.refl a).mul hc).mul (Derivable.refl b)

/-- Conjugation by `X[i,j]` exchanges `i` and `j` in a word (given a third index `o`). -/
theorem conj_word {i j o : Fin n} (hij : i ≠ j) (hoi : o ≠ i) (hoj : o ≠ j) (w : Word (Gen n)) :
    Derivable (RelK false) (X_[i,j] * w * X_[i,j])
      (wmapC (Equiv.swap i j) (Equiv.swap i j).injective w) := by
  have hxx : Derivable (RelK false) (X_[i,j] * X_[i,j]) 1 := Derivable.of (RelK.r3 hij)
  induction w using FreeMonoid.inductionOn' with
  | one => simpa using hxx
  | mul_of g w ih =>
    have h1 : Derivable (RelK false) (X_[i,j] * (of g * w) * X_[i,j])
        ((X_[i,j] * of g * X_[i,j]) * (X_[i,j] * w * X_[i,j])) := by
      rw [show X_[i,j] * (of g * w) * X_[i,j] = (X_[i,j] * of g) * (w * X_[i,j]) by
          simp only [mul_assoc],
        show (X_[i,j] * of g * X_[i,j]) * (X_[i,j] * w * X_[i,j]) =
          (X_[i,j] * of g) * (X_[i,j] * X_[i,j]) * (w * X_[i,j]) by simp only [mul_assoc]]
      exact (ins_mid hxx).symm
    rw [map_mul]
    exact h1.trans ((conj_gen hij hoi hoj g).mul ih)

/-- A third index, when `n ≥ 3`. -/
theorem exists_third (hn : 3 ≤ n) (i j : Fin n) : ∃ o : Fin n, o ≠ i ∧ o ≠ j := by
  by_contra hc
  push Not at hc
  have h0 := hc ⟨0, by omega⟩
  have h1 := hc ⟨1, by omega⟩
  have h2 := hc ⟨2, by omega⟩
  by_cases a0 : (⟨0, by omega⟩ : Fin n) = i <;> by_cases a1 : (⟨1, by omega⟩ : Fin n) = i <;>
    by_cases a2 : (⟨2, by omega⟩ : Fin n) = i <;>
    simp_all [Fin.ext_iff] <;> omega

theorem wmapC_congr {m : ℕ} {f g : Fin m → Fin n} (e : f = g) (hf : Function.Injective f)
    (hg : Function.Injective g) (w : Word (Gen m)) : wmapC f hf w = wmapC g hg w := by
  subst e; rfl

/-- `Rel` is invariant under every permutation of the indices, when `n ≥ 3`. -/
theorem rel_perm (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) {w v : Word (Gen n)}
    (h : Derivable Rel w v) : Derivable Rel (wmapC σ σ.injective w) (wmapC σ σ.injective v) := by
  revert w v
  refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ {w v : Word (Gen n)},
    Derivable Rel w v → Derivable Rel (wmapC σ σ.injective w) (wmapC σ σ.injective v)) σ ?_ ?_
  · intro w v h
    rw [wmapC_congr (Equiv.Perm.coe_one) _ Function.injective_id,
      wmapC_congr (Equiv.Perm.coe_one) _ Function.injective_id, wmapC_id, wmapC_id]
    exact h
  · intro f x y hxy ih w v h
    obtain ⟨o, hox, hoy⟩ := exists_third hn x y
    have e : ∀ u : Word (Gen n), wmapC (Equiv.swap x y * f) (Equiv.swap x y * f).injective u =
        wmapC (Equiv.swap x y) (Equiv.swap x y).injective (wmapC f f.injective u) := by
      intro u
      rw [wmapC_comp]
      exact wmapC_congr (Equiv.Perm.coe_mul _ _) _ _ u
    rw [e, e]
    have hc := fun u => relK_false_rel (conj_word hxy hox hoy u)
    exact (hc _).symm.trans (((Derivable.refl _).mul (ih h)).mul (Derivable.refl _) |>.trans
      (hc _))

/-- The first `k` indices. -/
def std {k : ℕ} (h : k ≤ n) : Fin k → Fin n := Fin.castLE h

theorem std_injective {k : ℕ} (h : k ≤ n) : Function.Injective (std h) := Fin.castLE_injective h

/-- `RelK true` is contained in `Rel`: (20) and (21) hold at every placement. -/
theorem relK_rel {full : Bool} {w v : Word (Gen n)} (h : Derivable (RelK full) w v) :
    Derivable Rel w v := by
  have : conGen (RelK full (n := n)) ≤ conGen (Rel (n := n)) := by
    refine Con.conGen_le fun x y hxy => ?_
    cases hxy with
    | r20 hb f hf =>
      have h4 : 4 ≤ n := by simpa using Fintype.card_le_of_injective f hf
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (std h4) f (std_injective h4) hf
      have h0 : Derivable Rel (ofList (l20L (std h4) (std_injective h4)))
          (ofList (l20R (std h4) (std_injective h4))) := Derivable.of (Rel.r20 h4)
      have := rel_perm (by omega) σ h0
      rw [wmapC_ofList, wmapC_ofList, (l20_map _ _ _ _).1, (l20_map _ _ _ _).2,
        (l20_congr (show ⇑σ ∘ std h4 = f from funext hσ) _ hf).1,
        (l20_congr (show ⇑σ ∘ std h4 = f from funext hσ) _ hf).2] at this
      exact this
    | r21 hb f hf =>
      have h6 : 6 ≤ n := by simpa using Fintype.card_le_of_injective f hf
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (std h6) f (std_injective h6) hf
      have h0 : Derivable Rel (ofList (l21L (std h6) (std_injective h6)))
          (ofList (l21R (std h6) (std_injective h6))) := Derivable.of (Rel.r21 h6)
      have := rel_perm (by omega) σ h0
      rw [wmapC_ofList, wmapC_ofList, (l21_map _ _ _ _).1, (l21_map _ _ _ _).2,
        (l21_congr (show ⇑σ ∘ std h6 = f from funext hσ) _ hf).1,
        (l21_congr (show ⇑σ ∘ std h6 = f from funext hσ) _ hf).2] at this
      exact this
    | r1 j => exact Derivable.of (Rel.r1 j)
    | r2 h => exact Derivable.of (Rel.r2 h)
    | r3 h => exact Derivable.of (Rel.r3 h)
    | r4 h => exact Derivable.of (Rel.r4 h)
    | r5 h1 h2 h3 => exact Derivable.of (Rel.r5 h1 h2 h3)
    | r6 h1 h2 h3 => exact Derivable.of (Rel.r6 h1 h2 h3)
    | r7 h1 h2 h3 h4 h5 h6 => exact Derivable.of (Rel.r7 h1 h2 h3 h4 h5 h6)
    | r8 h1 h2 h3 h4 h5 h6 => exact Derivable.of (Rel.r8 h1 h2 h3 h4 h5 h6)
    | r9 h1 h2 h3 h4 h5 h6 => exact Derivable.of (Rel.r9 h1 h2 h3 h4 h5 h6)
    | r10 h => exact Derivable.of (Rel.r10 h)
    | r11 h => exact Derivable.of (Rel.r11 h)
    | r12 h1 h2 h3 => exact Derivable.of (Rel.r12 h1 h2 h3)
    | r13 h1 h2 h3 => exact Derivable.of (Rel.r13 h1 h2 h3)
    | r14 h1 h2 h3 => exact Derivable.of (Rel.r14 h1 h2 h3)
    | r15 h1 h2 h3 => exact Derivable.of (Rel.r15 h1 h2 h3)
    | r16 h => exact Derivable.of (Rel.r16 h)
    | r17 h => exact Derivable.of (Rel.r17 h)
    | r18 h => exact Derivable.of (Rel.r18 h)
    | r19 h1 h2 h3 h4 h5 => exact Derivable.of (Rel.r19 h1 h2 h3 h4 h5)
  exact this h

end QCert.Clement2019
