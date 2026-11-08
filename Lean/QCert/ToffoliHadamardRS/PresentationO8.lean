/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: Theorem 5.2

Translation of `PresentationO8.agda`.  Theorem 5.2 of Amy, Ross and Wesley,
with `r_K`: the circuits over `Σ₁` modulo `R₁⁺ = R₀ ∪ R₈₄ ∪ {r_K}` present
`O(8, 𝔻)`.

* the semantics is a homomorphism and respects `R₁⁺` (`SoundnessH`);
* it is one-to-one on circuits modulo `R₁⁺` (`Completeness`, with the
  identities of `Derived`);
* it is onto: an orthogonal matrix is the value of a word over Li, Ross and
  Selinger's generators, and the decoding of that word has the same value
  (`dec_sem`).

`dec_sem` goes, as in the Agda, along Li, Ross and Selinger's reduction of
a generator to a basic one by adjacent transpositions; the Agda's
`Conjugation.decompose` (one step at a time) is the Lean development's
`conjForm_gen` (Lemma A.19's decomposition `g ≈ P g₀ P⁻¹` at once).
-/
import QCert.ToffoliHadamardRS.Derived
import QCert.ToffoliHadamardRS.DecMatrices
import QCert.LiRossSelinger.Decomp

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen sem IsBasic conjForm_gen isBasic_of_adjLe)

/-! ## Completeness -/

theorem complete1 {w v : Word G₁} (h : semO w = semO v) : Derivable R1plus w v :=
  Complete.complete derived h

/-! ## The decoding of a generator has its value -/

theorem basic : ∀ g : Gen 8, IsBasic g → semO (dec g) = sem 8 g
  | .neg ⟨a, ha⟩, h => by
    simp only [IsBasic] at h; subst h
    exact dM0
  | .x ⟨a, ha⟩ ⟨b, hb⟩ p, h => by
    simp only [IsBasic] at h; subst h
    have : a < 7 := by omega
    interval_cases a
    · exact dX01
    · exact dX12
    · exact dX23
    · exact dX34
    · exact dX45
    · exact dX56
    · exact dX67
  | .k ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ p q r, h => by
    simp only [IsBasic] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact dK0123

theorem dec_sem_basic (L : List (Gen 8)) (hL : ∀ x ∈ L, IsBasic x) :
    semO (decW (FreeMonoid.ofList L)) = FreeMonoid.lift (sem 8) (FreeMonoid.ofList L) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [FreeMonoid.ofList_cons, map_mul, map_mul, map_mul, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, basic x (hL x (by simp)),
      ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))]

theorem dec_sem (g : Gen 8) : semO (dec g) = sem 8 g := by
  obtain ⟨P, g₀, hP, hb, hd⟩ := conjForm_gen g
  have hL : ∀ x ∈ P ++ [g₀] ++ P.reverse, IsBasic x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton, List.mem_reverse] at hx
    rcases hx with (hx | rfl) | hx
    · exact isBasic_of_adjLe (hP x hx)
    · exact hb
    · exact isBasic_of_adjLe (hP x hx)
  calc semO (dec g) = semO (decW (FreeMonoid.of g)) := by rw [FreeMonoid.lift_eval_of]
    _ = semO (decW (FreeMonoid.ofList (P ++ [g₀] ++ P.reverse))) :=
        sound1plus_der (dec_cong Toffoli.coxeter1 hd)
    _ = FreeMonoid.lift (sem 8) (FreeMonoid.ofList (P ++ [g₀] ++ P.reverse)) :=
        dec_sem_basic _ hL
    _ = FreeMonoid.lift (sem 8) (FreeMonoid.of g) := (derivable_sound LiRossSelinger.sound hd).symm
    _ = sem 8 g := FreeMonoid.lift_eval_of _ _

theorem dec_semW (u : Word (Gen 8)) : semO (decW u) = FreeMonoid.lift (sem 8) u := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g u ih =>
    rw [map_mul, map_mul, map_mul, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of, dec_sem, ih]

/-! ## The presentation -/

theorem grouplike1 : Grouplike R1plus := fun g => ⟨FreeMonoid.of g, invol1 g⟩

/-- Theorem 5.2, with `r_K`: `R₁⁺` presents `O(8, 𝔻)`. -/
theorem presentation : IsPresentationOf R1plus sem1 where
  grouplike := grouplike1
  sound w v h := by rw [lift_sem1, lift_sem1]; exact sound1plus_ax h
  complete w v h := complete1 (by rwa [lift_sem1, lift_sem1] at h)
  surjective A := by
    obtain ⟨u, hu⟩ := LiRossSelinger.surjective 8 A
    exact ⟨decW u, by rw [lift_sem1, dec_semW, hu]⟩

end QCert.ToffoliHadamardRS
