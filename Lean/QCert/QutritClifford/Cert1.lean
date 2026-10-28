/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness on one wire

Toward Theorem 4.4.  The coset certificate of `Cert1Data.lean` checks
(`cert1_ok`): every one-qutrit word is derivably, up to a phase, the
representative of its coset; a word acting trivially on the Paulis reaches
the coset of the empty word, so the rules (C2)-(C5) are complete on one
wire (`complete_one`).
-/
import QCert.QutritClifford.CosetCheck
import QCert.QutritClifford.Cert1Data

namespace QCert.QutritClifford

theorem cert1_len : cert1.dl.length = 216 ∧ cert1.letters.length = 2 ∧ cert1.rep.length = 216 := by
  decide +kernel

theorem cert1_ded : ∀ c < 216, ∀ i < 2, cert1.dedOk c i = true := by decide +kernel

theorem cert1_dl : ∀ c < 216, ∀ i < 2, cert1.del c i < 216 := by decide +kernel

theorem cert1_rep : ∀ c < 216, Fits 1 (cert1.repW c) := by unfold Fits; decide +kernel

theorem cert1_eqs : cert1.eqsOk base1 [] = true := by decide +kernel

/-- The one-wire certificate checks. -/
theorem cert1_ok : cert1.Ok where
  ded c i hc hi := cert1_ded c (by rw [cert1_len.1] at hc; exact hc) i
    (by rw [cert1_len.2.1] at hi; exact hi)
  dl_lt c i hc hi := by
    rw [cert1_len.1] at hc ⊢; rw [cert1_len.2.1] at hi; exact cert1_dl c hc i hi
  fits_letters := by decide
  fits_rep c := by
    by_cases h : c < 216
    · exact cert1_rep c h
    · rw [Cert.repW_of_le _ (by rw [cert1_len.2.2]; omega)]; intro x hx; simp at hx
  eqs_letters := Cert.eqs_letters_of (by decide +kernel)
  eqs_valid := Cert.eqs_valid_of base1_valid (fun _ h => by simp at h) cert1_eqs
  zero_lt := by rw [cert1_len.1]; decide
  nodup := by decide +kernel
  loc_sub := by decide +kernel

theorem cert1_reps : ∀ c < 216, c ≠ 0 → same1 (cert1.repW c) [] = false := by decide +kernel

theorem fits1_letters {l : List Lt} (h : Fits 1 l) : ∀ x ∈ l, x ∈ cert1.letters := by
  intro x hx
  have := h x hx
  rcases x with j | j | j <;> simp only [Lt.hi] at this
  · obtain rfl : j = 0 := by omega
    decide
  · obtain rfl : j = 0 := by omega
    decide
  · omega

/-- On one wire, a word acting trivially on the Paulis is derivably trivial
up to a phase. -/
theorem words_trivial_one : WordsTrivial 1 := by
  intro l hl h
  obtain ⟨μ, hμ, hE⟩ := Cert.word cert1_ok l (fits1_letters hl) rfl
  obtain rfl : μ = [] := by
    cases μ with
    | nil => rfl
    | cons x μ => exact absurd (hμ x List.mem_cons_self) (by simp [cert1])
  have hc : cert1.walk 0 l < 216 := by
    have := Cert.walk_lt cert1_ok 0 l cert1_ok.zero_lt (fits1_letters hl)
    rwa [cert1_len.1] at this
  have hrep : actC 1 (cw 1 (cert1.repW (cert1.walk 0 l))) = 1 := by
    rw [← actC_eq_of_E (n := 1) (by simpa using hE)]; exact h
  have hs := same1_rep (cert1_ok.fits_rep _) hrep
  by_cases hc0 : cert1.walk 0 l = 0
  · rw [hc0] at hE; simpa using hE
  · rw [cert1_reps _ hc hc0] at hs; exact absurd hs (by decide)

/-- **Completeness on one wire.** -/
theorem complete_one : Complete 1 := complete_of_words words_trivial_one

end QCert.QutritClifford
