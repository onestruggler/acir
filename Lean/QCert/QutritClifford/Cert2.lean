/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness on two wires

Toward Theorem 4.4.  The coset certificate of `Cert2Data.lean` checks
(`cert2_ok`, given completeness on one wire for the stabiliser facts of
the two-wire library): every two-qutrit word is derivably, up to a phase,
a local word times the representative of its coset.  A word acting
trivially on the Paulis reaches the coset of the local subgroup, since no
other representative acts like a local word (`cert2_reps`), and a local
word acting trivially is derivably trivial (`local_trivial`), so the rules
are complete on two wires (`complete_two`).
-/
import QCert.QutritClifford.Cert1
import QCert.QutritClifford.Cert2Data

namespace QCert.QutritClifford

theorem cert2_len : cert2.dl.length = 90 ∧ cert2.letters.length = 5 ∧ cert2.rep.length = 90 := by
  decide +kernel

theorem cert2_ded : ∀ c < 90, ∀ i < 5, cert2.dedOk c i = true := by decide +kernel

theorem cert2_dl : ∀ c < 90, ∀ i < 5, cert2.del c i < 90 := by decide +kernel

theorem cert2_rep : ∀ c < 90, Fits 2 (cert2.repW c) := by unfold Fits; decide +kernel

theorem cert2_eqs : cert2.eqsOk eq2A (lib2T.take (base2.length + 105)) = true := by decide +kernel

/-- The two-wire certificate checks. -/
theorem cert2_ok (hc : Complete 1) : cert2.Ok where
  ded c i hc' hi := cert2_ded c (by rw [cert2_len.1] at hc'; exact hc') i
    (by rw [cert2_len.2.1] at hi; exact hi)
  dl_lt c i hc' hi := by
    rw [cert2_len.1] at hc' ⊢; rw [cert2_len.2.1] at hi; exact cert2_dl c hc' i hi
  fits_letters := by decide +kernel
  fits_rep c := by
    by_cases h : c < 90
    · exact cert2_rep c h
    · rw [Cert.repW_of_le _ (by rw [cert2_len.2.2]; omega)]; intro x hx; simp at hx
  eqs_letters := Cert.eqs_letters_of (by decide +kernel)
  eqs_valid := Cert.eqs_valid_of eq2A_valid (valid_take (lib2_valid hc)) cert2_eqs
  zero_lt := by rw [cert2_len.1]; decide
  nodup := by decide +kernel
  loc_sub := by decide +kernel

theorem cert2_reps : ∀ c < 90, c ≠ 0 → isLoc2 (cert2.repW c) = false := by decide +kernel

theorem fits2_letters {l : List Lt} (h : Fits 2 l) : ∀ x ∈ l, x ∈ cert2.letters := by
  intro x hx
  have := h x hx
  rcases x with j | j | j <;> simp only [Lt.hi] at this
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
  · obtain rfl : j = 0 := by omega
    decide

/-- On two wires, a word acting trivially on the Paulis is derivably
trivial up to a phase, given completeness on one wire. -/
theorem words_trivial_two (hc : Complete 1) : WordsTrivial 2 := by
  intro l hl h
  obtain ⟨μ, hμ, hE⟩ := Cert.word (cert2_ok hc) l (fits2_letters hl) rfl
  have hc' : cert2.walk 0 l < 90 := by
    have := Cert.walk_lt (cert2_ok hc) 0 l (cert2_ok hc).zero_lt (fits2_letters hl)
    rwa [cert2_len.1] at this
  have hact : actC 2 (cw 2 (μ ++ cert2.repW (cert2.walk 0 l))) = 1 := by
    rw [← actC_eq_of_E (n := 2) hE]; exact h
  have hloc := isLoc2_rep hμ ((cert2_ok hc).fits_rep _) hact
  by_cases hc0 : cert2.walk 0 l = 0
  · rw [hc0] at hE hact
    have h0 : cert2.repW 0 = [] := rfl
    rw [h0, List.append_nil] at hE hact
    exact hE.trans (local_trivial hc hμ hact)
  · rw [cert2_reps _ hc' hc0] at hloc; exact absurd hloc (by decide)

/-- **Completeness on two wires.** -/
theorem complete_two : Complete 2 := complete_of_words (words_trivial_two complete_one)

end QCert.QutritClifford
