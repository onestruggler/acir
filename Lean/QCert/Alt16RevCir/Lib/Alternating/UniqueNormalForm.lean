/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lafont's Lemma 6, uniqueness

Translation of `Examples/Groups/Alternating/UniqueNormalForm.agda`: two
canonical forms that denote the same permutation are the same.

By induction on the width, as in the paper.  The stairs of a canonical form
is determined by where the permutation sends wire 0, the canonical form on
the top wires leaving wire 0 alone; cancelling the stairs (a bijection)
leaves two shifted canonical forms with the same denotation, hence
(`Fin.succ_injective`) two canonical forms one wire narrower with the same
denotation.  This mentions no relation.

**Deviations from the Agda.**  The Agda's `⟦[c]⟧-zero` is `sem_sec_zero`.
In `inv_nf_injective` the two stairs are identified first and substituted,
where the Agda transports along `c≡c′` (`on-c`).
-/
import QCert.Alt16RevCir.Lib.Alternating.Interpretation
import QCert.Alt16RevCir.Lib.Alternating.Normalization

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit

variable {n : ℕ}

/-! ## The stairs of a canonical form -/

/-- A permutation is injective. -/
theorem perm_injective (π : Equiv.Perm (Fin n)) {i j : Fin n} (h : π i = π j) : i = j :=
  (π.symm_apply_apply i).symm.trans ((congrArg π.symm h).trans (π.symm_apply_apply j))

/-- A stairs sends wire 0 to its target (the Agda's `⟦[c]⟧-zero`). -/
theorem sem_sec_zero : ∀ {n : ℕ} (c : C n), Alt.perm (sem (sec c)) 0 = target c
  | _, .ε => sem_one 0
  | _, .ωc c => by
    rw [sec_ωc, sem_mul, sem_of, perm_semG_ω]
    exact (sem_up (sec c) (Fin.succ 0)).trans (congrArg Fin.succ (sem_sec_zero c))
  | _, .ωω => by
    rw [sec_ωω, sem_mul, sem_of, perm_semG_ω]
    rfl

/-! ## Uniqueness -/

/-- Canonical forms with the same denotation are equal. -/
theorem inv_nf_injective {n : ℕ} {u v : NF n}
    (h : ∀ i, Alt.perm (sem (inv_nf u)) i = Alt.perm (sem (inv_nf v)) i) : u = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨x, c⟩ := u
    obtain ⟨x', c'⟩ := v
    -- The stairs: compare where wire 0 goes.
    have hc : c = c' := by
      have e := h 0
      simp only [inv_nf_succ, sem_mul, sem_up, lift₀_zero, sem_sec_zero] at e
      exact target_injective e
    subst hc
    -- The rest: cancel the stairs, then the shift.
    have hx : x = x' := ih fun j => by
      have e := h j.succ
      simp only [inv_nf_succ, sem_mul] at e
      have e' := perm_injective _ e
      rw [sem_up, sem_up, lift₀_succ, lift₀_succ] at e'
      exact Fin.succ_injective _ e'
    rw [hx]

end QCert.Alt16RevCir.Alternating
