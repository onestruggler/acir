/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness: congruent circuits denote the same even permutation

Translation of `Examples/Groups/Alternating/Soundness.agda`.

Two steps, for any theory.  `sound_ax` handles the raw relation given
soundness of the theory's own rules: a shifted rule by `sem_up` and the
induction hypothesis, `Lift.comm3` by case analysis on `Fin`; `sound` then
closes it under the monoid congruence.  The rules of Theorem 4 are checked
one by one (`sound_S`), each by case analysis on the at most five wires it
touches.

**Deviations from the Agda.**  The Agda's module parameters `T` and
`sound-T` are arguments of `sound_ax` and `sound`.  `sound` is by the
congruence being the least one containing the relation (`Con.conGen_le`),
where the Agda recurses on the derivation.  Each rule is first read as an
equation between composites of `cycle` and its lifts (`cycle_order`,
`cycle_near`, `cycle_far`), which the case analysis then proves by `rfl`;
the Agda's `refl`s check the circuits' denotations directly.  `sound-R` (the
rules of Fig. 10 as a theory) and `sound-A` (`Alternative`'s relations) are
not translated.
-/
import QCert.Alt16RevCir.Lib.Alternating.Interpretation

namespace QCert.Alt16RevCir.Alternating

open QCert QCert.Circuit

variable {n : ℕ}

/-! ## The structural rules -/

/-- A cycle commutes with any permutation of the wires above it. -/
theorem sound_comm₃ (π : Equiv.Perm (Fin n)) : ∀ i : Fin (n + 3),
    cycle (lift₀ (lift₀ (lift₀ π)) i) = lift₀ (lift₀ (lift₀ π)) (cycle i)
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨_ + 3, _⟩ => rfl

section Theory

variable {T : Theory}
  (sound_T : ∀ {n : ℕ} {w v : Circ n}, T n w v → ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i)

include sound_T

/-- Soundness of the raw relation. -/
theorem sound_ax : ∀ {n : ℕ} {w v : Circ n}, Lift T n w v →
    ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i
  | _, _, _, .rule r, k => sound_T r k
  | _, _, _, .shift (w := w) (v := v) p, k =>
    (sem_up w k).trans ((lift₀_cong (sound_ax p) k).trans (sem_up v k).symm)
  | _, _, _, .comm1 h _, _ => nomatch h
  | _, _, _, .comm2 h _, _ => nomatch h
  | _, _, _, .comm3 .ω_gate g, k => by
    rw [sem_mul, sem_mul, sem_of, sem_of, perm_semG_ω, perm_semG_up, perm_semG_up, perm_semG_up]
    exact sound_comm₃ (Alt.perm (semG g)) k
  | _, _, _, .scalar c, _ => nomatch c

/-- Soundness of the congruence. -/
theorem sound {n : ℕ} {w v : Circ n} (d : Derives T n w v) (i : Fin n) :
    Alt.perm (sem w) i = Alt.perm (sem v) i := by
  let c : Con (Circ n) :=
    { r := fun w v => ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i
      iseqv := ⟨fun _ _ => rfl, fun e i => (e i).symm, fun e e' i => (e i).trans (e' i)⟩
      mul' := fun {w w' v v'} e e' i => by rw [sem_mul, sem_mul, e i, e' _] }
  have : conGen (Lift T n) ≤ c := Con.conGen_le fun _ _ r => sound_ax sound_T r
  exact this d i

end Theory

/-! ## Theorem 4's relations -/

/-- `order`, on permutations. -/
theorem cycle_order : ∀ i : Fin (n + 3), cycle (cycle (cycle i)) = i
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨_ + 3, _⟩ => rfl

/-- `near`, on permutations. -/
theorem cycle_near : ∀ i : Fin (n + 4),
    cycle (lift₀ cycle (cycle i)) = lift₀ cycle (lift₀ cycle i)
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨_ + 4, _⟩ => rfl

/-- `far`, on permutations. -/
theorem cycle_far : ∀ i : Fin (n + 5),
    cycle (lift₀ (lift₀ cycle) (cycle i)) = lift₀ cycle (cycle (lift₀ (lift₀ cycle) i))
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨_ + 5, _⟩ => rfl

/-- Theorem 4's relations are sound. -/
theorem sound_S : ∀ {n : ℕ} {w v : Circ n}, SRel n w v →
    ∀ i, Alt.perm (sem w) i = Alt.perm (sem v) i
  | _, _, _, .order, i => by
    simp only [sem_mul, sem_one, sem_of, perm_semG_ω]
    exact cycle_order i
  | _, _, _, .near, i => by
    simp only [sem_mul, shift_of, sem_of, perm_semG_ω, perm_semG_up]
    exact cycle_near i
  | _, _, _, .far, i => by
    simp only [sem_mul, shift_of, sem_of, perm_semG_ω, perm_semG_up]
    exact cycle_far i

end QCert.Alt16RevCir.Alternating
