/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: checks

Translation of `Check.agda`: facts about functions on the eight basis states,
decided by evaluation: two functions agree on the states below `j`
(`agree`), or on all eight (`everywhere`), and a concrete list of states is
duplicate-free (`distinct`).  States are natural numbers here, as in
`CoxeterFrames`.
-/
import QCert.Presentation

namespace QCert.ToffoliHadamardRS

/-- `f` and `g` agree on the states below `j`. -/
def below (j : ℕ) (f g : ℕ → ℕ) : Bool := (List.range j).all fun x => Nat.beq (f x) (g x)

theorem agree (j : ℕ) (f g : ℕ → ℕ) (h : below j f g = true) : ∀ x, x < j → f x = g x := by
  intro x hx
  simp only [below, List.all_eq_true, List.mem_range] at h
  exact Nat.eq_of_beq_eq_true (h x hx)

/-- On all eight basis states. -/
theorem everywhere (f g : ℕ → ℕ) (h : below 8 f g = true) : ∀ x, x < 8 → f x = g x :=
  agree 8 f g h

/-- A duplicate-free list of states, decided. -/
theorem distinct (xs : List ℕ) (h : decide xs.Nodup = true) : xs.Nodup := of_decide_eq_true h

end QCert.ToffoliHadamardRS
