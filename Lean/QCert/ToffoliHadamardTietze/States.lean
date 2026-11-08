/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-Tietze`: states

Translation of `States.agda`: facts about functions on the eight basis
states, decided by evaluation: two functions agree on the states below `j`
(`agree`) or everywhere (`everywhere`), a property holds of every state
(`all8`), and a concrete list of states is duplicate-free (`distinct`).  As
in `CCX+H-3qubit-RS`'s `Check`.  States are natural numbers below `8` here,
as in `CoxeterFrames`, where the Agda's are `Fin 8`.
-/
import QCert.Presentation

namespace QCert.ToffoliHadamardTietze

/-- A property of every state. -/
def all8 (P : ℕ → Bool) : Bool := (List.range 8).all P

theorem all8_sound (P : ℕ → Bool) (h : all8 P = true) : ∀ x, x < 8 → P x = true := by
  intro x hx
  simp only [all8, List.all_eq_true, List.mem_range] at h
  exact h x hx

/-- `x < y`, decided. -/
def incr (x y : ℕ) : Bool := Nat.blt x y

theorem incr_ok {x y : ℕ} (h : x < y) : incr x y = true := by rw [incr, Nat.blt_eq]; exact h

/-- What a guarded check gives when its guard holds. -/
theorem if_true (b : Bool) {t : Bool} (hb : b = true) (h : (if b then t else true) = true) : t = true := by
  subst hb; exact h

/-- `f` and `g` agree on the states below `j`. -/
def below (j : ℕ) (f g : ℕ → ℕ) : Bool := (List.range j).all fun x => Nat.beq (f x) (g x)

theorem agree (j : ℕ) (f g : ℕ → ℕ) (h : below j f g = true) : ∀ x, x < j → f x = g x := by
  intro x hx
  simp only [below, List.all_eq_true, List.mem_range] at h
  exact Nat.eq_of_beq_eq_true (h x hx)

/-- On all eight states. -/
theorem everywhere (f g : ℕ → ℕ) (h : below 8 f g = true) : ∀ x, x < 8 → f x = g x :=
  agree 8 f g h

/-- A duplicate-free list of states, decided. -/
theorem distinct (xs : List ℕ) (h : decide xs.Nodup = true) : xs.Nodup := of_decide_eq_true h

end QCert.ToffoliHadamardTietze
