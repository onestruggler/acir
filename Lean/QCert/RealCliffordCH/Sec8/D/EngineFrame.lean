/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The placement hypothesis of the engine, discharged

`SymEngine.Frame k` asks that a letter avoiding the local wire `q`,
conjugated by a fixed network, be its version without that wire with an idle
wire on top.  The network is `Net.topNet`, carrying wire `q` to the top, and
the property is `Net.mc_toTop` for the multi-controlled letters and
`Net.letter_toTop` for the small ones.
-/
import QCert.RealCliffordCH.Sec8.D.SymEngine
import QCert.RealCliffordCH.Sec8.Net

namespace QCert.RealCliffordCH.Sec8.SE

open Circuit Eng Net

theorem dropW_eq : SE.dropW = Net.dropW := rfl

theorem kindSp_eq (Kd : Kind) : Kd.ar = kindSp Kd := by cases Kd <;> rfl

theorem dropL_eq (q : ℕ) (l : L) (hq : q < l.lo ∨ l.lo + l.wd ≤ q) :
    (if q < l.lo then l.down else l) = dropL q l := by
  cases l <;> simp only [L.lo, L.wd, L.down, dropL, Net.dropW] at hq ⊢ <;> split_ifs <;> first
    | rfl | (congr 1; omega)

/-- Looking up a key in a list whose keys are mapped by `dropW q`. -/
theorem lookup_drop (q : ℕ) : ∀ (cs : List (ℕ × Bool)), (∀ p ∈ cs, p.1 ≠ q) → ∀ i,
    (cs.map fun p => (Net.dropW q p.1, p.2)).lookup i = cs.lookup (liftW q i)
  | [], _, _ => rfl
  | (p, v) :: cs, h, i => by
    have hp : p ≠ q := h (p, v) (by simp)
    have ih := lookup_drop q cs (fun p hp => h p (by simp [hp])) i
    have hiff : i = Net.dropW q p ↔ liftW q i = p := by
      simp only [Net.dropW, liftW]; constructor <;> intro e <;> split_ifs at * <;> omega
    by_cases hi : i = Net.dropW q p
    · have hl : liftW q i = p := hiff.1 hi
      simp only [List.map_cons, List.lookup_cons]
      rw [show (i == Net.dropW q p) = true from by simpa using hi,
        show (liftW q i == p) = true from by simpa using hl]
    · have hl : liftW q i ≠ p := fun e => hi (hiff.2 e)
      simp only [List.map_cons, List.lookup_cons]
      rw [show (i == Net.dropW q p) = false from by simpa using hi,
        show (liftW q i == p) = false from by simpa using hl]
      exact ih

/-- The frame of the engine, from `Net`. -/
def frame (k : ℕ) : Frame k where
  c m q := swW (m + k + 1) (topNet (m + k) q)
  c' m q := swW (m + k + 1) (topNet (m + k) q).reverse
  inv m q := by
    rw [← swW_append]; exact (SwEq.cancel _ (topNet_ok (m + k) q)).der
  inv' m q := by
    rw [← swW_append]
    have := (SwEq.cancel _ (topNet_rev_ok (m + k) q)).der
    rwa [List.reverse_reverse] at this
  top m q x hq hx hav := by
    cases x with
    | s l =>
      simp only [Lt.ok, decide_eq_true_eq] at hx
      simp only [Lt.avoids, Bool.or_eq_true, decide_eq_true_eq] at hav
      have hq' : q < l.lo ∨ l.lo + l.wd ≤ q := hav.symm
      have h := letter_toTop (m + k) q (by omega) l (by omega) hq'
      show Derivable _ _ (padTop ((Lt.drop q (Lt.s l)).circ k (m + k)))
      simp only [Lt.drop]
      have e : (if q < l.lo then Lt.s l.down else Lt.s l) = Lt.s (dropL q l) := by
        rw [← dropL_eq q l hq']; split_ifs <;> rfl
      rw [e]
      exact h
    | g Kd tg cs b =>
      simp only [Lt.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hx
      obtain ⟨⟨hnd, hlt⟩, ha⟩ := hx
      simp only [Lt.avoids, Bool.and_eq_true, Bool.not_eq_true'] at hav
      have hqt : q ∉ tg := by
        intro hm
        have : tg.contains q = true := by simpa using hm
        rw [this] at hav; exact Bool.noConfusion hav.1
      have hcs : ∀ p ∈ cs, p.1 ≠ q := by
        intro p hp e
        have : cs.any (fun p => p.1 == q) = true := List.any_eq_true.2 ⟨p, hp, by simp [e]⟩
        rw [this] at hav; exact Bool.noConfusion hav.2
      have hcq : ctl (k + 1) cs b q = none := by
        simp only [ctl, if_pos (show q < k + 1 by omega)]
        exact List.lookup_eq_none_iff.2 (fun p hp => by
          simpa using (hcs p hp).symm)
      have h := mc_toTop (m + k) q (by omega) Kd tg (ctl (k + 1) cs b) (by rw [← kindSp_eq]; exact ha)
        hnd (fun t ht => by have := hlt t ht; simp at this; omega) hqt hcq
      have e : (Lt.drop q (Lt.g Kd tg cs b)).circ k (m + k) =
          mc (m + k) Kd (tg.map (SE.dropW q)) (ctl k (cs.map fun p => (SE.dropW q p.1, p.2)) b) :=
        rfl
      rw [e]
      rw [dropW_eq]
      have hmc : mc (m + k) Kd (tg.map (Net.dropW q)) (ctl (k + 1) cs b ∘ liftW q) =
          mc (m + k) Kd (tg.map (Net.dropW q)) (ctl k (cs.map fun p => (Net.dropW q p.1, p.2)) b) := by
        refine mc_congr (m + k) Kd _ (fun i hi => ?_)
        simp only [Function.comp_apply, ctl]
        by_cases hik : i < k
        · rw [if_pos hik, lookup_drop q cs hcs i,
            if_pos (show liftW q i < k + 1 by simp only [liftW]; split_ifs <;> omega)]
        · rw [if_neg hik, if_neg (show ¬ liftW q i < k + 1 by simp only [liftW]; split_ifs <;> omega)]
      rw [hmc] at h
      exact h

end QCert.RealCliffordCH.Sec8.SE
