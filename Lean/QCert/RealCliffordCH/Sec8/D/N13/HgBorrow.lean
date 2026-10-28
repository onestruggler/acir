/- Circuits on the borrowed wire commute with a controlled H. -/
import QCert.RealCliffordCH.Sec8.D.N13.MergeAll
import QCert.RealCliffordCH.Sec8.D.N13.E336x

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net Eng SE
set_option maxHeartbeats 0

theorem hg_swap0 (N : ℕ) (hN : 3 ≤ N) (y : ℕ → Bool) :
    Derivable (theory N)
      (swAt N 0 * mc N .hg [0, 1] (colOn 2 N y) * swAt N 0)
      (mc N .hg [1, 0] (colOn 2 N y)) := by
  have h := mc_swap N 0 (by omega) .hg [0, 1] (colOn 2 N y)
    rfl (by decide) (by simp; omega) (by
      intro h; have h0 := h.1
      rw [MS.mem_ctrlWires] at h0
      exact h0.2.2 (by simp))
  have he : ([0, 1] : List ℕ).map (Net.tau 0) = [1, 0] := by decide
  rw [he, show drawn [swAt N 0, mc N .hg [0, 1] (colOn 2 N y), swAt N 0] =
      swAt N 0 * mc N .hg [0, 1] (colOn 2 N y) * swAt N 0 by simp [drawn, mul_assoc]] at h
  refine h.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
  simp only [Function.comp, colOn, Net.tau]
  split_ifs <;> first | rfl | omega

theorem atBot_twice {k m : ℕ} (g : Circ k) (hkm : k ≤ m) :
    ∀ N, m ≤ N → atBot N (atBot m g) = atBot N g := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [atBot_self]
  | succ M hM ihM =>
    rw [atBot_succ M _ (by omega), atBot_succ M _ (by omega), ihM]

theorem small_box_swap (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (swAt N 0 * atBot N (z : Circ 1) * swAt N 0)
      (mc N .box [0] (ctlAt 1 true)) := by
  have h2 : Derivable (theory 2) (swAt 2 0 * atBot 2 (z : Circ 1) * swAt 2 0)
      (mc 2 .box [0] (ctlAt 1 true)) :=
    ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h2 N (by omega)
  rw [atBot_mul, atBot_mul, atBot_swAt 0 (by omega) N (by omega),
    atBot_twice z (by omega) N (by omega)] at h
  rw [mc_atBot (k := 2) .box [0] (ctlAt 1 true) rfl (by simp) (by simp)
    (by intro j hj; simp [ctlAt]; omega) N (by omega)]
  exact h

theorem small_box_hg_black (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Comm N (mc N .box [0] (ctlAt 1 true)) (mc N .hg [1, 0] (colOn 2 N fun _ => true)) := by
  have h := eq314 N hN ih 1 le_rfl (by omega) (z : Circ 1)
  have e : blackOn 2 N = colOn 2 N (fun _ => true) := by funext i; simp [blackOn, colOn]
  change Comm N (atBot N (z : Circ 1)) (mc N .hg [0, 1] (blackOn 2 N)) at h
  rw [e] at h
  exact Comm.congr (small_box_swap N hN ih) (hg_swap0 N hN _)
    (Comm.conj h (swsw N 0 (by omega)))

theorem xAt_atBot (k j : ℕ) (hj : j < k) :
    ∀ N, k ≤ N → xAt N j = atBot N (xAt k j) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [atBot_self]
  | succ M hM ihM =>
    rw [xAt_top M j (by omega), ihM, atBot_succ M _ (by omega)]

theorem swap_x_one (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (swAt N 0 * atBot N (x : Circ 1) * swAt N 0) (xAt N 1) := by
  have h2 : Derivable (theory 2) (swAt 2 0 * atBot 2 (x : Circ 1) * swAt 2 0) (xAt 2 1) :=
    ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h2 N (by omega)
  rw [atBot_mul, atBot_mul, atBot_swAt 0 (by omega) N (by omega),
    atBot_twice x (by omega) N (by omega)] at h
  rwa [xAt_atBot 2 1 (by omega) N (by omega)]

theorem x_one_hg_black (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Comm N (xAt N 1) (mc N .hg [1, 0] (colOn 2 N fun _ => true)) := by
  have h := eq314 N hN ih 1 le_rfl (by omega) (x : Circ 1)
  have e : blackOn 2 N = colOn 2 N (fun _ => true) := by funext i; simp [blackOn, colOn]
  change Comm N (atBot N (x : Circ 1)) (mc N .hg [0, 1] (blackOn 2 N)) at h
  rw [e] at h
  exact Comm.congr (swap_x_one N hN ih) (hg_swap0 N hN _)
    (Comm.conj h (swsw N 0 (by omega)))

end QCert.RealCliffordCH.Sec8.D.N13
