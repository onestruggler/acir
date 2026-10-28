/- Equation (345): controlled Hadamards on the two bottom wires. -/
import QCert.RealCliffordCH.Sec8.D.N13.HgBorrow
import QCert.RealCliffordCH.Sec8.D.N13.Low
import QCert.RealCliffordCH.Sec8.D.N13.ThreeHg345

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net Eng SE N8
set_option maxHeartbeats 0

theorem pp_swap4 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (swAt (m + 4) 0 * (pp : Circ (m + 4)))
      (pp * swAt (m + 4) 0) := by
  have h2 : Derivable (theory 2) (swAt 2 0 * (pp : Circ 2)) (pp * swAt 2 0) :=
    ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  have h := der_atBot h2 (m + 4) (by omega)
  have ep : atBot (m + 4) (pp : Circ 2) = (pp : Circ (m + 4)) :=
    (pad_atBot2 (m + 2) pp).symm.trans (MS.pad_pp (m + 2))
  rwa [atBot_mul, atBot_mul, atBot_swAt 0 (by omega) (m + 4) (by omega), ep] at h

theorem pp_move_swap {N : ℕ} {u P a a' : Circ N}
    (hp : Derivable (theory N) (u * P) (P * u))
    (ha : Derivable (theory N) (u * a * u) a') :
    Derivable (theory N) (u * (P * a * P) * u) (P * a' * P) := by
  have e : u * (P * a * P) * u = (u * P) * a * (P * u) := by simp only [mul_assoc]
  rw [e]
  refine (dmul (dmul hp (Derivable.refl a)) hp.symm).trans ?_
  have e' : (P * u) * a * (u * P) = P * (u * a * u) * P := by simp only [mul_assoc]
  rw [e']; exact dright P (dleft P ha)

theorem hg0_box4 (m : ℕ) (x : ℕ → Bool) :
    Derivable (theory (m + 4)) (mc (m + 4) .hg [0, 1] (colOn 2 (m + 4) x))
      ((pp : Circ (m + 4)) * bA (m + 4) x true * pp) := by
  have h := hg_box m x
  have e : mc (m + 4) .box [0] (colOn 1 (m + 4) (hgCol x)) = bA (m + 4) x true :=
    (bA_eq (m + 4) x true).symm
  rw [e] at h
  simpa only [mul_assoc] using h

theorem hg1_box4 (m : ℕ) (ih : IH (m + 4)) (x : ℕ → Bool) :
    Derivable (theory (m + 4)) (mc (m + 4) .hg [1, 0] (colOn 2 (m + 4) x))
      ((pp : Circ (m + 4)) * bB (m + 4) x true * pp) :=
  (hg_swap0 (m + 4) (by omega) x).symm.trans
    ((dright _ (dleft _ (hg0_box4 m x))).trans
      (pp_move_swap (pp_swap4 m ih) (swapAB (m + 4) (by omega) x true).1))

theorem comm345_ge4 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [1, 0] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
  have hc : Comm (m + 4) (bA (m + 4) y true) (bB (m + 4) x true) := by
    cases m with
    | zero => exact comm336_4 ih y x true true
    | succ m => exact comm336_ge5 (m + 1 + 4) (by omega) ih y x true true
  have h := Comm.conj hc.symm (pp_inv (m + 1) ih)
  exact Comm.congr (hg1_box4 m ih x).symm (hg0_box4 m y).symm h

theorem comm345_3 (ih : IH 3) (x y : ℕ → Bool) :
    Comm 3 (mc 3 .hg [1, 0] (colOn 2 3 x)) (mc 3 .hg [0, 1] (colOn 2 3 y)) := by
  have e : ∀ (t u : ℕ) (x : ℕ → Bool),
      mc 3 .hg [t, u] (colOn 2 3 x) = mc 3 .hg [t, u] (SE.ctl 3 [(2, x 2)] false) := by
    intro t u x
    apply mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, SE.ctl, List.lookup_cons]
  rw [e, e]
  cases hx : x 2 <;> cases hy : y 2
  · exact Low3Hg345.tHg345FF ih
  · exact Low3Hg345.tHg345FT ih
  · exact Low3Hg345.tHg345TF ih
  · exact Low3Hg345.tHg345TT ih

theorem comm345 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [1, 0] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
  · exact comm345_3 ih x y
  · exact comm345_ge4 N h4 ih x y

end QCert.RealCliffordCH.Sec8.D.N13
