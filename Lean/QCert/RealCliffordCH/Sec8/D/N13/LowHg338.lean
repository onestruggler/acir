/- Small-width cases of (338). -/
import QCert.RealCliffordCH.Sec8.D.W4.BoxHgLow
import QCert.RealCliffordCH.Sec8.D.N13.ThreeHg338
import QCert.RealCliffordCH.Sec8.D.N13.Low
namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem core338_3 (ih : IH 3) (a b c : Bool) :
    Comm 3 (mc 3 .box [0] (SE.ctl 3 [(1, a), (2, b)] false)) (mc 3 .hg [1, 0] (SE.ctl 3 [(2, c)] false)) := by
  cases a <;> cases b <;> cases c
  · exact Low3Hg338.tLowHg338FFF ih
  · exact Low3Hg338.tLowHg338FFT ih
  · exact Low3Hg338.tLowHg338FTF ih
  · exact Low3Hg338.tLowHg338FTT ih
  · exact Low3Hg338.tLowHg338TFF ih
  · exact Low3Hg338.tLowHg338TFT ih
  · exact Low3Hg338.tLowHg338TTF ih
  · exact Low3Hg338.tLowHg338TTT ih
theorem comm338_3 (ih : IH 3) (x y : ℕ → Bool) (c : Bool) :
    Comm 3 (mc 3 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x)))
      (mc 3 .hg [1, 0] (colOn 2 3 y)) := by
  have hx : mc 3 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x)) = mc 3 .box [0] (SE.ctl 3 [(1, c), (2, x 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 3 .hg [1, 0] (colOn 2 3 y) = mc 3 .hg [1, 0] (SE.ctl 3 [(2, y 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  exact core338_3 ih _ _ _
theorem core338_4 (ih : IH 4) (a b c d e : Bool) (hxy : b ≠ d ∨ c ≠ e) :
    Comm 4 (mc 4 .box [0] (SE.ctl 4 [(1, a), (2, b), (3, c)] false)) (mc 4 .hg [1, 0] (SE.ctl 4 [(2, d), (3, e)] false)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e
  · simp at hxy
  · exact W4LowHg.tHg338BaseTFf1f2f3 ih
  · exact W4LowHg.tHg338BaseFTf1f2f3 ih
  · exact W4LowHg.tHg338BaseFFf1f2f3 ih
  · exact W4LowHg.tHg338BaseTFf1f2 ih
  · simp at hxy
  · exact W4LowHg.tHg338BaseFFf1f2 ih
  · exact W4LowHg.tHg338BaseFTf1f2 ih
  · exact W4LowHg.tHg338BaseFTf1f3 ih
  · exact W4LowHg.tHg338BaseFFf1f3 ih
  · simp at hxy
  · exact W4LowHg.tHg338BaseTFf1f3 ih
  · exact W4LowHg.tHg338BaseFFf1 ih
  · exact W4LowHg.tHg338BaseFTf1 ih
  · exact W4LowHg.tHg338BaseTFf1 ih
  · simp at hxy
  · simp at hxy
  · exact W4LowHg.tHg338BaseTFf2f3 ih
  · exact W4LowHg.tHg338BaseFTf2f3 ih
  · exact W4LowHg.tHg338BaseFFf2f3 ih
  · exact W4LowHg.tHg338BaseTFf2 ih
  · simp at hxy
  · exact W4LowHg.tHg338BaseFFf2 ih
  · exact W4LowHg.tHg338BaseFTf2 ih
  · exact W4LowHg.tHg338BaseFTf3 ih
  · exact W4LowHg.tHg338BaseFFf3 ih
  · simp at hxy
  · exact W4LowHg.tHg338BaseTFf3 ih
  · exact W4LowHg.tHg338BaseFF ih
  · exact W4LowHg.tHg338BaseFT ih
  · exact W4LowHg.tHg338BaseTF ih
  · simp at hxy
theorem comm338_4 (ih : IH 4) (x y : ℕ → Bool) (hxy : DiffOn 2 4 x y) (c : Bool) :
    Comm 4 (mc 4 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 4 x)))
      (mc 4 .hg [1, 0] (colOn 2 4 y)) := by
  have hx : mc 4 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 4 x)) = mc 4 .box [0] (SE.ctl 4 [(1, c), (2, x 2), (3, x 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 4 .hg [1, 0] (colOn 2 4 y) = mc 4 .hg [1, 0] (SE.ctl 4 [(2, y 2), (3, y 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  apply core338_4 ih
  obtain ⟨i, hi, hiN, hne⟩ := hxy
  rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl
  · exact Or.inl hne
  · exact Or.inr hne
end QCert.RealCliffordCH.Sec8.D.N13
