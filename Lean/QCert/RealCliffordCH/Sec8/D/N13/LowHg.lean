/- Small-width cases of (337). -/
import QCert.RealCliffordCH.Sec8.D.W4.BoxHgLow
import QCert.RealCliffordCH.Sec8.D.N13.ThreeHg
import QCert.RealCliffordCH.Sec8.D.N13.Low
namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem core337_3 (ih : IH 3) (a b c : Bool) (hxy : b ≠ c) :
    Comm 3 (mc 3 .box [0] (SE.ctl 3 [(1, a), (2, b)] false)) (mc 3 .hg [0, 1] (SE.ctl 3 [(2, c)] false)) := by
  cases a <;> cases b <;> cases c
  · simp at hxy
  · exact Low3Hg.tLowHg3_337FFT ih
  · exact Low3Hg.tLowHg3_337FTF ih
  · simp at hxy
  · simp at hxy
  · exact Low3Hg.tLowHg3_337TFT ih
  · exact Low3Hg.tLowHg3_337TTF ih
  · simp at hxy
theorem comm337_3 (ih : IH 3) (x y : ℕ → Bool) (hxy : DiffOn 2 3 x y) (c : Bool) :
    Comm 3 (mc 3 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x)))
      (mc 3 .hg [0, 1] (colOn 2 3 y)) := by
  have hx : mc 3 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 3 x)) = mc 3 .box [0] (SE.ctl 3 [(1, c), (2, x 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 3 .hg [0, 1] (colOn 2 3 y) = mc 3 .hg [0, 1] (SE.ctl 3 [(2, y 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  apply core337_3 ih
  obtain ⟨i, hi, hiN, hne⟩ := hxy
  have : i = 2 := by omega
  simpa [this] using hne
theorem core337_4 (ih : IH 4) (a b c d e : Bool) (hxy : b ≠ d ∨ c ≠ e) :
    Comm 4 (mc 4 .box [0] (SE.ctl 4 [(1, a), (2, b), (3, c)] false)) (mc 4 .hg [0, 1] (SE.ctl 4 [(2, d), (3, e)] false)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e
  · simp at hxy
  · exact W4LowHg.tWhiteHg337TFf2f3 ih
  · exact W4LowHg.tWhiteHg337FTf2f3 ih
  · exact W4LowHg.tWhiteHg337FFf2f3 ih
  · exact W4LowHg.tWhiteHg337TFf2 ih
  · simp at hxy
  · exact W4LowHg.tWhiteHg337FFf2 ih
  · exact W4LowHg.tWhiteHg337FTf2 ih
  · exact W4LowHg.tWhiteHg337FTf3 ih
  · exact W4LowHg.tWhiteHg337FFf3 ih
  · simp at hxy
  · exact W4LowHg.tWhiteHg337TFf3 ih
  · exact W4LowHg.tWhiteHg337FF ih
  · exact W4LowHg.tWhiteHg337FT ih
  · exact W4LowHg.tWhiteHg337TF ih
  · simp at hxy
  · simp at hxy
  · exact W4LowHg.tHg337BaseTFf2f3 ih
  · exact W4LowHg.tHg337BaseFTf2f3 ih
  · exact W4LowHg.tHg337BaseFFf2f3 ih
  · exact W4LowHg.tHg337BaseTFf2 ih
  · simp at hxy
  · exact W4LowHg.tHg337BaseFFf2 ih
  · exact W4LowHg.tHg337BaseFTf2 ih
  · exact W4LowHg.tHg337BaseFTf3 ih
  · exact W4LowHg.tHg337BaseFFf3 ih
  · simp at hxy
  · exact W4LowHg.tHg337BaseTFf3 ih
  · exact W4LowHg.tHg337BaseFF ih
  · exact W4LowHg.tHg337BaseFT ih
  · exact W4LowHg.tHg337BaseTF ih
  · simp at hxy
theorem comm337_4 (ih : IH 4) (x y : ℕ → Bool) (hxy : DiffOn 2 4 x y) (c : Bool) :
    Comm 4 (mc 4 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 4 x)))
      (mc 4 .hg [0, 1] (colOn 2 4 y)) := by
  have hx : mc 4 .box [0] (ctlOr (ctlAt 1 c) (colOn 2 4 x)) = mc 4 .box [0] (SE.ctl 4 [(1, c), (2, x 2), (3, x 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 4 .hg [0, 1] (colOn 2 4 y) = mc 4 .hg [0, 1] (SE.ctl 4 [(2, y 2), (3, y 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  apply core337_4 ih
  obtain ⟨i, hi, hiN, hne⟩ := hxy
  rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl
  · exact Or.inl hne
  · exact Or.inr hne
end QCert.RealCliffordCH.Sec8.D.N13
