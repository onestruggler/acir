/- Small-width cases of the general commutation equations. -/
import QCert.RealCliffordCH.Sec8.D.W4.BoxCommLow
import QCert.RealCliffordCH.Sec8.D.N13.Three
import QCert.RealCliffordCH.Sec8.D.N13.E336x
import QCert.RealCliffordCH.Sec8.D.N13.E340
import Mathlib.Tactic.IntervalCases

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Net
set_option maxRecDepth 20000
theorem core335_4 (ih : IH 4) (a b c d e f : Bool) :
    Comm 4 (mc 4 .box [0] (SE.ctl 4 [(1, a), (2, b), (3, c)] false)) (mc 4 .box [0] (SE.ctl 4 [(1, d), (2, e), (3, f)] false)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
  · exact W4Low.tBox335BaseTTTf1f2f3 ih
  · exact W4Low.tBox335BaseTTFf1f2f3 ih
  · exact W4Low.tBox335BaseTFTf1f2f3 ih
  · exact W4Low.tBox335BaseTFFf1f2f3 ih
  · exact W4Low.tBox335BaseFTTf1f2f3 ih
  · exact W4Low.tBox335BaseFTFf1f2f3 ih
  · exact W4Low.tBox335BaseFFTf1f2f3 ih
  · exact W4Low.tBox335BaseFFFf1f2f3 ih
  · exact W4Low.tBox335BaseTTFf1f2 ih
  · exact W4Low.tBox335BaseTTTf1f2 ih
  · exact W4Low.tBox335BaseTFFf1f2 ih
  · exact W4Low.tBox335BaseTFTf1f2 ih
  · exact W4Low.tBox335BaseFTFf1f2 ih
  · exact W4Low.tBox335BaseFTTf1f2 ih
  · exact W4Low.tBox335BaseFFFf1f2 ih
  · exact W4Low.tBox335BaseFFTf1f2 ih
  · exact W4Low.tBox335BaseTFTf1f3 ih
  · exact W4Low.tBox335BaseTFFf1f3 ih
  · exact W4Low.tBox335BaseTTTf1f3 ih
  · exact W4Low.tBox335BaseTTFf1f3 ih
  · exact W4Low.tBox335BaseFFTf1f3 ih
  · exact W4Low.tBox335BaseFFFf1f3 ih
  · exact W4Low.tBox335BaseFTTf1f3 ih
  · exact W4Low.tBox335BaseFTFf1f3 ih
  · exact W4Low.tBox335BaseTFFf1 ih
  · exact W4Low.tBox335BaseTFTf1 ih
  · exact W4Low.tBox335BaseTTFf1 ih
  · exact W4Low.tBox335BaseTTTf1 ih
  · exact W4Low.tBox335BaseFFFf1 ih
  · exact W4Low.tBox335BaseFFTf1 ih
  · exact W4Low.tBox335BaseFTFf1 ih
  · exact W4Low.tBox335BaseFTTf1 ih
  · exact W4Low.tBox335BaseFTTf2f3 ih
  · exact W4Low.tBox335BaseFTFf2f3 ih
  · exact W4Low.tBox335BaseFFTf2f3 ih
  · exact W4Low.tBox335BaseFFFf2f3 ih
  · exact W4Low.tBox335BaseTTTf2f3 ih
  · exact W4Low.tBox335BaseTTFf2f3 ih
  · exact W4Low.tBox335BaseTFTf2f3 ih
  · exact W4Low.tBox335BaseTFFf2f3 ih
  · exact W4Low.tBox335BaseFTFf2 ih
  · exact W4Low.tBox335BaseFTTf2 ih
  · exact W4Low.tBox335BaseFFFf2 ih
  · exact W4Low.tBox335BaseFFTf2 ih
  · exact W4Low.tBox335BaseTTFf2 ih
  · exact W4Low.tBox335BaseTTTf2 ih
  · exact W4Low.tBox335BaseTFFf2 ih
  · exact W4Low.tBox335BaseTFTf2 ih
  · exact W4Low.tBox335BaseFFTf3 ih
  · exact W4Low.tBox335BaseFFFf3 ih
  · exact W4Low.tBox335BaseFTTf3 ih
  · exact W4Low.tBox335BaseFTFf3 ih
  · exact W4Low.tBox335BaseTFTf3 ih
  · exact W4Low.tBox335BaseTFFf3 ih
  · exact W4Low.tBox335BaseTTTf3 ih
  · exact W4Low.tBox335BaseTTFf3 ih
  · exact W4Low.tBox335BaseFFF ih
  · exact W4Low.tBox335BaseFFT ih
  · exact W4Low.tBox335BaseFTF ih
  · exact W4Low.tBox335BaseFTT ih
  · exact W4Low.tBox335BaseTFF ih
  · exact W4Low.tBox335BaseTFT ih
  · exact W4Low.tBox335BaseTTF ih
  · exact W4Low.tBox335BaseTTT ih
theorem core336_4 (ih : IH 4) (a b c d e f : Bool) :
    Comm 4 (mc 4 .box [0] (SE.ctl 4 [(1, a), (2, b), (3, c)] false)) (mc 4 .box [1] (SE.ctl 4 [(0, d), (2, e), (3, f)] false)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
  · exact W4Low.tBox336BaseTTTf0f1f2f3 ih
  · exact W4Low.tBox336BaseTTFf0f1f2f3 ih
  · exact W4Low.tBox336BaseTFTf0f1f2f3 ih
  · exact W4Low.tBox336BaseTFFf0f1f2f3 ih
  · exact W4Low.tBox336BaseTTTf1f2f3 ih
  · exact W4Low.tBox336BaseTTFf1f2f3 ih
  · exact W4Low.tBox336BaseTFTf1f2f3 ih
  · exact W4Low.tBox336BaseTFFf1f2f3 ih
  · exact W4Low.tBox336BaseTTFf0f1f2 ih
  · exact W4Low.tBox336BaseTTTf0f1f2 ih
  · exact W4Low.tBox336BaseTFFf0f1f2 ih
  · exact W4Low.tBox336BaseTFTf0f1f2 ih
  · exact W4Low.tBox336BaseTTFf1f2 ih
  · exact W4Low.tBox336BaseTTTf1f2 ih
  · exact W4Low.tBox336BaseTFFf1f2 ih
  · exact W4Low.tBox336BaseTFTf1f2 ih
  · exact W4Low.tBox336BaseTFTf0f1f3 ih
  · exact W4Low.tBox336BaseTFFf0f1f3 ih
  · exact W4Low.tBox336BaseTTTf0f1f3 ih
  · exact W4Low.tBox336BaseTTFf0f1f3 ih
  · exact W4Low.tBox336BaseTFTf1f3 ih
  · exact W4Low.tBox336BaseTFFf1f3 ih
  · exact W4Low.tBox336BaseTTTf1f3 ih
  · exact W4Low.tBox336BaseTTFf1f3 ih
  · exact W4Low.tBox336BaseTFFf0f1 ih
  · exact W4Low.tBox336BaseTFTf0f1 ih
  · exact W4Low.tBox336BaseTTFf0f1 ih
  · exact W4Low.tBox336BaseTTTf0f1 ih
  · exact W4Low.tBox336BaseTFFf1 ih
  · exact W4Low.tBox336BaseTFTf1 ih
  · exact W4Low.tBox336BaseTTFf1 ih
  · exact W4Low.tBox336BaseTTTf1 ih
  · exact W4Low.tBox336BaseTTTf0f2f3 ih
  · exact W4Low.tBox336BaseTTFf0f2f3 ih
  · exact W4Low.tBox336BaseTFTf0f2f3 ih
  · exact W4Low.tBox336BaseTFFf0f2f3 ih
  · exact W4Low.tBox336BaseTTTf2f3 ih
  · exact W4Low.tBox336BaseTTFf2f3 ih
  · exact W4Low.tBox336BaseTFTf2f3 ih
  · exact W4Low.tBox336BaseTFFf2f3 ih
  · exact W4Low.tBox336BaseTTFf0f2 ih
  · exact W4Low.tBox336BaseTTTf0f2 ih
  · exact W4Low.tBox336BaseTFFf0f2 ih
  · exact W4Low.tBox336BaseTFTf0f2 ih
  · exact W4Low.tBox336BaseTTFf2 ih
  · exact W4Low.tBox336BaseTTTf2 ih
  · exact W4Low.tBox336BaseTFFf2 ih
  · exact W4Low.tBox336BaseTFTf2 ih
  · exact W4Low.tBox336BaseTFTf0f3 ih
  · exact W4Low.tBox336BaseTFFf0f3 ih
  · exact W4Low.tBox336BaseTTTf0f3 ih
  · exact W4Low.tBox336BaseTTFf0f3 ih
  · exact W4Low.tBox336BaseTFTf3 ih
  · exact W4Low.tBox336BaseTFFf3 ih
  · exact W4Low.tBox336BaseTTTf3 ih
  · exact W4Low.tBox336BaseTTFf3 ih
  · exact W4Low.tBox336BaseTFFf0 ih
  · exact W4Low.tBox336BaseTFTf0 ih
  · exact W4Low.tBox336BaseTTFf0 ih
  · exact W4Low.tBox336BaseTTTf0 ih
  · exact W4Low.tBox336BaseTFF ih
  · exact W4Low.tBox336BaseTFT ih
  · exact W4Low.tBox336BaseTTF ih
  · exact W4Low.tBox336BaseTTT ih
theorem core335_3 (ih : IH 3) (a b c d : Bool) :
    Comm 3 (mc 3 .box [0] (SE.ctl 3 [(1, a), (2, b)] false)) (mc 3 .box [0] (SE.ctl 3 [(1, c), (2, d)] false)) := by
  cases a <;> cases b <;> cases c <;> cases d
  · exact Low3.tLow3_335FFFF ih
  · exact Low3.tLow3_335FFFT ih
  · exact Low3.tLow3_335FFTF ih
  · exact Low3.tLow3_335FFTT ih
  · exact Low3.tLow3_335FTFF ih
  · exact Low3.tLow3_335FTFT ih
  · exact Low3.tLow3_335FTTF ih
  · exact Low3.tLow3_335FTTT ih
  · exact Low3.tLow3_335TFFF ih
  · exact Low3.tLow3_335TFFT ih
  · exact Low3.tLow3_335TFTF ih
  · exact Low3.tLow3_335TFTT ih
  · exact Low3.tLow3_335TTFF ih
  · exact Low3.tLow3_335TTFT ih
  · exact Low3.tLow3_335TTTF ih
  · exact Low3.tLow3_335TTTT ih
theorem core336_3 (ih : IH 3) (a b c d : Bool) :
    Comm 3 (mc 3 .box [0] (SE.ctl 3 [(1, a), (2, b)] false)) (mc 3 .box [1] (SE.ctl 3 [(0, c), (2, d)] false)) := by
  cases a <;> cases b <;> cases c <;> cases d
  · exact Low3.tLow3_336FFFF ih
  · exact Low3.tLow3_336FFFT ih
  · exact Low3.tLow3_336FFTF ih
  · exact Low3.tLow3_336FFTT ih
  · exact Low3.tLow3_336FTFF ih
  · exact Low3.tLow3_336FTFT ih
  · exact Low3.tLow3_336FTTF ih
  · exact Low3.tLow3_336FTTT ih
  · exact Low3.tLow3_336TFFF ih
  · exact Low3.tLow3_336TFFT ih
  · exact Low3.tLow3_336TFTF ih
  · exact Low3.tLow3_336TFTT ih
  · exact Low3.tLow3_336TTFF ih
  · exact Low3.tLow3_336TTFT ih
  · exact Low3.tLow3_336TTTF ih
  · exact Low3.tLow3_336TTTT ih
theorem core340_3 (ih : IH 3) (a b : Bool) :
    Comm 3 (mc 3 .hg [0, 1] (SE.ctl 3 [(2, a)] false)) (mc 3 .hg [0, 1] (SE.ctl 3 [(2, b)] false)) := by
  cases a <;> cases b
  · exact Low3.tLow3_340FF ih
  · exact Low3.tLow3_340FT ih
  · exact Low3.tLow3_340TF ih
  · exact Low3.tLow3_340TT ih

theorem comm335_3 (ih : IH 3) (x y : ℕ → Bool) :
    Comm 3 (mc 3 .box [0] (colOn 1 3 x)) (mc 3 .box [0] (colOn 1 3 y)) := by
  have hx : mc 3 .box [0] (colOn 1 3 x) = mc 3 .box [0] (SE.ctl 3 [(1, x 1), (2, x 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 3 .box [0] (colOn 1 3 y) = mc 3 .box [0] (SE.ctl 3 [(1, y 1), (2, y 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  exact core335_3 ih (x 1) (x 2) (y 1) (y 2)

theorem comm336_3 (ih : IH 3) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm 3 (mc 3 .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 x))) (mc 3 .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 3 y))) := by
  have hx : mc 3 .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 x)) = mc 3 .box [0] (SE.ctl 3 [(1, c₁), (2, x 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 3 .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 3 y)) = mc 3 .box [1] (SE.ctl 3 [(0, c₂), (2, y 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  exact core336_3 ih (c₁) (x 2) (c₂) (y 2)

theorem comm340_3 (ih : IH 3) (x y : ℕ → Bool) :
    Comm 3 (mc 3 .hg [0, 1] (colOn 2 3 x)) (mc 3 .hg [0, 1] (colOn 2 3 y)) := by
  have hx : mc 3 .hg [0, 1] (colOn 2 3 x) = mc 3 .hg [0, 1] (SE.ctl 3 [(2, x 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 3 .hg [0, 1] (colOn 2 3 y) = mc 3 .hg [0, 1] (SE.ctl 3 [(2, y 2)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  exact core340_3 ih (x 2) (y 2)

theorem comm335_4 (ih : IH 4) (x y : ℕ → Bool) :
    Comm 4 (mc 4 .box [0] (colOn 1 4 x)) (mc 4 .box [0] (colOn 1 4 y)) := by
  have hx : mc 4 .box [0] (colOn 1 4 x) = mc 4 .box [0] (SE.ctl 4 [(1, x 1), (2, x 2), (3, x 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 4 .box [0] (colOn 1 4 y) = mc 4 .box [0] (SE.ctl 4 [(1, y 1), (2, y 2), (3, y 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  exact core335_4 ih (x 1) (x 2) (x 3) (y 1) (y 2) (y 3)

theorem comm336_4 (ih : IH 4) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm 4 (mc 4 .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 4 x))) (mc 4 .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 4 y))) := by
  have hx : mc 4 .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 4 x)) = mc 4 .box [0] (SE.ctl 4 [(1, c₁), (2, x 2), (3, x 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  have hy : mc 4 .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 4 y)) = mc 4 .box [1] (SE.ctl 4 [(0, c₂), (2, y 2), (3, y 3)] false) := by
    apply Net.mc_congr
    intro i hi
    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]
  rw [hx, hy]
  exact core336_4 ih (c₁) (x 2) (x 3) (c₂) (y 2) (y 3)

theorem comm340_4 (ih : IH 4) (x y : ℕ → Bool) :
    Comm 4 (mc 4 .hg [0, 1] (colOn 2 4 x)) (mc 4 .hg [0, 1] (colOn 2 4 y)) := by
  have h := Comm.conj (comm335_4 ih (hgCol x) (hgCol y)) (pp_inv 1 ih)
    (u := (pp : Circ 4)) (v := pp)
  refine Comm.congr ((hg_box 0 x).trans ?_).symm ((hg_box 0 y).trans ?_).symm h <;>
    simp only [mul_assoc] <;> exact Derivable.refl _

end QCert.RealCliffordCH.Sec8.D.N13
