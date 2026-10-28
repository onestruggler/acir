/-
Copyright (c) 2026 QCert contributors. All rights reserved.


# Appendix D.3 at width 4 (package (ii)): statements

The equations of D.3 that the chain cites, at width 4, given completeness on
three wires (`IH 4`).  Owned by package (ii) of `PLAN.md`.  The derivations are
runs of the engine `WEng` in the generated modules `W4/*.lean`
with every Boolean parameter case checked by Lean's kernel.
-/
import QCert.RealCliffordCH.Sec8.D.W4.ConjComm245
import QCert.RealCliffordCH.Sec8.D.SmallDefs
import QCert.RealCliffordCH.Sec8.D.W4.A
import QCert.RealCliffordCH.Sec8.D.W4.B1
import QCert.RealCliffordCH.Sec8.D.W4.B3
import QCert.RealCliffordCH.Sec8.D.W4.Inverse
import QCert.RealCliffordCH.Sec8.D.W4.MergeZX
import QCert.RealCliffordCH.Sec8.D.W4.Late
import QCert.RealCliffordCH.Sec8.D.W4.CommuteLate
import QCert.RealCliffordCH.Sec8.D.W4.HgLate
import QCert.RealCliffordCH.Sec8.D.W4.SameRotation
import QCert.RealCliffordCH.Sec8.D.W4.WhiteCZ
import QCert.RealCliffordCH.Sec8.D.W4.ConjRotation

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

theorem d157 (ih : IH 4) :
    Derivable (theory 4) (l157) (r157) :=
  W4.e157 ih

theorem d160 (ih : IH 4) :
    Derivable (theory 4) (l160) (r160) := by
  exact W4.e160 ih

theorem d168 (ih : IH 4) :
    Derivable (theory 4) (l168) (r168) :=
  W4.e168 ih

theorem d172 (ih : IH 4) :
    Derivable (theory 4) (l172) (r172) := by
  exact W4.e172 ih

theorem d173 (ih : IH 4) :
    Derivable (theory 4) (l173) (r173) := by
  exact W4.e173 ih

theorem d174 (ih : IH 4) :
    Derivable (theory 4) (l174) (r174) := by
  exact W4.e174 ih

theorem d209 (ih : IH 4) :
    Derivable (theory 4) (l209) (r209) := by
  exact W4.e209 ih

theorem d214 (a : Bool) (ih : IH 4) :
    Derivable (theory 4) (l214 a) (r214 a) := by
  cases a
  · exact W4.e214F ih
  · exact W4.e214T ih

theorem d215 (a : Bool) (ih : IH 4) :
    Derivable (theory 4) (l215 a) (r215 a) := by
  cases a
  · exact W4.e215F ih
  · exact W4.e215T ih

theorem d216 (ih : IH 4) :
    Derivable (theory 4) (l216) (r216) := by
  exact W4.e216 ih

theorem d217 (ih : IH 4) :
    Derivable (theory 4) (l217) (r217) := by
  exact W4.e217 ih

theorem d218 (ih : IH 4) :
    Derivable (theory 4) (l218) (r218) := by
  exact W4.e218 ih

theorem d219 (ih : IH 4) :
    Derivable (theory 4) (l219) (r219) := by
  exact W4.e219 ih

theorem d220 (ih : IH 4) :
    Derivable (theory 4) (l220) (r220) :=
  W4.e220 ih

theorem d221 (ih : IH 4) :
    Derivable (theory 4) (l221) (r221) := by
  exact W4.e221 ih

theorem d222 (ih : IH 4) :
    Derivable (theory 4) (l222) (r222) := by
  exact W4.e222 ih

theorem d223 (ih : IH 4) :
    Derivable (theory 4) (l223) (r223) := by
  exact W4.e223 ih

theorem d224 (ih : IH 4) :
    Derivable (theory 4) (l224) (r224) := by
  exact W4.e224 ih

theorem d225 (ih : IH 4) :
    Derivable (theory 4) (l225) (r225) := by
  exact W4.e225 ih

theorem d226 (ih : IH 4) :
    Derivable (theory 4) (l226) (r226) := by
  exact W4.e226 ih

theorem d227 (ih : IH 4) :
    Derivable (theory 4) (l227) (r227) := by
  exact W4.e227 ih

theorem d228 (β : Bool) (ih : IH 4) :
    Derivable (theory 4) (l228 β) (r228 β) := by
  cases β
  · exact W4.e228F ih
  · exact W4.e228T ih

theorem d229 (a : Bool) (ih : IH 4) :
    Derivable (theory 4) (l229 a) (r229 a) := by
  cases a
  · exact W4.e229F ih
  · exact W4.e229T ih

theorem d230 (ih : IH 4) :
    Derivable (theory 4) (l230) (r230) := by
  exact W4.e230 ih

theorem d231 (ih : IH 4) :
    Derivable (theory 4) (l231) (r231) := by
  exact W4.e231 ih

theorem d232 (ih : IH 4) :
    Derivable (theory 4) (l232) (r232) := by
  exact W4.e232 ih

theorem d233 (ih : IH 4) :
    Derivable (theory 4) (l233) (r233) := by
  exact W4.e233 ih

theorem d234 (ih : IH 4) :
    Derivable (theory 4) (l234) (r234) := by
  exact W4.e234 ih

theorem d235 (ih : IH 4) :
    Derivable (theory 4) (l235) (r235) := by
  exact W4.e235 ih

theorem d236 (ih : IH 4) :
    Derivable (theory 4) (l236) (r236) := by
  exact W4.e236 ih

theorem d237 (ih : IH 4) :
    Derivable (theory 4) (l237) (r237) := by
  exact W4.e237 ih

theorem d238 (ih : IH 4) :
    Derivable (theory 4) (l238) (r238) := by
  exact W4.e238 ih

theorem d239 (a : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l239 a γ) (r239 a γ) := by
  cases a <;> cases γ
  · exact W4.e239FF ih
  · exact W4.e239FT ih
  · exact W4.e239TF ih
  · exact W4.e239TT ih

theorem d240 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l240 a α b β δ γ) (r240 a α b β δ γ) := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases δ <;> cases γ
  · exact W4.e240FFFFFF ih
  · exact W4.e240FFFFFT ih
  · exact W4.e240FFFFTF ih
  · exact W4.e240FFFFTT ih
  · exact W4.e240FFFTFF ih
  · exact W4.e240FFFTFT ih
  · exact W4.e240FFFTTF ih
  · exact W4.e240FFFTTT ih
  · exact W4.e240FFTFFF ih
  · exact W4.e240FFTFFT ih
  · exact W4.e240FFTFTF ih
  · exact W4.e240FFTFTT ih
  · exact W4.e240FFTTFF ih
  · exact W4.e240FFTTFT ih
  · exact W4.e240FFTTTF ih
  · exact W4.e240FFTTTT ih
  · exact W4.e240FTFFFF ih
  · exact W4.e240FTFFFT ih
  · exact W4.e240FTFFTF ih
  · exact W4.e240FTFFTT ih
  · exact W4.e240FTFTFF ih
  · exact W4.e240FTFTFT ih
  · exact W4.e240FTFTTF ih
  · exact W4.e240FTFTTT ih
  · exact W4.e240FTTFFF ih
  · exact W4.e240FTTFFT ih
  · exact W4.e240FTTFTF ih
  · exact W4.e240FTTFTT ih
  · exact W4.e240FTTTFF ih
  · exact W4.e240FTTTFT ih
  · exact W4.e240FTTTTF ih
  · exact W4.e240FTTTTT ih
  · exact W4.e240TFFFFF ih
  · exact W4.e240TFFFFT ih
  · exact W4.e240TFFFTF ih
  · exact W4.e240TFFFTT ih
  · exact W4.e240TFFTFF ih
  · exact W4.e240TFFTFT ih
  · exact W4.e240TFFTTF ih
  · exact W4.e240TFFTTT ih
  · exact W4.e240TFTFFF ih
  · exact W4.e240TFTFFT ih
  · exact W4.e240TFTFTF ih
  · exact W4.e240TFTFTT ih
  · exact W4.e240TFTTFF ih
  · exact W4.e240TFTTFT ih
  · exact W4.e240TFTTTF ih
  · exact W4.e240TFTTTT ih
  · exact W4.e240TTFFFF ih
  · exact W4.e240TTFFFT ih
  · exact W4.e240TTFFTF ih
  · exact W4.e240TTFFTT ih
  · exact W4.e240TTFTFF ih
  · exact W4.e240TTFTFT ih
  · exact W4.e240TTFTTF ih
  · exact W4.e240TTFTTT ih
  · exact W4.e240TTTFFF ih
  · exact W4.e240TTTFFT ih
  · exact W4.e240TTTFTF ih
  · exact W4.e240TTTFTT ih
  · exact W4.e240TTTTFF ih
  · exact W4.e240TTTTFT ih
  · exact W4.e240TTTTTF ih
  · exact W4.e240TTTTTT ih

theorem d241 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l241 a α b β δ γ) (r241 a α b β δ γ) := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases δ <;> cases γ
  · exact W4.e241FFFFFF ih
  · exact W4.e241FFFFFT ih
  · exact W4.e241FFFFTF ih
  · exact W4.e241FFFFTT ih
  · exact W4.e241FFFTFF ih
  · exact W4.e241FFFTFT ih
  · exact W4.e241FFFTTF ih
  · exact W4.e241FFFTTT ih
  · exact W4.e241FFTFFF ih
  · exact W4.e241FFTFFT ih
  · exact W4.e241FFTFTF ih
  · exact W4.e241FFTFTT ih
  · exact W4.e241FFTTFF ih
  · exact W4.e241FFTTFT ih
  · exact W4.e241FFTTTF ih
  · exact W4.e241FFTTTT ih
  · exact W4.e241FTFFFF ih
  · exact W4.e241FTFFFT ih
  · exact W4.e241FTFFTF ih
  · exact W4.e241FTFFTT ih
  · exact W4.e241FTFTFF ih
  · exact W4.e241FTFTFT ih
  · exact W4.e241FTFTTF ih
  · exact W4.e241FTFTTT ih
  · exact W4.e241FTTFFF ih
  · exact W4.e241FTTFFT ih
  · exact W4.e241FTTFTF ih
  · exact W4.e241FTTFTT ih
  · exact W4.e241FTTTFF ih
  · exact W4.e241FTTTFT ih
  · exact W4.e241FTTTTF ih
  · exact W4.e241FTTTTT ih
  · exact W4.e241TFFFFF ih
  · exact W4.e241TFFFFT ih
  · exact W4.e241TFFFTF ih
  · exact W4.e241TFFFTT ih
  · exact W4.e241TFFTFF ih
  · exact W4.e241TFFTFT ih
  · exact W4.e241TFFTTF ih
  · exact W4.e241TFFTTT ih
  · exact W4.e241TFTFFF ih
  · exact W4.e241TFTFFT ih
  · exact W4.e241TFTFTF ih
  · exact W4.e241TFTFTT ih
  · exact W4.e241TFTTFF ih
  · exact W4.e241TFTTFT ih
  · exact W4.e241TFTTTF ih
  · exact W4.e241TFTTTT ih
  · exact W4.e241TTFFFF ih
  · exact W4.e241TTFFFT ih
  · exact W4.e241TTFFTF ih
  · exact W4.e241TTFFTT ih
  · exact W4.e241TTFTFF ih
  · exact W4.e241TTFTFT ih
  · exact W4.e241TTFTTF ih
  · exact W4.e241TTFTTT ih
  · exact W4.e241TTTFFF ih
  · exact W4.e241TTTFFT ih
  · exact W4.e241TTTFTF ih
  · exact W4.e241TTTFTT ih
  · exact W4.e241TTTTFF ih
  · exact W4.e241TTTTFT ih
  · exact W4.e241TTTTTF ih
  · exact W4.e241TTTTTT ih

theorem d242 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l242 a α b β δ γ) (r242 a α b β δ γ) := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases δ <;> cases γ
  · exact W4.e242FFFFFF ih
  · exact W4.e242FFFFFT ih
  · exact W4.e242FFFFTF ih
  · exact W4.e242FFFFTT ih
  · exact W4.e242FFFTFF ih
  · exact W4.e242FFFTFT ih
  · exact W4.e242FFFTTF ih
  · exact W4.e242FFFTTT ih
  · exact W4.e242FFTFFF ih
  · exact W4.e242FFTFFT ih
  · exact W4.e242FFTFTF ih
  · exact W4.e242FFTFTT ih
  · exact W4.e242FFTTFF ih
  · exact W4.e242FFTTFT ih
  · exact W4.e242FFTTTF ih
  · exact W4.e242FFTTTT ih
  · exact W4.e242FTFFFF ih
  · exact W4.e242FTFFFT ih
  · exact W4.e242FTFFTF ih
  · exact W4.e242FTFFTT ih
  · exact W4.e242FTFTFF ih
  · exact W4.e242FTFTFT ih
  · exact W4.e242FTFTTF ih
  · exact W4.e242FTFTTT ih
  · exact W4.e242FTTFFF ih
  · exact W4.e242FTTFFT ih
  · exact W4.e242FTTFTF ih
  · exact W4.e242FTTFTT ih
  · exact W4.e242FTTTFF ih
  · exact W4.e242FTTTFT ih
  · exact W4.e242FTTTTF ih
  · exact W4.e242FTTTTT ih
  · exact W4.e242TFFFFF ih
  · exact W4.e242TFFFFT ih
  · exact W4.e242TFFFTF ih
  · exact W4.e242TFFFTT ih
  · exact W4.e242TFFTFF ih
  · exact W4.e242TFFTFT ih
  · exact W4.e242TFFTTF ih
  · exact W4.e242TFFTTT ih
  · exact W4.e242TFTFFF ih
  · exact W4.e242TFTFFT ih
  · exact W4.e242TFTFTF ih
  · exact W4.e242TFTFTT ih
  · exact W4.e242TFTTFF ih
  · exact W4.e242TFTTFT ih
  · exact W4.e242TFTTTF ih
  · exact W4.e242TFTTTT ih
  · exact W4.e242TTFFFF ih
  · exact W4.e242TTFFFT ih
  · exact W4.e242TTFFTF ih
  · exact W4.e242TTFFTT ih
  · exact W4.e242TTFTFF ih
  · exact W4.e242TTFTFT ih
  · exact W4.e242TTFTTF ih
  · exact W4.e242TTFTTT ih
  · exact W4.e242TTTFFF ih
  · exact W4.e242TTTFFT ih
  · exact W4.e242TTTFTF ih
  · exact W4.e242TTTFTT ih
  · exact W4.e242TTTTFF ih
  · exact W4.e242TTTTFT ih
  · exact W4.e242TTTTTF ih
  · exact W4.e242TTTTTT ih

theorem d243 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l243 a α b β δ γ) (r243 a α b β δ γ) := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases δ <;> cases γ
  · exact W4.e243FFFFFF ih
  · exact W4.e243FFFFFT ih
  · exact W4.e243FFFFTF ih
  · exact W4.e243FFFFTT ih
  · exact W4.e243FFFTFF ih
  · exact W4.e243FFFTFT ih
  · exact W4.e243FFFTTF ih
  · exact W4.e243FFFTTT ih
  · exact W4.e243FFTFFF ih
  · exact W4.e243FFTFFT ih
  · exact W4.e243FFTFTF ih
  · exact W4.e243FFTFTT ih
  · exact W4.e243FFTTFF ih
  · exact W4.e243FFTTFT ih
  · exact W4.e243FFTTTF ih
  · exact W4.e243FFTTTT ih
  · exact W4.e243FTFFFF ih
  · exact W4.e243FTFFFT ih
  · exact W4.e243FTFFTF ih
  · exact W4.e243FTFFTT ih
  · exact W4.e243FTFTFF ih
  · exact W4.e243FTFTFT ih
  · exact W4.e243FTFTTF ih
  · exact W4.e243FTFTTT ih
  · exact W4.e243FTTFFF ih
  · exact W4.e243FTTFFT ih
  · exact W4.e243FTTFTF ih
  · exact W4.e243FTTFTT ih
  · exact W4.e243FTTTFF ih
  · exact W4.e243FTTTFT ih
  · exact W4.e243FTTTTF ih
  · exact W4.e243FTTTTT ih
  · exact W4.e243TFFFFF ih
  · exact W4.e243TFFFFT ih
  · exact W4.e243TFFFTF ih
  · exact W4.e243TFFFTT ih
  · exact W4.e243TFFTFF ih
  · exact W4.e243TFFTFT ih
  · exact W4.e243TFFTTF ih
  · exact W4.e243TFFTTT ih
  · exact W4.e243TFTFFF ih
  · exact W4.e243TFTFFT ih
  · exact W4.e243TFTFTF ih
  · exact W4.e243TFTFTT ih
  · exact W4.e243TFTTFF ih
  · exact W4.e243TFTTFT ih
  · exact W4.e243TFTTTF ih
  · exact W4.e243TFTTTT ih
  · exact W4.e243TTFFFF ih
  · exact W4.e243TTFFFT ih
  · exact W4.e243TTFFTF ih
  · exact W4.e243TTFFTT ih
  · exact W4.e243TTFTFF ih
  · exact W4.e243TTFTFT ih
  · exact W4.e243TTFTTF ih
  · exact W4.e243TTFTTT ih
  · exact W4.e243TTTFFF ih
  · exact W4.e243TTTFFT ih
  · exact W4.e243TTTFTF ih
  · exact W4.e243TTTFTT ih
  · exact W4.e243TTTTFF ih
  · exact W4.e243TTTTFT ih
  · exact W4.e243TTTTTF ih
  · exact W4.e243TTTTTT ih

theorem d244 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (ih : IH 4) :
    Derivable (theory 4) (l244 a α b β) (r244 a α b β) := by
  cases a <;> cases α <;> cases b <;> cases β
  · exact W4.e244FFFF ih
  · exact W4.e244FFFT ih
  · exact W4.e244FFTF ih
  · exact W4.e244FFTT ih
  · exact W4.e244FTFF ih
  · exact W4.e244FTFT ih
  · exact W4.e244FTTF ih
  · exact W4.e244FTTT ih
  · exact W4.e244TFFF ih
  · exact W4.e244TFFT ih
  · exact W4.e244TFTF ih
  · exact W4.e244TFTT ih
  · exact W4.e244TTFF ih
  · exact W4.e244TTFT ih
  · exact W4.e244TTTF ih
  · exact W4.e244TTTT ih

theorem d245 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (ih : IH 4) :
    Derivable (theory 4) (l245 a α b β) (r245 a α b β) := by
  cases a <;> cases α <;> cases b <;> cases β
  · exact W4.e245FFFF ih
  · exact W4.e245FFFT ih
  · exact W4.e245FFTF ih
  · exact W4.e245FFTT ih
  · exact W4.e245FTFF ih
  · exact W4.e245FTFT ih
  · exact W4.e245FTTF ih
  · exact W4.e245FTTT ih
  · exact W4.e245TFFF ih
  · exact W4.e245TFFT ih
  · exact W4.e245TFTF ih
  · exact W4.e245TFTT ih
  · exact W4.e245TTFF ih
  · exact W4.e245TTFT ih
  · exact W4.e245TTTF ih
  · exact W4.e245TTTT ih

theorem d246 (ih : IH 4) :
    Derivable (theory 4) (l246) (r246) := by
  exact W4.e246 ih

theorem d247 (a : Bool) (α : Bool) (β : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l247 a α β γ) (r247 a α β γ) := by
  cases a <;> cases α <;> cases β <;> cases γ
  · exact W4.e247FFFF ih
  · exact W4.e247FFFT ih
  · exact W4.e247FFTF ih
  · exact W4.e247FFTT ih
  · exact W4.e247FTFF ih
  · exact W4.e247FTFT ih
  · exact W4.e247FTTF ih
  · exact W4.e247FTTT ih
  · exact W4.e247TFFF ih
  · exact W4.e247TFFT ih
  · exact W4.e247TFTF ih
  · exact W4.e247TFTT ih
  · exact W4.e247TTFF ih
  · exact W4.e247TTFT ih
  · exact W4.e247TTTF ih
  · exact W4.e247TTTT ih

theorem d248 (a : Bool) (α : Bool) (β : Bool) (γ : Bool) (ih : IH 4) :
    Derivable (theory 4) (l248 a α β γ) (r248 a α β γ) := by
  cases a <;> cases α <;> cases β <;> cases γ
  · exact W4.e248FFFF ih
  · exact W4.e248FFFT ih
  · exact W4.e248FFTF ih
  · exact W4.e248FFTT ih
  · exact W4.e248FTFF ih
  · exact W4.e248FTFT ih
  · exact W4.e248FTTF ih
  · exact W4.e248FTTT ih
  · exact W4.e248TFFF ih
  · exact W4.e248TFFT ih
  · exact W4.e248TFTF ih
  · exact W4.e248TFTT ih
  · exact W4.e248TTFF ih
  · exact W4.e248TTFT ih
  · exact W4.e248TTTF ih
  · exact W4.e248TTTT ih

end QCert.RealCliffordCH.Sec8.D
