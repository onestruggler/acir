/-
Copyright (c) 2026 QCert contributors. All rights reserved.


# Appendix D.4 at width 5 (package (iii)): statements

The equations (267), (268) of D.4 at width 5, given completeness on four
wires (`IH 5`). The proof certificates cover every Boolean case.
-/
import QCert.RealCliffordCH.Sec8.D.W5.Family268

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

theorem d267 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (γ : Bool) (ih : IH 5) :
    Derivable (theory 5) (l267 a α b β γ) (r267 a α b β γ) := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases γ
  · exact W5T.e267FFFFF ih
  · exact W5T.e267FFFFT ih
  · exact W5T.e267FFFTF ih
  · exact W5T.e267FFFTT ih
  · exact W5T.e267FFTFF ih
  · exact W5T.e267FFTFT ih
  · exact W5T.e267FFTTF ih
  · exact W5T.e267FFTTT ih
  · exact W5T.e267FTFFF ih
  · exact W5T.e267FTFFT ih
  · exact W5T.e267FTFTF ih
  · exact W5T.e267FTFTT ih
  · exact W5T.e267FTTFF ih
  · exact W5T.e267FTTFT ih
  · exact W5T.e267FTTTF ih
  · exact W5T.e267FTTTT ih
  · exact W5T.e267TFFFF ih
  · exact W5T.e267TFFFT ih
  · exact W5T.e267TFFTF ih
  · exact W5T.e267TFFTT ih
  · exact W5T.e267TFTFF ih
  · exact W5T.e267TFTFT ih
  · exact W5T.e267TFTTF ih
  · exact W5T.e267TFTTT ih
  · exact W5T.e267TTFFF ih
  · exact W5T.e267TTFFT ih
  · exact W5T.e267TTFTF ih
  · exact W5T.e267TTFTT ih
  · exact W5T.e267TTTFF ih
  · exact W5T.e267TTTFT ih
  · exact W5T.e267TTTTF ih
  · exact W5T.e267TTTTT ih

theorem d268 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (γ : Bool) (ih : IH 5) :
    Derivable (theory 5) (l268 a α b β γ) (r268 a α b β γ) := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases γ
  · exact W5T.e268FFFFF ih
  · exact W5T.e268FFFFT ih
  · exact W5T.e268FFFTF ih
  · exact W5T.e268FFFTT ih
  · exact W5T.e268FFTFF ih
  · exact W5T.e268FFTFT ih
  · exact W5T.e268FFTTF ih
  · exact W5T.e268FFTTT ih
  · exact W5T.e268FTFFF ih
  · exact W5T.e268FTFFT ih
  · exact W5T.e268FTFTF ih
  · exact W5T.e268FTFTT ih
  · exact W5T.e268FTTFF ih
  · exact W5T.e268FTTFT ih
  · exact W5T.e268FTTTF ih
  · exact W5T.e268FTTTT ih
  · exact W5T.e268TFFFF ih
  · exact W5T.e268TFFFT ih
  · exact W5T.e268TFFTF ih
  · exact W5T.e268TFFTT ih
  · exact W5T.e268TFTFF ih
  · exact W5T.e268TFTFT ih
  · exact W5T.e268TFTTF ih
  · exact W5T.e268TFTTT ih
  · exact W5T.e268TTFFF ih
  · exact W5T.e268TTFFT ih
  · exact W5T.e268TTFTF ih
  · exact W5T.e268TTFTT ih
  · exact W5T.e268TTTFF ih
  · exact W5T.e268TTTFT ih
  · exact W5T.e268TTTTF ih
  · exact W5T.e268TTTTT ih

end QCert.RealCliffordCH.Sec8.D
