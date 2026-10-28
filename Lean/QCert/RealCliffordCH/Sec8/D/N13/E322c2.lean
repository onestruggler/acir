/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The letters of (268) as the words of `SmallDefs`
-/
import QCert.RealCliffordCH.Sec8.D.N13.E322l

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem cv268 (a α b β γ : Bool) :
    wc 5 5 (W0 a α β ++ [Qa b γ]) = l268 a α b β γ ∧ wc 5 5 ([Qa b γ] ++ W0 a α β) = r268 a α b β γ := by
  cases a <;> cases α <;> cases b <;> cases β <;> cases γ <;> exact ⟨rfl, rfl⟩

end QCert.RealCliffordCH.Sec8.D.N13
