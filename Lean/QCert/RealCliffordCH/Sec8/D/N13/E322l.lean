/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (267), (268) as engine entries

The five-wire equations (267), (268) of Appendix D.4 (`W5.d267`, `d268`),
written with the letters of the engine on five local wires and carried to
every width: `P ⊗ P` on the wires `0, 1` around the triply controlled
rotation `(-1)^a ZX` on wire `0` (`W0`), against the rotation `(-1)^b XZ`
with target `1` (`Qb`, (267)) or `0` (`Qa`, (268)) controlled by the wires
`4` (black), `2` (white) and `0`, resp. `1` (colour `γ`).  The same with the
rotation of `W0` on wire `1` (`W1`) follows by the swap of the wires `0, 1`
(`e267s`, `e268s`).
-/
import QCert.RealCliffordCH.Sec8.D.N13.Loc
import QCert.RealCliffordCH.Sec8.D.W5

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-! ## The letters -/

/-- `P ⊗ P` on the wires `0, 1`. -/
def ppL : List Lt := [.s (.K 0), .s (.H 1), .s (.Z 0), .s (.K 0), .s (.H 1), .s (.Z 0), .s (.K 0),
  .s (.H 1), .s (.Z 0), .s (.S 0)]
/-- `(-1)^a ZX` on wire `0`, controls `1` (colour `β`), `2` (black), `3` (colour `α`). -/
def R0 (a α β : Bool) : Lt := .g (Kind.sgnZX a) [0] [(1, β), (2, true), (3, α)] false
/-- The same on wire `1`, control `0` of colour `β`. -/
def R1 (a α β : Bool) : Lt := .g (Kind.sgnZX a) [1] [(0, β), (2, true), (3, α)] false
def W0 (a α β : Bool) : List Lt := ppL ++ [R0 a α β] ++ ppL
def W1 (a α β : Bool) : List Lt := ppL ++ [R1 a α β] ++ ppL
/-- `(-1)^b XZ` on wire `0`, controls `1` (colour `γ`), `2` (white), `4` (black). -/
def Qa (b γ : Bool) : Lt := .g (Kind.sgnZX (!b)) [0] [(1, γ), (2, false), (4, true)] false
/-- The same on wire `1`, control `0` of colour `γ`. -/
def Qb (b γ : Bool) : Lt := .g (Kind.sgnZX (!b)) [1] [(0, γ), (2, false), (4, true)] false

end QCert.RealCliffordCH.Sec8.D.N13
