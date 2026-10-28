/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.5 at every width: the first schemas

Runs of the engine `SymEngine` for the first equations of Lemma D.8, given
the placement hypothesis `Frame`.
-/
import QCert.RealCliffordCH.Sec8.D.EngineFrame

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE

/-- The box on wire `1` with controls `2, 3, 4` and the bulk (wire `0` idle). -/
def B1 : Lt := .g .box [1] [(2, true), (3, true), (4, true)] true
def W' : Lt := .g .zx [1] [(2, true), (3, true)] false
def V' : Lt := .g .xz [1] [(2, true), (3, true)] false
def C' : Lt := .g .box [2] [(1, true), (4, true)] true
/-- `CZ` between wires `0` and `2`. -/
def cz02 : List Lt := [.s (.S 1), .s (.C 0), .s (.S 1)]

theorem run271 : check 4 [] (cz02 ++ [B1]) ([B1] ++ cz02)
    [.sem 3 1 [W', C', V', C'] 0, .sem 0 4 ([W'] ++ cz02) 4, .sem 1 4 ([C'] ++ cz02) 3,
     .sem 2 4 ([V'] ++ cz02) 4, .sem 3 4 ([C'] ++ cz02) 3, .sem 0 4 [B1] 0] = true := by
  decide +kernel

/-- (271), five local wires: `CZ` between wires `0` and `2` commutes with the
box on wire `1` (controls `2, 3, 4` and the bulk; wire `0` idle). -/
theorem eq271_wc (m : ℕ) (ih : IH (m + 4 + 1)) :
    Derivable (theory (m + 4 + 1)) (wc 5 (m + 4 + 1) (cz02 ++ [B1])) (wc 5 (m + 4 + 1) ([B1] ++ cz02)) :=
  check_sound (frame 4) ih (T := []) (fun _ h => by simp at h) run271

end QCert.RealCliffordCH.Sec8.D.N8
