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
import QCert.RealCliffordCH.Sec8.D.N13.E322c1
import QCert.RealCliffordCH.Sec8.D.N13.E322c2

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

theorem loc267 (a α b β γ : Bool) : (W0 a α β ++ [Qb b γ]).all (isLoc 5) = true ∧
    ([Qb b γ] ++ W0 a α β).all (isLoc 5) = true ∧ (W0 a α β ++ [Qa b γ]).all (isLoc 5) = true ∧
    ([Qa b γ] ++ W0 a α β).all (isLoc 5) = true := by
  revert a α b β γ; decide

/-- (267) at every width from five. -/
theorem e267 (m : ℕ) (ih : IH (m + 5)) (a α b β γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (W0 a α β ++ [Qb b γ]))
      (wc 5 (m + 5) ([Qb b γ] ++ W0 a α β)) := by
  have d := d267 a α b β γ (ih.mono (by omega))
  rw [← (cv267 a α b β γ).1, ← (cv267 a α b β γ).2] at d
  exact der_loc (loc267 a α b β γ).1 (loc267 a α b β γ).2.1 d (m + 5) (by omega)

/-- (268) at every width from five. -/
theorem e268 (m : ℕ) (ih : IH (m + 5)) (a α b β γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (W0 a α β ++ [Qa b γ]))
      (wc 5 (m + 5) ([Qa b γ] ++ W0 a α β)) := by
  have d := d268 a α b β γ (ih.mono (by omega))
  rw [← (cv268 a α b β γ).1, ← (cv268 a α b β γ).2] at d
  exact der_loc (loc267 a α b β γ).2.2.1 (loc267 a α b β γ).2.2.2 d (m + 5) (by omega)

/-! ## The rotation on wire `1`: the swap of the wires `0, 1` -/

/-- The run carrying an entry for `W0` and `q0` to `W1` and `q`. -/
def swRun : List St :=
  [.rw 10 1 true, .rw 23 2 true, .sem 0 11 ([.s (.S 0)] ++ ppL) 2, .sem 12 12 ppL 2, .rw 1 0 false,
   .sem 2 10 ([.s (.S 0)] ++ ppL ++ [.s (.S 0)]) 2, .sem 15 11 ([.s (.S 0)] ++ ppL) 2, .rw 0 2 false,
   .rw 11 1 false]

def swTbl (a α β : Bool) (q0 q : Lt) : SE.Tbl :=
  [(W0 a α β ++ [q0], [q0] ++ W0 a α β), ([.s (.S 0), R0 a α β, .s (.S 0)], [R1 a α β]),
   ([.s (.S 0), q0, .s (.S 0)], [q])]

theorem chkSwA : ∀ a α β b γ : Bool,
    check 4 (swTbl a α β (Qb b γ) (Qa b γ)) (W1 a α β ++ [Qa b γ]) ([Qa b γ] ++ W1 a α β) swRun = true ∧
    check 4 (swTbl a α β (Qa b γ) (Qb b γ)) (W1 a α β ++ [Qb b γ]) ([Qb b γ] ++ W1 a α β) swRun = true := by
  decide +kernel

theorem swE_R (m : ℕ) (a α β : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.S 0), R0 a α β, .s (.S 0)]) (wc 5 (m + 5) [R1 a α β]) := by
  have h := swapE m 5 0 (by omega) (Kind.sgnZX a) [0] [(1, β), (2, true), (3, α)] false
    (by cases a <;> cases α <;> cases β <;> decide) (by simp)
  exact h

theorem swE_Qb (m : ℕ) (b γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.S 0), Qb b γ, .s (.S 0)]) (wc 5 (m + 5) [Qa b γ]) := by
  have h := swapE m 5 0 (by omega) (Kind.sgnZX (!b)) [1] [(0, γ), (2, false), (4, true)] false
    (by cases b <;> cases γ <;> decide) (by simp)
  exact h

theorem swE_Qa (m : ℕ) (b γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) [.s (.S 0), Qa b γ, .s (.S 0)]) (wc 5 (m + 5) [Qb b γ]) := by
  have h := swapE m 5 0 (by omega) (Kind.sgnZX (!b)) [0] [(1, γ), (2, false), (4, true)] false
    (by cases b <;> cases γ <;> decide) (by simp)
  exact h

/-- (267) with the rotation of `P ⊗ P` on wire `1`. -/
theorem e267s (m : ℕ) (ih : IH (m + 5)) (a α b β γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (W1 a α β ++ [Qa b γ]))
      (wc 5 (m + 5) ([Qa b γ] ++ W1 a α β)) := by
  refine check_sound (frame 4) ih (T := swTbl a α β (Qb b γ) (Qa b γ)) ?_ (chkSwA a α β b γ).1
  intro e he
  simp only [swTbl, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact e267 m ih a α b β γ
  · exact swE_R m a α β
  · exact swE_Qb m b γ

/-- (268) with the rotation of `P ⊗ P` on wire `1`. -/
theorem e268s (m : ℕ) (ih : IH (m + 5)) (a α b β γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (W1 a α β ++ [Qb b γ]))
      (wc 5 (m + 5) ([Qb b γ] ++ W1 a α β)) := by
  refine check_sound (frame 4) ih (T := swTbl a α β (Qa b γ) (Qb b γ)) ?_ (chkSwA a α β b γ).2
  intro e he
  simp only [swTbl, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact e268 m ih a α b β γ
  · exact swE_R m a α β
  · exact swE_Qa m b γ

end QCert.RealCliffordCH.Sec8.D.N13
