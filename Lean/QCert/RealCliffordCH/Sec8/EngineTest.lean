/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: a test of the engine

A three-wire derivation with each kind of step: a rewrite with Equation (12)
from a table, an exchange of disjoint letters, and a semantic step on a
window idle on the top wire (two-qubit completeness).  Not imported by the
development.
-/
import QCert.RealCliffordCH.Sec8.EngineN

namespace QCert.RealCliffordCH.Sec8.EngineTest

open Circuit Eng

/-- A table with Equation (12) on three wires. -/
def T3 : Tbl := [([.C 1, .C 0], [.C 0, .C 1])]

theorem T3_ok : AllD 3 T3 := by
  intro e he
  simp only [T3, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  exact derivable_rule Rule.e12 0

example (ih : IH 3) :
    Derivable (theory 3) (circW 3 [.C 1, .C 0, .Z 0, .H 2, .H 0, .H 0])
      (circW 3 [.C 0, .C 1, .H 2, .Z 0]) :=
  check_sound ih T3_ok (ss := [.rw 0 0 false, .sw 2, .sem 4 2 []]) (by decide +kernel)

/-- A semantic step on a window idle on wire 0 (the swap of wires 1, 2
around their `CZ`), backwards rewriting, on four wires. -/
example (ih : IH 4) :
    Derivable (theory 4) (circW 4 [.S 1, .C 1, .S 1, .C 2, .H 3])
      (circW 4 [.C 1, .C 2, .H 3]) :=
  check_sound ih (T := []) (fun _ h => by simp at h) (ss := [.sem 0 3 [.C 1]]) (by decide +kernel)

end QCert.RealCliffordCH.Sec8.EngineTest
