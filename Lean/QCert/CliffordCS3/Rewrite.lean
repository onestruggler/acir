/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checked rewriting for three-qubit Clifford+CS

The finite rules of Figure 2 and arbitrary checked equations on an adjacent
pair of qubits are replayed by the generic kernel-checked certificate engine.
The latter equations use the independently proved two-qubit completeness
theorem; they do not assume the unfinished three-qubit theorem.
-/
import QCert.CliffordCS3.Two.Completeness
import QCert.CliffordT2.FastRewrite

namespace QCert.CliffordCS3

/-- The nine generators as nonzero hexadecimal digits, in declaration order. -/
def gcode3 : Gen → ℕ
  | .i => 1 | .K₀ => 2 | .K₁ => 3 | .K₂ => 4
  | .S₀ => 5 | .S₁ => 6 | .S₂ => 7 | .CS₀₁ => 8 | .CS₁₂ => 9

theorem gcode3_bounds : ∀ a, 0 < gcode3 a ∧ gcode3 a < 16 := by decide

theorem gcode3_inj : Function.Injective gcode3 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

namespace Replay

/-- A defining relation, packaged as a rewriting rule. -/
def ax {w v : Word Gen} (h : Rel w v) : Rule Rel :=
  Rule.ofDerivable w v (Derivable.of h)

/--
Figure 2's rules in a fixed order for external certificate search:
0: C1; 1–9: C2–C4 (qubits 0,1,2); 10–23: C5–C11 (pairs 0,1);
24–29: C12–C17; 30–37: scalar commutations; 38–49: disjoint local gates
(K/K, K/S, S/K, S/S, each on pairs 01,02,12); 50–53: the two disjoint
local/CS commutations, K then S.
-/
def baseRules : List (Rule Rel) :=
  [ax Rel.c1,
   ax (Rel.c2 0),
   ax (Rel.c2 1),
   ax (Rel.c2 2),
   ax (Rel.c3 0),
   ax (Rel.c3 1),
   ax (Rel.c3 2),
   ax (Rel.c4 0),
   ax (Rel.c4 1),
   ax (Rel.c4 2),
   ax (Rel.c5 0),
   ax (Rel.c5 1),
   ax (Rel.c6 0),
   ax (Rel.c6 1),
   ax (Rel.c7 0),
   ax (Rel.c7 1),
   ax (Rel.c8 0),
   ax (Rel.c8 1),
   ax (Rel.c9 0),
   ax (Rel.c9 1),
   ax (Rel.c10 0),
   ax (Rel.c10 1),
   ax (Rel.c11 0),
   ax (Rel.c11 1),
   ax Rel.c12,
   ax Rel.c13,
   ax Rel.c14,
   ax Rel.c15,
   ax Rel.c16,
   ax Rel.c17,
   ax (Rel.comm_i Gen.K₀ (by decide)),
   ax (Rel.comm_i Gen.K₁ (by decide)),
   ax (Rel.comm_i Gen.K₂ (by decide)),
   ax (Rel.comm_i Gen.S₀ (by decide)),
   ax (Rel.comm_i Gen.S₁ (by decide)),
   ax (Rel.comm_i Gen.S₂ (by decide)),
   ax (Rel.comm_i Gen.CS₀₁ (by decide)),
   ax (Rel.comm_i Gen.CS₁₂ (by decide)),
   ax (Rel.comm_loc Local.K Local.K 0 1 (by decide)),
   ax (Rel.comm_loc Local.K Local.K 0 2 (by decide)),
   ax (Rel.comm_loc Local.K Local.K 1 2 (by decide)),
   ax (Rel.comm_loc Local.K Local.S 0 1 (by decide)),
   ax (Rel.comm_loc Local.K Local.S 0 2 (by decide)),
   ax (Rel.comm_loc Local.K Local.S 1 2 (by decide)),
   ax (Rel.comm_loc Local.S Local.K 0 1 (by decide)),
   ax (Rel.comm_loc Local.S Local.K 0 2 (by decide)),
   ax (Rel.comm_loc Local.S Local.K 1 2 (by decide)),
   ax (Rel.comm_loc Local.S Local.S 0 1 (by decide)),
   ax (Rel.comm_loc Local.S Local.S 0 2 (by decide)),
   ax (Rel.comm_loc Local.S Local.S 1 2 (by decide)),
   ax (Rel.comm_0_12 Local.K),
   ax (Rel.comm_0_12 Local.S),
   ax (Rel.comm_2_01 Local.K),
   ax (Rel.comm_2_01 Local.S)]

/-- A matrix equality on an adjacent pair, using its completed presentation. -/
def pairRule (j : Fin 2) (u v : List Two.Gen2)
    (h : Two.check2 (FreeMonoid.ofList u) (FreeMonoid.ofList v) = true) : Rule Rel :=
  Rule.ofDerivable (Two.embW j (FreeMonoid.ofList u))
    (Two.embW j (FreeMonoid.ofList v))
    (Two.derivable_embed j (Two.derivable_of_check2 h))

/-- Replay a certificate against any finite collection of proved rules. -/
def byChunks (rules : List (Rule Rel)) (l r : List Gen) (cs : List (ℕ × ℕ))
    (h : runChunks (compileRules gcode3 rules) cs (enc gcode3 l) =
      some (enc gcode3 r)) : Rule Rel :=
  Rule.byChunks gcode3_bounds gcode3_inj rules l r cs h

/-- A word equation certified by the same replay. -/
theorem derive (rules : List (Rule Rel)) (w v : Word Gen) (cs : List (ℕ × ℕ))
    (h : runChunks (compileRules gcode3 rules) cs (enc gcode3 w.toList) =
      some (enc gcode3 v.toList)) : Derivable Rel w v :=
  derivable_of_chunks gcode3_bounds gcode3_inj rules w v cs h

end Replay
end QCert.CliffordCS3

