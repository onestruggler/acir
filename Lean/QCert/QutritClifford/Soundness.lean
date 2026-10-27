/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of the rules of Figure 1

Every rule of Figure 1 holds for the matrices of §2.1, at every width, and
every generator has an inverse modulo the rules.

The rules are decided over `ℚ(ζ)` (`QutritClifford.ops`) by evaluating
circuits on tries (`QutritClifford.Vec`).  To keep the evaluations short,
the derived gates `S'`, `SWAP`, `CX` and `XC` are first evaluated once on
their own wires, and the rules are then decided for circuits over an
extended gate set (`XGate`) in which they are single gates: `expandC`
writes an extended circuit out in the generators, and evaluation commutes
with it (`eval_expandC`).

As printed, (D6) is `-SWAP`, not `SWAP`: the circuit `(H ⊗ H) CZ (H ⊗ H) CZ
(H ⊗ H) CZ` sends `|x, y⟩` to `-|y, x⟩` (`swapX`).  The rules use the
circuit, and each uses it an even number of times or once on each side, so
they hold as printed.
-/
import QCert.QutritClifford.Semantics
import QCert.QutritClifford.Trie

namespace QCert.QutritClifford

open Matrix

/-! ### Evaluation of padded and shifted circuits -/

section EvalLemmas

variable {G : ℕ → Type} {R : Type*} [CommRing R] {d : ℕ} (O : GateOps G R d)

theorem evalShift {n : ℕ} (w : Circuit G n) :
    O.eval (n + 1) (Circuit.shift w) = onTop 1 (O.eval n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [onTop_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Circuit.shift_of, ih, map_mul (O.eval n), onTop_mul]
    rfl

theorem genPad (m : ℕ) {k : ℕ} (g : Gen G k) :
    O.gen (g.pad m) = onBottom (n := m) (O.gen g) := by
  induction g with
  | gate0 c =>
    show O.scalar c • (1 : Op R d _) = onBottom (O.scalar c • 1)
    rw [onBottom_smul, onBottom_one]
  | @gate1 n' c =>
    show onBottom (n := m + n') (O.gate1 c) = onBottom (n := m) (onBottom (n := n') (O.gate1 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @gate2 n' c =>
    show onBottom (n := m + n') (O.gate2 c) = onBottom (n := m) (onBottom (n := n') (O.gate2 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @gate3 n' c =>
    show onBottom (n := m + n') (O.gate3 c) = onBottom (n := m) (onBottom (n := n') (O.gate3 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @up n' g ih =>
    show onTop 1 (O.gen (g.pad m)) = onBottom (n := m) (onTop 1 (O.gen g))
    rw [ih]; exact (onBottom_onTop _).symm

theorem evalPad (m : ℕ) {k : ℕ} (w : Circuit G k) :
    O.eval (m + k) (Circuit.pad m w) = onBottom (n := m) (O.eval k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [onBottom_one]
  | mul_of g w ih =>
    rw [map_mul (Circuit.pad m), map_mul (O.eval _), ih, map_mul (O.eval k), onBottom_mul]
    congr 1
    exact genPad O m g

theorem evalOfGate1 (g : G 1) : O.eval 1 (FreeMonoid.of (Gen.gate1 g)) = O.gate1 g := by
  rw [GateOps.eval, FreeMonoid.lift_eval_of]
  ext s t
  show onBottom (n := 0) (O.gate1 g) s t = _
  rw [onBottom_apply', if_pos (fun i hi hk => by omega)]

theorem evalOfGate2 (g : G 2) : O.eval 2 (FreeMonoid.of (Gen.gate2 g)) = O.gate2 g := by
  rw [GateOps.eval, FreeMonoid.lift_eval_of]
  ext s t
  show onBottom (n := 0) (O.gate2 g) s t = _
  rw [onBottom_apply', if_pos (fun i hi hk => by omega)]

end EvalLemmas

/-! ### The extended gate set -/

/-- The generators and the derived gates that occur in the rules, as
single gates. -/
inductive XGate : ℕ → Type
  | negω : XGate 0
  | H : XGate 1
  | S : XGate 1
  /-- `S'` (D3). -/
  | Sp : XGate 1
  | CZ : XGate 2
  /-- The circuit (D6). -/
  | SWAP : XGate 2
  /-- `CX` (D7). -/
  | CX : XGate 2
  /-- `XC` (D8). -/
  | XC : XGate 2

/-- `S' = diag(ω, 1, ω)`. -/
def SpX : Op Q 3 1 := fun s t => if s = t then (if s 0 = 1 then 1 else ωQ) else 0

/-- The circuit (D6) is `-SWAP`: `|x, y⟩ ↦ -|y, x⟩`. -/
def swapX : Op Q 3 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then -1 else 0

/-- `CX |x, y⟩ = |x, x + y⟩`, `x` on wire 1. -/
def cxX : Op Q 3 2 := fun s t => if s 1 = t 1 ∧ s 0 = t 0 + t 1 then 1 else 0

/-- `XC |x, y⟩ = |x + y, y⟩`, `y` on wire 0. -/
def xcX : Op Q 3 2 := fun s t => if s 0 = t 0 ∧ s 1 = t 1 + t 0 then 1 else 0

/-- The matrices of the extended gates over `ℚ(ζ)`. -/
def opsX : GateOps XGate Q 3 where
  scalar
    | .negω => negωQ
  gate1
    | .H => ofMat (k := 1) HQ
    | .S => ofMat (k := 1) SQ
    | .Sp => SpX
  gate2
    | .CZ => ofMat (k := 2) CZQ
    | .SWAP => swapX
    | .CX => cxX
    | .XC => xcX
  gate3 g := nomatch g

set_option maxRecDepth 100000

theorem eval_S' : ops.eval 1 S' = SpX :=
  (Vec.eval_eq_of_cols' ops opsX (w' := FreeMonoid.of (Gen.gate1 XGate.Sp))
    (by decide +kernel)).trans (evalOfGate1 opsX XGate.Sp)

theorem eval_SWAP : ops.eval 2 SWAP = swapX :=
  (Vec.eval_eq_of_cols' ops opsX (w' := FreeMonoid.of (Gen.gate2 XGate.SWAP))
    (by decide +kernel)).trans (evalOfGate2 opsX XGate.SWAP)

theorem eval_CX : ops.eval 2 CX = cxX :=
  (Vec.eval_eq_of_cols' ops opsX (w' := FreeMonoid.of (Gen.gate2 XGate.CX))
    (by decide +kernel)).trans (evalOfGate2 opsX XGate.CX)

theorem eval_XC : ops.eval 2 XC = xcX :=
  (Vec.eval_eq_of_cols' ops opsX (w' := FreeMonoid.of (Gen.gate2 XGate.XC))
    (by decide +kernel)).trans (evalOfGate2 opsX XGate.XC)

/-! ### Circuits and extended circuits with the same evaluation -/

/-- `c` and the extended circuit `cX` have the same evaluation. -/
def Sim {n : ℕ} (c : Circ n) (cX : Circuit XGate n) : Prop := ops.eval n c = opsX.eval n cX

namespace Sim

variable {n : ℕ}

theorem one : Sim (1 : Circ n) 1 := by simp [Sim]

theorem seq {a b : Circ n} {aX bX : Circuit XGate n} (ha : Sim a aX) (hb : Sim b bX) :
    Sim (a ⨾ b) (bX * aX) := by
  simp only [Sim, seq_def, map_mul] at *; rw [ha, hb]

theorem pow {c : Circ n} {cX : Circuit XGate n} (h : Sim c cX) (k : ℕ) : Sim (c ^ k) (cX ^ k) := by
  simp only [Sim, map_pow] at *; rw [h]

theorem top {c : Circ n} {cX : Circuit XGate n} (h : Sim c cX) :
    Sim (QutritClifford.top c) (Circuit.shift cX) := by
  simp only [Sim, QutritClifford.top] at *; rw [evalShift, evalShift, h]

theorem bot {c : Circ 1} {cX : Circuit XGate 1} (h : Sim c cX) :
    Sim (QutritClifford.bot (n := n) c) (Circuit.pad n cX) := by
  simp only [Sim, QutritClifford.bot] at *; rw [evalPad, evalPad, h]

theorem bot2 {c : Circ 2} {cX : Circuit XGate 2} (h : Sim c cX) :
    Sim (QutritClifford.bot2 (n := n) c) (Circuit.pad n cX) := by
  simp only [Sim, QutritClifford.bot2] at *; rw [evalPad, evalPad, h]

theorem negω : Sim (QutritClifford.negω : Circ n) (FreeMonoid.of (Gen.gate0 XGate.negω)) := by
  simp only [Sim, QutritClifford.negω, Circuit.g0, GateOps.eval, FreeMonoid.lift_eval_of]; rfl

theorem H : Sim QutritClifford.H (FreeMonoid.of (Gen.gate1 XGate.H)) := by
  simp only [Sim, QutritClifford.H, Circuit.g1]; rw [evalOfGate1, evalOfGate1]; rfl

theorem S : Sim QutritClifford.S (FreeMonoid.of (Gen.gate1 XGate.S)) := by
  simp only [Sim, QutritClifford.S, Circuit.g1]; rw [evalOfGate1, evalOfGate1]; rfl

theorem Sp : Sim S' (FreeMonoid.of (Gen.gate1 XGate.Sp)) := by
  simp only [Sim]; rw [eval_S', evalOfGate1]; rfl

theorem CZ : Sim QutritClifford.CZ (FreeMonoid.of (Gen.gate2 XGate.CZ)) := by
  simp only [Sim, QutritClifford.CZ, Circuit.g2]; rw [evalOfGate2, evalOfGate2]; rfl

theorem SWAP : Sim QutritClifford.SWAP (FreeMonoid.of (Gen.gate2 XGate.SWAP)) := by
  simp only [Sim]; rw [eval_SWAP, evalOfGate2]; rfl

theorem CX : Sim QutritClifford.CX (FreeMonoid.of (Gen.gate2 XGate.CX)) := by
  simp only [Sim]; rw [eval_CX, evalOfGate2]; rfl

theorem XC : Sim QutritClifford.XC (FreeMonoid.of (Gen.gate2 XGate.XC)) := by
  simp only [Sim]; rw [eval_XC, evalOfGate2]; rfl

/-- Two circuits simulated by extended circuits that send every basis vector
to the same trie evaluate alike. -/
theorem eval_eq {w v : Circ n} {wX vX : Circuit XGate n} (hw : Sim w wX) (hv : Sim v vX)
    (h : ∀ t ∈ Vec.allStates n, Vec.actW opsX wX (Vec.basis t) = Vec.actW opsX vX (Vec.basis t)) :
    ops.eval n w = ops.eval n v := by
  rw [hw, hv]; exact Vec.eval_eq_of_cols opsX h

end Sim

/-! ### Soundness -/

/-- (C1) over `ℚ(ζ)`. -/
theorem eval_C1 : ops.eval 0 (negω ^ 6) = ops.eval 0 (1) :=
  Sim.eval_eq
    (Sim.negω.pow 6)
    Sim.one
    (by decide +kernel)

/-- (C2) over `ℚ(ζ)`. -/
theorem eval_C2 : ops.eval 1 (H ^ 4) = ops.eval 1 (1) :=
  Sim.eval_eq
    (Sim.H.pow 4)
    Sim.one
    (by decide +kernel)

/-- (C3) over `ℚ(ζ)`. -/
theorem eval_C3 : ops.eval 1 (S ^ 3) = ops.eval 1 (1) :=
  Sim.eval_eq
    (Sim.S.pow 3)
    Sim.one
    (by decide +kernel)

/-- (C4) over `ℚ(ζ)`. -/
theorem eval_C4 : ops.eval 1 (S ^ 2 ⨾ H ⨾ S ^ 2 ⨾ H ⨾ S ^ 2 ⨾ H) = ops.eval 1 (negω) :=
  Sim.eval_eq
    ((((((Sim.S.pow 2).seq Sim.H).seq (Sim.S.pow 2)).seq Sim.H).seq (Sim.S.pow 2)).seq Sim.H)
    Sim.negω
    (by decide +kernel)

/-- (C5) over `ℚ(ζ)`. -/
theorem eval_C5 : ops.eval 1 (S ⨾ S') = ops.eval 1 (S' ⨾ S) :=
  Sim.eval_eq
    (Sim.S.seq Sim.Sp)
    (Sim.Sp.seq Sim.S)
    (by decide +kernel)

/-- (C6) over `ℚ(ζ)`. -/
theorem eval_C6 : ops.eval 2 (CZ ^ 3) = ops.eval 2 (1) :=
  Sim.eval_eq
    (Sim.CZ.pow 3)
    Sim.one
    (by decide +kernel)

/-- (C7) over `ℚ(ζ)`. -/
theorem eval_C7 : ops.eval 2 (SWAP ^ 2) = ops.eval 2 (1) :=
  Sim.eval_eq
    (Sim.SWAP.pow 2)
    Sim.one
    (by decide +kernel)

/-- (C8) over `ℚ(ζ)`. -/
theorem eval_C8 : ops.eval 2 (top S ⨾ CZ) = ops.eval 2 (CZ ⨾ top S) :=
  Sim.eval_eq
    (Sim.S.top.seq Sim.CZ)
    (Sim.CZ.seq Sim.S.top)
    (by decide +kernel)

/-- (C9) over `ℚ(ζ)`. -/
theorem eval_C9 : ops.eval 2 (top (H ^ 2) ⨾ CZ ⨾ CZ) = ops.eval 2 (CZ ⨾ top (H ^ 2)) :=
  Sim.eval_eq
    (((Sim.H.pow 2).top.seq Sim.CZ).seq Sim.CZ)
    (Sim.CZ.seq (Sim.H.pow 2).top)
    (by decide +kernel)

/-- (C10) over `ℚ(ζ)`. -/
theorem eval_C10 : ops.eval 2 (top S ⨾ SWAP) = ops.eval 2 (SWAP ⨾ bot S) :=
  Sim.eval_eq
    (Sim.S.top.seq Sim.SWAP)
    (Sim.SWAP.seq Sim.S.bot)
    (by decide +kernel)

/-- (C11) over `ℚ(ζ)`. -/
theorem eval_C11 : ops.eval 2 (top H ⨾ SWAP) = ops.eval 2 (SWAP ⨾ bot H) :=
  Sim.eval_eq
    (Sim.H.top.seq Sim.SWAP)
    (Sim.SWAP.seq Sim.H.bot)
    (by decide +kernel)

/-- (C12) over `ℚ(ζ)`. -/
theorem eval_C12 : ops.eval 2 (CZ ⨾ SWAP) = ops.eval 2 (SWAP ⨾ CZ) :=
  Sim.eval_eq
    (Sim.CZ.seq Sim.SWAP)
    (Sim.SWAP.seq Sim.CZ)
    (by decide +kernel)

/-- (C13) over `ℚ(ζ)`. -/
theorem eval_C13 : ops.eval 2 (top S ⨾ XC) = ops.eval 2 (XC ⨾ CZ ⨾ top S ⨾ bot S' ⨾ ω ^ 2) :=
  Sim.eval_eq
    (Sim.S.top.seq Sim.XC)
    ((((Sim.XC.seq Sim.CZ).seq Sim.S.top).seq Sim.Sp.bot).seq ((Sim.negω.pow 4).pow 2))
    (by decide +kernel)

/-- (C14) over `ℚ(ζ)`. -/
theorem eval_C14 : ops.eval 2 (CZ ⨾ XC) = ops.eval 2 (XC ⨾ CZ ⨾ bot S' ⨾ bot S ⨾ ω) :=
  Sim.eval_eq
    (Sim.CZ.seq Sim.XC)
    ((((Sim.XC.seq Sim.CZ).seq Sim.Sp.bot).seq Sim.S.bot).seq (Sim.negω.pow 4))
    (by decide +kernel)

/-- (C15) over `ℚ(ζ)`. -/
theorem eval_C15 : ops.eval 3 (CZ₀₁ ⨾ CZ₁₂) = ops.eval 3 (CZ₁₂ ⨾ CZ₀₁) :=
  Sim.eval_eq
    (Sim.CZ.bot2.seq Sim.CZ.top)
    (Sim.CZ.top.seq Sim.CZ.bot2)
    (by decide +kernel)

/-- (C16) over `ℚ(ζ)`. -/
theorem eval_C16 : ops.eval 3 (SWAP₁₂ ⨾ SWAP₀₁ ⨾ SWAP₁₂) = ops.eval 3 (SWAP₀₁ ⨾ SWAP₁₂ ⨾ SWAP₀₁) :=
  Sim.eval_eq
    ((Sim.SWAP.top.seq Sim.SWAP.bot2).seq Sim.SWAP.top)
    ((Sim.SWAP.bot2.seq Sim.SWAP.top).seq Sim.SWAP.bot2)
    (by decide +kernel)

/-- (C17) over `ℚ(ζ)`. -/
theorem eval_C17 : ops.eval 3 (CZ₀₁ ⨾ SWAP₁₂ ⨾ SWAP₀₁) = ops.eval 3 (SWAP₁₂ ⨾ SWAP₀₁ ⨾ CZ₁₂) :=
  Sim.eval_eq
    ((Sim.CZ.bot2.seq Sim.SWAP.top).seq Sim.SWAP.bot2)
    ((Sim.SWAP.top.seq Sim.SWAP.bot2).seq Sim.CZ.top)
    (by decide +kernel)

/-- (C18) over `ℚ(ζ)`. -/
theorem eval_C18 : ops.eval 3 (CX₂₁ ⨾ CZ₀₁) = ops.eval 3 (CZ₀₁ ⨾ CX₂₁ ⨾ CZ₀₂) :=
  Sim.eval_eq
    (Sim.CX.top.seq Sim.CZ.bot2)
    ((Sim.CZ.bot2.seq Sim.CX.top).seq ((Sim.SWAP.bot2.seq Sim.CZ.top).seq Sim.SWAP.bot2))
    (by decide +kernel)

/-- Every rule holds over `ℚ(ζ)`. -/
theorem rule_eval {k : ℕ} {w v : Circ k} (h : Rule k w v) : ops.eval k w = ops.eval k v := by
  cases h
  exacts [eval_C1, eval_C2, eval_C3, eval_C4, eval_C5, eval_C6, eval_C7, eval_C8, eval_C9,
    eval_C10, eval_C11, eval_C12, eval_C13, eval_C14, eval_C15, eval_C16, eval_C17, eval_C18]

/-- Every rule of Figure 1 holds for the matrices of §2.1. -/
theorem rule_sound {k : ℕ} {w v : Circ k} (h : Rule k w v) : sem k w = sem k v :=
  gateSem.sem_eq_of_eval toC ops toOps_eq (rule_eval h)

/-- The rules and the structural rules hold at every width. -/
theorem theory_sound {n : ℕ} {w v : Circ n} (h : Theory n w v) : sem n w = sem n v :=
  gateSem.lift_sound (gateSem.padded_sound fun _ _ _ h => rule_sound h) n w v h

/-- Soundness: derivably equal circuits have the same operator. -/
theorem sound {n : ℕ} {w v : Circ n} (h : Derives (Padded Rule) n w v) : sem n w = sem n v :=
  derivable_sound (fun _ _ h => theory_sound h) h

/-! ### Inverses -/

theorem derives_shift {n : ℕ} {w v : Circ n} (h : Derives (Padded Rule) n w v) :
    Derives (Padded Rule) (n + 1) (Circuit.shift w) (Circuit.shift v) := by
  have : conGen (Theory n) ≤ (conGen (Theory (n + 1))).comap Circuit.shift (map_mul _) :=
    Con.conGen_le fun a b hab => ConGen.Rel.of _ _ (Lift.shift hab)
  exact this h

theorem derives_rule {n k : ℕ} {w v : Circ k} (h : Rule k w v) :
    Derives (Padded Rule) (n + k) (Circuit.pad n w) (Circuit.pad n v) :=
  Derivable.of (Lift.rule (Padded.pad n h))

/-- Every generator has an inverse modulo the rules: `(-ω)⁵`, `H³`, `S²`,
`CZ²`, by (C1), (C2), (C3), (C6), shifted up as needed. -/
theorem exists_inverse : {n : ℕ} → (g : Gen Gate n) →
    ∃ w, Derives (Padded Rule) n (w * FreeMonoid.of g) 1
  | n, .gate0 .negω => ⟨FreeMonoid.of (Gen.gate0 Gate.negω) ^ 5, by
      rw [← pow_succ]; exact derives_rule (n := n) Rule.C1⟩
  | n + 1, .gate1 .H => ⟨FreeMonoid.of (Gen.gate1 Gate.H) ^ 3, by
      rw [← pow_succ]; exact derives_rule (n := n) Rule.C2⟩
  | n + 1, .gate1 .S => ⟨FreeMonoid.of (Gen.gate1 Gate.S) ^ 2, by
      rw [← pow_succ]; exact derives_rule (n := n) Rule.C3⟩
  | n + 2, .gate2 .CZ => ⟨FreeMonoid.of (Gen.gate2 Gate.CZ) ^ 2, by
      rw [← pow_succ]; exact derives_rule (n := n) Rule.C6⟩
  | _, .gate3 g => nomatch g
  | _, .up g => by
    obtain ⟨w, hw⟩ := exists_inverse g
    refine ⟨Circuit.shift w, ?_⟩
    have := derives_shift hw
    rwa [map_mul, map_one, Circuit.shift_of] at this

/-- Every generator has an inverse modulo the rules. -/
theorem grouplike (n : ℕ) : Grouplike (Theory n) := fun g => exists_inverse g

end QCert.QutritClifford
