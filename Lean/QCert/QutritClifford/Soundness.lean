/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of the rules of Figure 1

Every rule of Figure 1 holds for the matrices of §2.1, at every width, and
every generator has an inverse modulo the rules.

The rules are decided by evaluating circuits on tries
(`QutritClifford.Vec`) over `ℤ[ω]` (`QutritClifford.Zω`), with the
Hadamard gate scaled by `c = ω² - ω` so that every entry is an Eisenstein
integer: two circuits with `h` and `h'` Hadamard gates have the same
matrix when their scaled evaluations, multiplied by `c^{h'}` and `c^h`,
send every basis vector to the same trie (`checkZ`, `evalX_eq`).  To keep
the evaluations short, the derived gates `S'`, `SWAP`, `CX` and `XC` are
first evaluated once on their own wires, and the rules are then decided
for circuits over an extended gate set (`XGate`) in which they are single
gates (`Sim`), each gate acting on a trie directly (`TrieZ.lean`).

As printed, (D6) is `-SWAP`, not `SWAP`: the circuit `(H ⊗ H) CZ (H ⊗ H) CZ
(H ⊗ H) CZ` sends `|x, y⟩` to `-|y, x⟩` (`swapX`).  The rules use the
circuit, and each uses it an even number of times or once on each side, so
they hold as printed.
-/
import QCert.QutritClifford.Semantics
import QCert.QutritClifford.Trie
import QCert.QutritClifford.TrieZ

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

/-! ### The extended gates over `ℤ[ω]`, acting on tries -/

open Zω Vec

/-- The matrices of the extended gates over `ℤ[ω]`, `H` scaled by `c`. -/
def opsZ : GateOps XGate Zω 3 where
  scalar
    | .negω => Zω.negω
  gate1
    | .H => HZ
    | .S => SZ
    | .Sp => SpZ
  gate2
    | .CZ => CZZ
    | .SWAP => swapZ
    | .CX => cxZ
    | .XC => xcZ
  gate3 g := nomatch g

/-- A generator applied to a trie, each gate by its direct action. -/
def actZ : {n : ℕ} → Gen XGate n → Vec Zω n → Vec Zω n
  | _, .gate0 .negω, v => mulNegω v
  | _, .gate1 .H, v => actH v
  | _, .gate1 .S, v => actS v
  | _, .gate1 .Sp, v => actSp v
  | _, .gate2 .CZ, v => actCZ v
  | _, .gate2 .SWAP, v => actSWAP v
  | _, .gate2 .CX, v => actCX v
  | _, .gate2 .XC, v => actXC v
  | _, .gate3 g, _ => nomatch g
  | _, .up g, node a b c => node (actZ g a) (actZ g b) (actZ g c)

theorem actZ_eq : ∀ {n : ℕ} (g : Gen XGate n) (v : Vec Zω n), actZ g v = act opsZ g v
  | _, .gate0 .negω, v => (smul_negω v).symm
  | _, .gate1 .H, v => actH_eq v
  | _, .gate1 .S, v => actS_eq v
  | _, .gate1 .Sp, v => actSp_eq v
  | _, .gate2 .CZ, v => actCZ_eq v
  | _, .gate2 .SWAP, v => actSWAP_eq v
  | _, .gate2 .CX, v => actCX_eq v
  | _, .gate2 .XC, v => actXC_eq v
  | _, .gate3 g, _ => nomatch g
  | _, .up g, node a b c => by
    simp only [actZ, act, actZ_eq g]

/-- A circuit applied to a trie, in operator order, by the direct actions. -/
def actWZ {n : ℕ} (w : Circuit XGate n) (v : Vec Zω n) : Vec Zω n := w.toList.foldr actZ v

theorem actWZ_eq {n : ℕ} (w : Circuit XGate n) (v : Vec Zω n) : actWZ w v = actW opsZ w v := by
  have : @actZ n = act opsZ := funext fun g => funext fun v => actZ_eq g v
  rw [actWZ, actW, this]

/-- The number of Hadamard gates of a generator. -/
def wtX : {n : ℕ} → Gen XGate n → ℕ
  | _, .gate1 .H => 1
  | _, .up g => wtX g
  | _, _ => 0

/-- The number of Hadamard gates of a circuit. -/
def hcount {n : ℕ} (w : Circuit XGate n) : ℕ := ((FreeMonoid.toList w).map wtX).sum

/-- `w` and `v`, scaled by `c` to the number of Hadamard gates of the other,
send every basis vector to the same trie. -/
def checkZ {n : ℕ} (w v : Circuit XGate n) : Bool :=
  (allStates n).all fun t =>
    beq (smul (c ^ hcount v) (actWZ w (basis t))) (smul (c ^ hcount w) (actWZ v (basis t)))

theorem HZ_map : HZ.map toQ = toQ c • ofMat (k := 1) HQ := op_ext_of_all (by decide +kernel)
theorem SZ_map : SZ.map toQ = ofMat (k := 1) SQ := op_ext_of_all (by decide +kernel)
theorem SpZ_map : SpZ.map toQ = SpX := op_ext_of_all (by decide +kernel)
theorem CZZ_map : CZZ.map toQ = ofMat (k := 2) CZQ := op_ext_of_all (by decide +kernel)
theorem swapZ_map : swapZ.map toQ = swapX := op_ext_of_all (by decide +kernel)
theorem cxZ_map : cxZ.map toQ = cxX := op_ext_of_all (by decide +kernel)
theorem xcZ_map : xcZ.map toQ = xcX := op_ext_of_all (by decide +kernel)

/-- Each extended gate over `ℤ[ω]`, read in `ℚ(ζ)`, is the gate times `c`
to its number of Hadamards. -/
theorem opsZ_gen {n : ℕ} (g : Gen XGate n) :
    (opsZ.map toQ).gen g = toQ c ^ wtX g • opsX.gen g := by
  induction g with
  | gate0 g =>
    cases g
    show toQ Zω.negω • (1 : Op Q 3 _) = toQ c ^ 0 • (negωQ • 1)
    rw [pow_zero, one_smul, toQ_negω]
  | gate1 g =>
    cases g
    · show onBottom (HZ.map toQ) = toQ c ^ 1 • onBottom (ofMat HQ)
      rw [pow_one, ← onBottom_smul, HZ_map]
    · show onBottom (SZ.map toQ) = toQ c ^ 0 • onBottom (ofMat SQ)
      rw [pow_zero, one_smul, SZ_map]
    · show onBottom (SpZ.map toQ) = toQ c ^ 0 • onBottom SpX
      rw [pow_zero, one_smul, SpZ_map]
  | gate2 g =>
    cases g
    · show onBottom (CZZ.map toQ) = toQ c ^ 0 • onBottom (ofMat CZQ)
      rw [pow_zero, one_smul, CZZ_map]
    · show onBottom (swapZ.map toQ) = toQ c ^ 0 • onBottom swapX
      rw [pow_zero, one_smul, swapZ_map]
    · show onBottom (cxZ.map toQ) = toQ c ^ 0 • onBottom cxX
      rw [pow_zero, one_smul, cxZ_map]
    · show onBottom (xcZ.map toQ) = toQ c ^ 0 • onBottom xcX
      rw [pow_zero, one_smul, xcZ_map]
  | gate3 g => exact nomatch g
  | up g ih =>
    show onTop 1 ((opsZ.map toQ).gen g) = _ • onTop 1 (opsX.gen g)
    rw [ih, onTop_smul]
    rfl

theorem evalZ_weight {n : ℕ} (w : Circuit XGate n) :
    (opsZ.map toQ).eval n w = toQ c ^ hcount w • opsX.eval n w :=
  eval_weight opsX (opsZ.map toQ) (toQ c) wtX opsZ_gen w

/-- Extended circuits passing the check have the same matrix over `ℚ(ζ)`. -/
theorem evalX_eq {n : ℕ} {w v : Circuit XGate n} (h : checkZ w v = true) :
    opsX.eval n w = opsX.eval n v := by
  have h1 : ∀ t ∈ allStates n, smul (c ^ hcount v) (actW opsZ w (basis t)) =
      smul (c ^ hcount w) (actW opsZ v (basis t)) := by
    intro t ht
    rw [← actWZ_eq, ← actWZ_eq]
    exact eq_of_beq (List.all_eq_true.1 h t ht)
  have h3 := congrArg (fun M => M.map toQ) (eval_eq_of_cols_smul opsZ opsZ h1)
  dsimp only at h3
  rw [map_smul_hom, map_smul_hom, map_pow, map_pow, ← GateOps.eval_map, ← GateOps.eval_map,
    evalZ_weight, evalZ_weight, smul_smul, smul_smul, ← pow_add, ← pow_add,
    add_comm (hcount w)] at h3
  exact smul_cancel h3

/-! ### Circuits and extended circuits with the same evaluation -/

/-- `c` and the extended circuit `cX` have the same evaluation. -/
def Sim {n : ℕ} (c : Circ n) (cX : Circuit XGate n) : Prop := ops.eval n c = opsX.eval n cX

namespace Sim

variable {n : ℕ}

theorem one : Sim (1 : Circ n) 1 := by simp [Sim]

theorem seq {a b : Circ n} {aX bX : Circuit XGate n} (ha : Sim a aX) (hb : Sim b bX) :
    Sim (a ⨾ b) (bX * aX) := by
  simp only [Sim, seq_def, map_mul] at *; rw [ha, hb]

theorem mul {a b : Circ n} {aX bX : Circuit XGate n} (ha : Sim a aX) (hb : Sim b bX) :
    Sim (a * b) (aX * bX) := by
  simp only [Sim, map_mul] at *; rw [ha, hb]

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

theorem par {a b : Circ 1} {aX bX : Circuit XGate 1} (ha : Sim a aX) (hb : Sim b bX) :
    Sim (QutritClifford.par a b) (Circuit.shift aX * Circuit.pad 1 bX) :=
  ha.top.mul hb.bot

theorem negω : Sim (QutritClifford.negω : Circ n) (FreeMonoid.of (Gen.gate0 XGate.negω)) := by
  simp only [Sim, QutritClifford.negω, Circuit.g0, GateOps.eval, FreeMonoid.lift_eval_of]; rfl

theorem H : Sim QutritClifford.H (FreeMonoid.of (Gen.gate1 XGate.H)) := by
  simp only [Sim, QutritClifford.H, Circuit.g1]; rw [evalOfGate1, evalOfGate1]; rfl

theorem S : Sim QutritClifford.S (FreeMonoid.of (Gen.gate1 XGate.S)) := by
  simp only [Sim, QutritClifford.S, Circuit.g1]; rw [evalOfGate1, evalOfGate1]; rfl

theorem CZ : Sim QutritClifford.CZ (FreeMonoid.of (Gen.gate2 XGate.CZ)) := by
  simp only [Sim, QutritClifford.CZ, Circuit.g2]; rw [evalOfGate2, evalOfGate2]; rfl

/-- Two circuits simulated by extended circuits that pass `checkZ` evaluate
alike. -/
theorem eval_eq {w v : Circ n} {wX vX : Circuit XGate n} (hw : Sim w wX) (hv : Sim v vX)
    (h : checkZ wX vX = true) : ops.eval n w = ops.eval n v :=
  hw.trans ((evalX_eq h).trans hv.symm)

end Sim

/-! ### The derived gates -/

set_option maxRecDepth 100000

theorem eval_S' : ops.eval 1 S' = SpX :=
  ((((Sim.H.pow 2).seq Sim.S).seq (Sim.H.pow 2)).trans
    (evalX_eq (v := FreeMonoid.of (Gen.gate1 XGate.Sp)) (by decide +kernel))).trans
    (evalOfGate1 opsX XGate.Sp)

theorem eval_SWAP : ops.eval 2 SWAP = swapX :=
  ((((((Sim.par Sim.H Sim.H).seq Sim.CZ).seq (Sim.par Sim.H Sim.H)).seq Sim.CZ).seq
      (Sim.par Sim.H Sim.H)).seq Sim.CZ).trans
    (evalX_eq (v := FreeMonoid.of (Gen.gate2 XGate.SWAP)) (by decide +kernel)) |>.trans
    (evalOfGate2 opsX XGate.SWAP)

theorem eval_CX : ops.eval 2 CX = cxX :=
  (((Sim.H.bot.seq Sim.CZ).seq (Sim.H.pow 3).bot).trans
    (evalX_eq (v := FreeMonoid.of (Gen.gate2 XGate.CX)) (by decide +kernel))).trans
    (evalOfGate2 opsX XGate.CX)

theorem eval_XC : ops.eval 2 XC = xcX :=
  (((Sim.H.top.seq Sim.CZ).seq (Sim.H.pow 3).top).trans
    (evalX_eq (v := FreeMonoid.of (Gen.gate2 XGate.XC)) (by decide +kernel))).trans
    (evalOfGate2 opsX XGate.XC)

namespace Sim

theorem Sp : Sim S' (FreeMonoid.of (Gen.gate1 XGate.Sp)) := by
  simp only [Sim]; rw [eval_S', evalOfGate1]; rfl

theorem SWAP : Sim QutritClifford.SWAP (FreeMonoid.of (Gen.gate2 XGate.SWAP)) := by
  simp only [Sim]; rw [eval_SWAP, evalOfGate2]; rfl

theorem CX : Sim QutritClifford.CX (FreeMonoid.of (Gen.gate2 XGate.CX)) := by
  simp only [Sim]; rw [eval_CX, evalOfGate2]; rfl

theorem XC : Sim QutritClifford.XC (FreeMonoid.of (Gen.gate2 XGate.XC)) := by
  simp only [Sim]; rw [eval_XC, evalOfGate2]; rfl

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
