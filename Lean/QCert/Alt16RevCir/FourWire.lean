/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Four wires: the steps a derivation from the rules (1)–(7) is made of

Translation of `FourWire.agda`.  On four wires a letter is a gate on the
bottom three wires, on the top three, or both, so a derivation needs just
two kinds of step besides the rules that are properly about four wires:

* `bot l r` and `top l r`: two three-wire circuits with the same function,
  on the bottom three wires and on the top three.  They are equal by the
  rules, because the rules are complete on three wires (`ThreeWire`); the
  evidence is a Boolean computed on the eight states.

* rule (7) (`r7E`), the naturality of the swap at `CCX` (`nat_ccxE`), and
  the commutations of a gate that touches wire 0 with a gate that touches
  wire 3 and no wire of the first (`comm_…`): the instances of the rules
  that involve all four wires.

These are equations of the engine (`Engine`), used by `rw` in the
derivations of the relations of `Syntactics` from the rules (`Frames`,
`Four.Part*`, `Four.Relations`, `Equivalence`).

**Deviations from the Agda.**  The letters on four wires are the alphabet
`L4` of `Engine` (the Agda defines `x0`, …, `ccx1 : Gen 4` here), and a
three-wire circuit is a list of names in `L3`.  The evidence of a
three-wire step is `same3 l r = true`, decided on the eight states as
numbers (`Semantics`' `sameOps`, with each letter's operation `op3` checked
against its function once), where the Agda's is `same 3 ⟪ l ⟫ ⟪ r ⟫ ≡ true`:
the kernel runs it some twenty thousand times in `Four.Part*`.  `top` and
`bot` are `Engine`'s `liftE` and `padE` along the maps of names `up34` and
`dn34`.  The Agda's `r7⁼`, `nat-ccx⁼` are `r7E`, `nat_ccxE`.
-/
import QCert.Alt16RevCir.ThreeWire
import QCert.Alt16RevCir.Engine

namespace QCert.Alt16RevCir.FourWire

open QCert QCert.Circuit CircuitProp Engine

/-! ## Three-wire steps -/

/-- The operation of a three-wire letter on the numbers of the states. -/
def op3 : L3 → Op
  | .x0 => ⟨0, 0, 0, 1⟩
  | .x1 => ⟨0, 0, 0, 2⟩
  | .x2 => ⟨0, 0, 0, 4⟩
  | .cx0 => ⟨2, 2, 2, 1⟩
  | .cx1 => ⟨4, 4, 4, 2⟩
  | .ex0 => ⟨3, 1, 2, 3⟩
  | .ex1 => ⟨6, 2, 4, 6⟩
  | .ccx => ⟨6, 6, 6, 1⟩

private theorem op3_ok (a : L3)
    (h : allB 3 (fun x => Nat.beq (num (semG (Alpha.gen a) x)) ((op3 a).app (num x))) = true)
    (x : Bits 3) : num (semG (Alpha.gen a) x) = (op3 a).app (num x) :=
  Nat.eq_of_beq_eq_true (allB_sound 3 _ h x)

/-- The operation of each letter is its function. -/
theorem op3_sem : ∀ (a : L3) (x : Bits 3), num (semG (Alpha.gen a) x) = (op3 a).app (num x)
  | .x0 => op3_ok _ (by decide +kernel)
  | .x1 => op3_ok _ (by decide +kernel)
  | .x2 => op3_ok _ (by decide +kernel)
  | .cx0 => op3_ok _ (by decide +kernel)
  | .cx1 => op3_ok _ (by decide +kernel)
  | .ex0 => op3_ok _ (by decide +kernel)
  | .ex1 => op3_ok _ (by decide +kernel)
  | .ccx => op3_ok _ (by decide +kernel)

/-- Two three-wire circuits with the same function, decided on the eight
states (the Agda's `same 3 ⟪ l ⟫ ⟪ r ⟫`). -/
def same3 (l r : List L3) : Bool := sameOps 8 (l.map op3) (r.map op3)

theorem same3_sound (l r : List L3) (h : same3 l r = true) :
    sem (word l) ≐ sem (word r) :=
  sameOps_sound Alpha.gen op3 op3_sem l r h

/-- Two three-wire circuits with the same function. -/
def sem₃ (l r : List L3) (h : same3 l r = true) : Eqn TRel L3 :=
  ⟨l, r, ThreeWire.complete₃ (same3_sound l r h)⟩

/-- A three-wire letter one wire up, on four wires. -/
def up34 : L3 → L4
  | .x0 => .x1 | .x1 => .x2 | .x2 => .x3 | .cx0 => .cx1 | .cx1 => .cx2
  | .ex0 => .ex1 | .ex1 => .ex2 | .ccx => .ccx1

theorem up34_gen : ∀ a : L3, Alpha.gen (up34 a) = (Alpha.gen a).up
  | .x0 => rfl | .x1 => rfl | .x2 => rfl | .cx0 => rfl | .cx1 => rfl
  | .ex0 => rfl | .ex1 => rfl | .ccx => rfl

/-- A three-wire letter on the bottom three wires of four (the Agda's
`_↧ᵏ 1`). -/
def dn34 : L3 → L4
  | .x0 => .x0 | .x1 => .x1 | .x2 => .x2 | .cx0 => .cx0 | .cx1 => .cx1
  | .ex0 => .ex0 | .ex1 => .ex1 | .ccx => .ccx0

theorem dn34_gen : ∀ a : L3, Alpha.gen (dn34 a) = (Alpha.gen a).pad 1
  | .x0 => rfl | .x1 => rfl | .x2 => rfl | .cx0 => rfl | .cx1 => rfl
  | .ex0 => rfl | .ex1 => rfl | .ccx => rfl

/-- … on the top three wires of four, -/
def top (l r : List L3) (h : same3 l r = true) : Eqn TRel L4 :=
  liftE up34 up34_gen (sem₃ l r h)

/-- … and on the bottom three. -/
def bot (l r : List L3) (h : same3 l r = true) : Eqn TRel L4 :=
  padE (m := 1) dn34 dn34_gen (by decide) (sem₃ l r h)

/-! ## The rules on four wires -/

open L4 in
/-- Rule (7). -/
def r7E : Eqn TRel L4 :=
  eqnW [ccx1, cx0, ccx1] [ex0, ccx1, ex0, cx0] (srel_rule TRel.r7) rfl rfl

open L4 in
/-- `CCX` followed by the cycle of the four wires is the cycle followed by
`CCX` one wire up. -/
def nat_ccxE : Eqn TRel L4 :=
  eqnW [ccx0, ex2, ex1, ex0] [ex2, ex1, ex0, ccx1] (sym_rule (Sym.σ_nat₃ Gate.CCX_gate)) rfl rfl

/-! A gate that touches wire 0 commutes with one that touches wire 3 on
other wires. -/

section Comm

open L4

def comm_x3_x0 : Eqn TRel L4 := eqnW [x3, x0] [x0, x3]
  (Derivable.of (Lift.comm1 Gate.X_gate (Gen.up (Gen.up (Gen.gate1 Gate.X_gate))))) rfl rfl

def comm_cx2_x0 : Eqn TRel L4 := eqnW [cx2, x0] [x0, cx2]
  (Derivable.of (Lift.comm1 Gate.X_gate (Gen.up (Gen.gate2 Gate.CX_gate)))) rfl rfl

def comm_ex2_x0 : Eqn TRel L4 := eqnW [ex2, x0] [x0, ex2]
  (Derivable.of (Lift.comm1 Gate.X_gate (Gen.up (Gen.gate2 Gate.Ex_gate)))) rfl rfl

def comm_ccx1_x0 : Eqn TRel L4 := eqnW [ccx1, x0] [x0, ccx1]
  (Derivable.of (Lift.comm1 Gate.X_gate (Gen.gate3 Gate.CCX_gate))) rfl rfl

def comm_x3_cx0 : Eqn TRel L4 := eqnW [x3, cx0] [cx0, x3]
  (Derivable.of (Lift.comm2 Gate.CX_gate (Gen.up (Gen.gate1 Gate.X_gate)))) rfl rfl

def comm_cx2_cx0 : Eqn TRel L4 := eqnW [cx2, cx0] [cx0, cx2]
  (Derivable.of (Lift.comm2 Gate.CX_gate (Gen.gate2 Gate.CX_gate))) rfl rfl

def comm_ex2_cx0 : Eqn TRel L4 := eqnW [ex2, cx0] [cx0, ex2]
  (Derivable.of (Lift.comm2 Gate.CX_gate (Gen.gate2 Gate.Ex_gate))) rfl rfl

def comm_x3_ex0 : Eqn TRel L4 := eqnW [x3, ex0] [ex0, x3]
  (Derivable.of (Lift.comm2 Gate.Ex_gate (Gen.up (Gen.gate1 Gate.X_gate)))) rfl rfl

def comm_cx2_ex0 : Eqn TRel L4 := eqnW [cx2, ex0] [ex0, cx2]
  (Derivable.of (Lift.comm2 Gate.Ex_gate (Gen.gate2 Gate.CX_gate))) rfl rfl

def comm_ex2_ex0 : Eqn TRel L4 := eqnW [ex2, ex0] [ex0, ex2]
  (Derivable.of (Lift.comm2 Gate.Ex_gate (Gen.gate2 Gate.Ex_gate))) rfl rfl

def comm_x3_ccx0 : Eqn TRel L4 := eqnW [x3, ccx0] [ccx0, x3]
  (Derivable.of (Lift.comm3 Gate.CCX_gate (Gen.gate1 Gate.X_gate))) rfl rfl

end Comm

/-! ## A first use: `CX` on the bottom wires commutes with the Toffoli gate from the top two wires onto wire 0

With `T` the Toffoli gate one wire up, `c` the bottom `CX` and `Q` the
Toffoli gate with controls 2 3 and target 0, rule (7) says `T c T = Q c`, so
`Q = T c T c`; `Q` is an involution (a fact about three wires), hence
`(T c)⁴ = ε`, which is what `c Q = Q c` comes to.  The generated derivations
(`Four.Part*`) are lists of steps like this one. -/

open L4 in
/-- `Q Q = ε`: the swaps cancel on the bottom wires, the Toffoli gates on the
top wires. -/
private def QQ : Eqn TRel L4 := derive [ex0, ccx1, ex0, ex0, ccx1, ex0] []
  [Step.rw 2 (bot [.ex0, .ex0] [] (by decide +kernel)),
   Step.rw 1 (top [.ccx, .ccx] [] (by decide +kernel)),
   Step.rw 0 (bot [.ex0, .ex0] [] (by decide +kernel))]
  (by decide +kernel)

open L4 in
def comm_cx0_Q : Eqn TRel L4 := derive [cx0, ex0, ccx1, ex0] [ex0, ccx1, ex0, cx0]
  -- c Q → c Q c c → c (T c T) c
  [Step.rw 4 (symE (bot [.cx0, .cx0] [] (by decide +kernel))),
   Step.rw 1 (symE r7E),
   -- → Q Q c T c T c: put Q Q, the identity, in front
   Step.rw 0 (symE QQ),
   -- the second Q with what follows it, Q c, is T c T
   Step.rw 3 (symE r7E),
   -- now Q (T c T) (T c T) c: the inner T T and c c cancel
   Step.rw 5 (top [.ccx, .ccx] [] (by decide +kernel)),
   Step.rw 4 (bot [.cx0, .cx0] [] (by decide +kernel)),
   Step.rw 3 (top [.ccx, .ccx] [] (by decide +kernel))]
  (by decide +kernel)

end QCert.Alt16RevCir.FourWire
