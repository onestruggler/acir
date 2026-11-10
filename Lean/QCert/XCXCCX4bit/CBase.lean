/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The controlled matching G = CX₃₀ and its frames over P

Translation of `CBase.agda`.  `G` is `X` on wire 0 controlled by wire 3: on
the half where wire 3 is 1 it is the perfect matching `μ₀` of the lower
states that flips wire 0, the pairs (0 1)(2 3)(4 5)(6 7) of `Width3`'s Gray
positions.  Its frames `Fr G p` (`PFrames`) are the matching `p μ₀ p⁻¹`,
controlled.  A frame depends only on that matching, because a three-wire
circuit whose permutation commutes with the flip of wire 0 commutes with `G`
(`wcore`): on the states it is a flip of wire 0 on some values of wires 2, 1
(`Width3`'s `T 0`, `T 2`, `T 4`, `T 6`, each commuting with `G` by equation
E8 and `X` on its controls) followed by a permutation of those values (a
two-wire circuit on wires 1, 2, which `G` does not touch).  The
decomposition is computed from the permutation and checked by evaluation
(`wcheck`), so `wcore` and `W` take the check as a hypothesis: every use is
at concrete Coxeter words.

Names.  The Agda's `comm-ε`, `comm-•`, `comm-≈`, `comm-sym`, `comm-list`,
`comm-circ` are `comm_ε`, `comm_mul`, `comm_eqv`, `comm_sym`, `comm_list`,
`comm_circ`; `Ḡ` and `commḠ` are `Gbar` and `commGbar` (a letter with a
macron is not an identifier character); `flip-comm₀` is `flip_comm₀`;
`Pc-↓` is `Pc_down`; `Pc₃` is `Pc₃` (the circuits of Coxeter words on
three wires, `Coxeter.Circuits.Pc Width3.T`).

**Deviation from the Agda.**  Words are multiplied left-associatively
(`Gbar = ι X₃ * G * ι X₃`, `flipsC b` and `PFrames.Fr` likewise), so the
Agda's associativity steps are reasoning in the quotient monoid
(`CircuitProp.cl`).  `comm-on12` is by induction on the circuit with one
case per letter of `Gn 2`, each decided as the Agda's.
-/
import QCert.XCXCCX4bit.PFrames
import QCert.XCXCCX4bit.ToPlaced
import QCert.XCXCCX4bit.Equations4

namespace QCert.XCXCCX4bit.CBase

open QCert QCert.Circuit CircuitProp IndepProp
open Placed ToPlaced PFrames

/-- The circuits of Coxeter words on the three lower wires. -/
abbrev Pc₃ (o : ℕ) {n : ℕ} : Word (SG n) →* Circ 3 := Coxeter.Circuits.Pc Width3.T o

/-! ## Commutation -/

/-- Two four-wire circuits that commute. -/
abbrev Comm (a b : Circ 4) : Prop := 4 ⊢ a * b ≈ b * a

theorem comm_ε {c : Circ 4} : Comm 1 c := by
  show 4 ⊢ 1 * c ≈ c * 1
  rw [one_mul, mul_one]

theorem comm_mul {a b c : Circ 4} (ea : Comm a c) (eb : Comm b c) : Comm (a * b) c := by
  apply cl_eq.1
  have ha := cl_eq.2 ea
  have hb := cl_eq.2 eb
  simp only [cl_mul] at ha hb ⊢
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem comm_eqv {a a' c : Circ 4} (e : 4 ⊢ a ≈ a') (h : Comm a' c) : Comm a c :=
  (e.mul (Derivable.refl c)).trans (h.trans ((Derivable.refl c).mul e.symm))

theorem comm_sym {a c : Circ 4} (h : Comm a c) : Comm c a := h.symm

/-- Every letter of a word of placed letters disjoint from `g`. -/
theorem comm_list (g : PG) : ∀ xs : List PG, every (fun x => disjoint x g) xs = true →
    Comm (ιs xs) (ι g)
  | [], _ => comm_ε
  | x :: xs, h => by
    simp only [every, Bool.and_eq_true] at h
    exact comm_mul (disj_comm x g h.1) (comm_list g xs h.2)

/-- A circuit whose placed letters are disjoint from `g`. -/
theorem comm_circ (u : Circ 4) (g : PG) (h : every (fun x => disjoint x g) (pg u) = true) :
    Comm u (ι g) :=
  comm_eqv (pg_ok u) (comm_list g (pg u) h)

/-! ## G and Ḡ -/

/-- `X` on wire 0 controlled by wire 3. -/
def G : Circ 4 := ι (.CXₚ 3 0)

/-- `G` with its control negated: `X` on wire 0 controlled by wire 3 = 0
(the Agda's `Ḡ`). -/
def Gbar : Circ 4 := ι (.Xₚ 3) * G * ι (.Xₚ 3)

/-- A circuit that commutes with `G` and with `X` on wire 3 commutes with
`Gbar` (the Agda's `commḠ`). -/
theorem commGbar {a : Circ 4} (hG : Comm a G) (hX : Comm a (ι (.Xₚ 3))) : Comm a Gbar :=
  comm_sym (comm_mul (comm_mul (comm_sym hX) (comm_sym hG)) (comm_sym hX))

/-! ## The flips of wire 0 commute with G -/

/-- E8: `CCX₂₁→₀` commutes with `G`. -/
private theorem comm_T4 : Comm (ι (.CCXₚ 1 2 0)) G := by
  have e : 4 ⊢ ιs [PG.CCXₚ 1 2 0, PG.CXₚ 3 0] ≈ ιs [PG.CXₚ 3 0, PG.CCXₚ 1 2 0] :=
    Equations4.E8E.prf
  simp only [ιs, mul_one] at e
  exact e

private theorem comm_X₁ : Comm (ι (.Xₚ 1)) G := disj_comm (.Xₚ 1) (.CXₚ 3 0) rfl

private theorem comm_X₂ : Comm (ι (.Xₚ 2)) G := disj_comm (.Xₚ 2) (.CXₚ 3 0) rfl

/-- `T 0`, `X` on the white controls of `CCX₂₁→₀`. -/
theorem flip_comm₀ : Comm (T₄ 0) G := by
  refine comm_eqv (pg_ok _) ?_
  rw [show pg (T₄ 0) = [PG.Xₚ 2, PG.Xₚ 1, PG.CCXₚ 1 2 0, PG.Xₚ 1, PG.Xₚ 2] from rfl]
  exact comm_mul comm_X₂ (comm_mul comm_X₁ (comm_mul comm_T4 (comm_mul comm_X₁
    (comm_mul comm_X₂ comm_ε))))

theorem flip_comm₂ : Comm (T₄ 2) G := by
  refine comm_eqv (pg_ok _) ?_
  rw [show pg (T₄ 2) = [PG.Xₚ 2, PG.CCXₚ 1 2 0, PG.Xₚ 2] from rfl]
  exact comm_mul comm_X₂ (comm_mul comm_T4 (comm_mul comm_X₂ comm_ε))

theorem flip_comm₄ : Comm (T₄ 4) G := by
  refine comm_eqv (pg_ok _) ?_
  rw [show pg (T₄ 4) = [PG.CCXₚ 1 2 0] from rfl]
  exact comm_mul comm_T4 comm_ε

theorem flip_comm₆ : Comm (T₄ 6) G := by
  refine comm_eqv (pg_ok _) ?_
  rw [show pg (T₄ 6) = [PG.Xₚ 1, PG.CCXₚ 1 2 0, PG.Xₚ 1] from rfl]
  exact comm_mul comm_X₁ (comm_mul comm_T4 (comm_mul comm_X₁ comm_ε))

/-! ## Two-wire circuits on wires 1, 2 commute with G -/

/-- `c` on wires 1, 2 of a four-wire circuit. -/
def on12 (c : Circ 2) : Circ 4 := Circuit.pad 1 (shift c)

private theorem comm_on12_gen : ∀ g : Gn 2, Comm (on12 (FreeMonoid.of g)) G
  | .gate0 (.gate g) => nomatch g
  | .gate1 (.gate .X_gate) => comm_circ _ (.CXₚ 3 0) rfl
  | .gate2 (.gate .CX_gate) => comm_circ _ (.CXₚ 3 0) rfl
  | .gate2 .swap => comm_circ _ (.CXₚ 3 0) rfl
  | .up (.gate0 (.gate g)) => nomatch g
  | .up (.gate1 (.gate .X_gate)) => comm_circ _ (.CXₚ 3 0) rfl
  | .up (.up (.gate0 (.gate g))) => nomatch g

theorem comm_on12 (c : Circ 2) : Comm (on12 c) G := by
  induction c using FreeMonoid.inductionOn' with
  | one => exact comm_ε
  | mul_of g c ih =>
    rw [on12, map_mul, map_mul]
    exact comm_mul (comm_on12_gen g) ih

/-! ## The decomposition of a permutation commuting with the flip of wire 0 -/

/-- A circuit or nothing. -/
def fl : Bool → Circ 3 → Circ 3
  | true, c => c
  | false, _ => 1

/-- The four flips, chosen by the values (wire 1, wire 2) they act on. -/
def flipsC (b : Bits 2 → Bool) : Circ 3 :=
  fl (b (false ∷ false ∷ .nil)) (Width3.T 0) * fl (b (true ∷ false ∷ .nil)) (Width3.T 2)
    * fl (b (true ∷ true ∷ .nil)) (Width3.T 4) * fl (b (false ∷ true ∷ .nil)) (Width3.T 6)

/-- A two-wire circuit for each permutation of the values of two wires,
given by its images of 00, 10, 01, 11 (wire 0 first). -/
def pairC : Bits 2 → Bits 2 → Bits 2 → Bits 2 → Circ 2
  | false ∷ false ∷ .nil, false ∷ true ∷ .nil, true ∷ false ∷ .nil, true ∷ true ∷ .nil => σ
  | false ∷ false ∷ .nil, false ∷ true ∷ .nil, true ∷ true ∷ .nil, true ∷ false ∷ .nil => CX * σ
  | false ∷ false ∷ .nil, true ∷ false ∷ .nil, false ∷ true ∷ .nil, true ∷ true ∷ .nil => 1
  | false ∷ false ∷ .nil, true ∷ false ∷ .nil, true ∷ true ∷ .nil, false ∷ true ∷ .nil => CX
  | false ∷ false ∷ .nil, true ∷ true ∷ .nil, false ∷ true ∷ .nil, true ∷ false ∷ .nil =>
    CX * σ * CX
  | false ∷ false ∷ .nil, true ∷ true ∷ .nil, true ∷ false ∷ .nil, false ∷ true ∷ .nil => σ * CX
  | false ∷ true ∷ .nil, false ∷ false ∷ .nil, true ∷ false ∷ .nil, true ∷ true ∷ .nil =>
    X * CX * σ
  | false ∷ true ∷ .nil, false ∷ false ∷ .nil, true ∷ true ∷ .nil, true ∷ false ∷ .nil => X * σ
  | false ∷ true ∷ .nil, true ∷ false ∷ .nil, false ∷ false ∷ .nil, true ∷ true ∷ .nil =>
    shift X * CX * σ * CX
  | false ∷ true ∷ .nil, true ∷ false ∷ .nil, true ∷ true ∷ .nil, false ∷ false ∷ .nil =>
    σ * CX * shift X
  | false ∷ true ∷ .nil, true ∷ true ∷ .nil, false ∷ false ∷ .nil, true ∷ false ∷ .nil => shift X
  | false ∷ true ∷ .nil, true ∷ true ∷ .nil, true ∷ false ∷ .nil, false ∷ false ∷ .nil =>
    CX * shift X
  | true ∷ false ∷ .nil, false ∷ false ∷ .nil, false ∷ true ∷ .nil, true ∷ true ∷ .nil => X * CX
  | true ∷ false ∷ .nil, false ∷ false ∷ .nil, true ∷ true ∷ .nil, false ∷ true ∷ .nil => X
  | true ∷ false ∷ .nil, false ∷ true ∷ .nil, false ∷ false ∷ .nil, true ∷ true ∷ .nil =>
    shift X * σ * CX
  | true ∷ false ∷ .nil, false ∷ true ∷ .nil, true ∷ true ∷ .nil, false ∷ false ∷ .nil =>
    CX * shift X * σ * CX
  | true ∷ false ∷ .nil, true ∷ true ∷ .nil, false ∷ false ∷ .nil, false ∷ true ∷ .nil =>
    shift X * σ
  | true ∷ false ∷ .nil, true ∷ true ∷ .nil, false ∷ true ∷ .nil, false ∷ false ∷ .nil =>
    CX * shift X * σ
  | true ∷ true ∷ .nil, false ∷ false ∷ .nil, false ∷ true ∷ .nil, true ∷ false ∷ .nil =>
    X * σ * CX
  | true ∷ true ∷ .nil, false ∷ false ∷ .nil, true ∷ false ∷ .nil, false ∷ true ∷ .nil =>
    X * CX * σ * CX
  | true ∷ true ∷ .nil, false ∷ true ∷ .nil, false ∷ false ∷ .nil, true ∷ false ∷ .nil =>
    shift X * CX
  | true ∷ true ∷ .nil, false ∷ true ∷ .nil, true ∷ false ∷ .nil, false ∷ false ∷ .nil =>
    X * shift X
  | true ∷ true ∷ .nil, true ∷ false ∷ .nil, false ∷ false ∷ .nil, false ∷ true ∷ .nil =>
    shift X * CX * σ
  | true ∷ true ∷ .nil, true ∷ false ∷ .nil, false ∷ true ∷ .nil, false ∷ false ∷ .nil =>
    X * shift X * σ
  | _, _, _, _ => 1

/-- The flips of the canonical circuit of a permutation `π` of the lower
states: wire 0 where `π` flips it on the states with wire 0 = 0. -/
def canB (π : Bits 3 → Bits 3) (v : Bits 2) : Bool := (π (false ∷ v)).head

/-- The values of wires 1, 2 that `π` sends them to. -/
def canS (π : Bits 3 → Bits 3) (v : Bits 2) : Bits 2 := (π (false ∷ v)).tail

def canP (π : Bits 3 → Bits 3) : Circ 2 :=
  pairC (canS π (false ∷ false ∷ .nil)) (canS π (true ∷ false ∷ .nil))
    (canS π (false ∷ true ∷ .nil)) (canS π (true ∷ true ∷ .nil))

/-- The canonical circuit of a permutation of the lower states: flip wire 0
where `π` does on the states with wire 0 = 0, then permute the values of
wires 1, 2 as `π` does. -/
def canon (π : Bits 3 → Bits 3) : Circ 3 := flipsC (canB π) * shift (canP π)

/-- The check: the permutation of `r` is its canonical circuit's. -/
def wcheck (r : CW 8) : Bool := eqF 3 (sem (Pc₃ 0 r)) (sem (canon (sem (Pc₃ 0 r))))

/-! ## The frame lemma for G -/

/-- The Agda's `Pc-↓`. -/
theorem Pc_down (o : ℕ) {n : ℕ} (r : Word (SG n)) : Pc o r = Circuit.pad 1 (Pc₃ o r) := by
  induction r using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g r ih => rw [map_mul, map_mul, map_mul, ih]; rfl

private theorem cf (x : Bool) (k : ℕ) (h : Comm (T₄ k) G) :
    Comm (Circuit.pad 1 (fl x (Width3.T k))) G := by
  cases x
  · exact comm_ε
  · exact h

theorem comm_flips (b : Bits 2 → Bool) : Comm (Circuit.pad 1 (flipsC b)) G := by
  rw [flipsC, map_mul, map_mul, map_mul]
  exact comm_mul (comm_mul (comm_mul (cf _ 0 flip_comm₀) (cf _ 2 flip_comm₂))
    (cf _ 4 flip_comm₄)) (cf _ 6 flip_comm₆)

/-- A Coxeter word whose permutation passes the check commutes with `G`. -/
theorem wcore (r : CW 8) (h : wcheck r = true) : Comm (Pc 0 r) G := by
  rw [Pc_down]
  refine comm_eqv (P_eq (eqF_sound 3 _ _ h)) ?_
  show Comm (Circuit.pad 1 (flipsC _ * shift (canP _))) G
  rw [map_mul]
  exact comm_mul (comm_flips _) (comm_on12 _)

/-- Two frames of `G` whose Coxeter words differ by a word commuting with `G`
are equal. -/
theorem Wc (p q : CW 8) (h : Comm (Pc 0 (inv q * p)) G) : 4 ⊢ Fr G p ≈ Fr G q := by
  apply cl_eq.1
  have hq := cl_eq.2 (Pc_inv 0 le_rfl q)
  have hp := cl_eq.2 (Pc_inv 0 le_rfl p)
  have hh := cl_eq.2 h
  simp only [Fr, Coxeter.Circuits.Fr, map_mul, cl_mul, cl_one] at hq hp hh ⊢
  calc cl4 (Pc 0 p) * cl4 G * cl4 (Pc 0 (inv p))
      = cl4 (Pc 0 q) * cl4 (Pc 0 (inv q)) * cl4 (Pc 0 p) * cl4 G * cl4 (Pc 0 (inv p)) := by
        rw [hq, one_mul]
    _ = cl4 (Pc 0 q) * (cl4 (Pc 0 (inv q)) * cl4 (Pc 0 p) * cl4 G) * cl4 (Pc 0 (inv p)) := by
        simp only [mul_assoc]
    _ = cl4 (Pc 0 q) * (cl4 G * (cl4 (Pc 0 (inv q)) * cl4 (Pc 0 p))) * cl4 (Pc 0 (inv p)) := by
        rw [hh]
    _ = cl4 (Pc 0 q) * cl4 G * cl4 (Pc 0 (inv q)) * (cl4 (Pc 0 p) * cl4 (Pc 0 (inv p))) := by
        simp only [mul_assoc]
    _ = cl4 (Pc 0 q) * cl4 G * cl4 (Pc 0 (inv q)) := by rw [hp, mul_one]

/-- The same with the commutation checked. -/
theorem W (p q : CW 8) (h : wcheck (inv q * p) = true) : 4 ⊢ Fr G p ≈ Fr G q :=
  Wc p q (wcore (inv q * p) h)

end QCert.XCXCCX4bit.CBase
