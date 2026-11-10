/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The controlled matchings: involution, conjugation and Klein pairs

Translation of `CRel.agda`.  A label is one of the 105 perfect matchings of
the Gray positions (`CLabels`), and `Xm x` is the frame of `G = CX₃₀` that
places `μ₀` on it: the matching `x` controlled by wire 3.  Three relations
hold among them, each under a side condition that is decided on the labels
(by comparing matchings on the eight positions), so that a certificate over
labels (`LabelEngine`) is checked by computation:

* `X_inv`:   `Xm x Xm x = ε`;
* `X_conj`:  `Xm x Xm y Xm x = Xm (x y x)`.  `G` is `X` on wire 0 times
  `Gbar`, the same controlled by wire 3 = 0 (`splitG`), so `Xm x` is
  `P x Qbar x` with `P x` a circuit of the lower wires (the matching `x`,
  uncontrolled) and `Qbar x` the matching `x` controlled by wire 3 = 0.
  `Qbar x` commutes with `Xm y` (block commutation, `BC`): conjugated by the
  frame of `x` it is `Gbar` against a frame of `G`, which the centraliser of
  `μ₀` carries to one of five base frames (`CLabels`' orbit table and the
  frame lemma `W'`); the five base commutations are the parameter `base` of
  the section `Calculus`.  So `Xm x Xm y Xm x = P x Xm y P x`, the frame of
  `G` by `x y x`;
* `X_klein`: `Xm x Xm y = Xm (x y)` for commuting `x ≠ y` whose product is a
  matching: a frame carries the standard Klein pair, `μ₀` and its conjugate
  by `CX₀₁`, to `x` and `y`, and there the relation holds on wires 0, 1, 3.

Names.  The Agda's `_==ᴸ_` is `eqLab`, `Ḡ`, `Q̄` are `Gbar`, `Qbar`, `ḠḠ` is
`GbarGbar`, `split` and `split-comm` are `splitG` and `splitG_comm`,
`Fr-•` is `Fr_mul`, `comm-≈ʳ` is `comm_eqv_r`, `BC₀-ok` is `BC₀_ok`, `inC?` is
`inC?`; hyphens are underscores.  The Agda's module `Calculus base` is the
namespace `Calculus`, whose theorems that use `base` (`BC₀`, `BC`,
`X_conj`) take it as their first explicit argument; `X_inv` and `X_klein`
do not use it and do not take it.  `X_conj` is stated
with Lean's left-associated product, `Xm x * Xm y * Xm x`, as `LabelEngine`
takes it.

**Deviation from the Agda.**  The tables are lists, read by `nthD`; `find`
returns an `Option` (the Agda's `Maybe`).  `Coxeter.frame` is total, so the
Agda's `distinct?` (which returns a proof of distinctness) is a Boolean
test here, and `ko` uses `frame (kleinList x y)` directly; the soundness of
`X_klein` never needed distinctness.  The Agda's `to-list` side conditions
of `viaN` (equality up to associativity) are equations of words here,
closed by `simp`.
-/
import QCert.XCXCCX4bit.CFrame
import QCert.XCXCCX4bit.CLabels
import QCert.XCXCCX4bit.Narrow3

namespace QCert.XCXCCX4bit.CRel

open QCert QCert.Circuit CircuitProp IndepProp
open Placed (PG Wire ι ιs every avoids semPs ιX₀ conj_mul cl4)
open ToPlaced (pg pg_ok)
open PFrames CBase CFrame CLabels
open Coxeter (frame)

/-! ## Tables -/

/-- The `i`-th entry of a list, `d` beyond its end (the Agda's `lookup`). -/
def nthD {α : Type} (d : α) : List α → ℕ → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: as, i + 1 => nthD d as i

/-- Two positions are distinct. -/
def avoid? (t : Fin 8) : List (Fin 8) → Bool
  | [] => true
  | x :: xs => !eq8 t x && avoid? t xs

/-- The positions of a list are distinct. -/
def distinct? : List (Fin 8) → Bool
  | [] => true
  | t :: ts => avoid? t ts && distinct? ts

/-- The frame of a list of distinct positions (`ε` otherwise). -/
def frameD (ts : List (Fin 8)) : CW 8 := bif distinct? ts then frame ts else 1

/-! ## Labels -/

abbrev L : Type := Fin 105

def frm (i : L) : CW 8 := nthD 1 frmT i.1

/-- The controlled matching of a label. -/
def Xm (i : L) : Circ 4 := Fr G (frm i)

def tbl (i : L) (x : Fin 8) : Fin 8 := nthD 0 (nthD [] tblT i.1) x.1

/-- The first table (from index `k`) that agrees with `f`. -/
def findIn (f : Fin 8 → Fin 8) : List (List (Fin 8)) → ℕ → Option ℕ
  | [], _ => none
  | t :: ts, k => bif all8 (fun x => eq8 (nthD 0 t x.1) (f x)) then some k else findIn f ts (k + 1)

private def toL (k : ℕ) : Option L := if h : k < 105 then some ⟨k, h⟩ else none

/-- The label of a matching given as a function. -/
def find (f : Fin 8 → Fin 8) : Option L := (findIn f tblT 0).bind toL

/-- `x y x` … -/
def c3 (x y : L) : L := (find fun p => tbl x (tbl y (tbl x p))).getD x

/-- … and `x y`. -/
def mul (x y : L) : L := (find fun p => tbl x (tbl y p)).getD x

/-- Equality of labels, decided (the Agda's `_==ᴸ_`). -/
def eqLab (x y : L) : Bool := Nat.beq x.1 y.1

theorem eqLab_sound (x y : L) (h : eqLab x y = true) : x = y :=
  Fin.ext (Nat.eq_of_beq_eq_true h)

/-! ## Frames -/

theorem Fr_cong {a b : Circ 4} (F : CW 8) (e : 4 ⊢ a ≈ b) : 4 ⊢ Fr a F ≈ Fr b F :=
  ((Derivable.refl _).mul e).mul (Derivable.refl _)

/-- The Agda's `Fr-•`. -/
theorem Fr_mul (a b : Circ 4) (F : CW 8) : 4 ⊢ Fr a F * Fr b F ≈ Fr (a * b) F :=
  conj_mul (Pc_inv' 0 le_rfl F) a b

theorem Fr_one (b : Circ 4) : Fr b 1 = b := by
  simp only [Fr, Coxeter.Circuits.Fr, Coxeter.inv_one, map_one, one_mul, mul_one]

theorem Fr_invol {b : Circ 4} (F : CW 8) (e : 4 ⊢ b * b ≈ 1) : 4 ⊢ Fr b F * Fr b F ≈ 1 := by
  refine (Fr_mul b b F).trans ((Fr_cong F e).trans ?_)
  show 4 ⊢ Pc 0 F * 1 * Pc 0 (inv F) ≈ 1
  rw [mul_one]
  exact Pc_inv 0 le_rfl F

theorem Fr_comm {a b : Circ 4} (F : CW 8) (h : Comm a b) : Comm (Fr a F) (Fr b F) :=
  (Fr_mul a b F).trans ((Fr_cong F h).trans (Fr_mul b a F).symm)

/-- The Agda's `comm-≈ʳ`. -/
theorem comm_eqv_r {a b b' : Circ 4} (e : 4 ⊢ b ≈ b') (h : Comm a b') : Comm a b :=
  comm_sym (comm_eqv e (comm_sym h))

/-! ## Small identities on few wires -/

/-- An identity of placed words on three wires. -/
private theorem nar (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (hs : eqF 4 (semPs u) (semPs v) = true) :
    4 ⊢ ιs u ≈ ιs v :=
  Narrow3.narrowP m u v hu hv (eqF_sound 4 _ _ hs)

/-- The same, between circuits with the same letters. -/
private theorem viaN {a b : Circ 4} (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (hs : eqF 4 (semPs u) (semPs v) = true) (p : a = ιs u)
    (q : ιs v = b) : 4 ⊢ a ≈ b := by
  rw [p, ← q]
  exact nar m u v hu hv hs

theorem GG : 4 ⊢ G * G ≈ 1 :=
  viaN 1 [PG.CXₚ 3 0, PG.CXₚ 3 0] [] rfl rfl (by decide +kernel) (by simp only [G, ιs, mul_one])
    rfl

theorem GbarGbar : 4 ⊢ Gbar * Gbar ≈ 1 :=
  viaN 1 [PG.Xₚ 3, PG.CXₚ 3 0, PG.Xₚ 3, PG.Xₚ 3, PG.CXₚ 3 0, PG.Xₚ 3] [] rfl rfl
    (by decide +kernel) (by simp only [Gbar, G, ιs, mul_one, mul_assoc]) rfl

theorem X₀X₀ : 4 ⊢ ι (.Xₚ 0) * ι (.Xₚ 0) ≈ 1 :=
  viaN 1 [PG.Xₚ 0, PG.Xₚ 0] [] rfl rfl (by decide +kernel) (by simp only [ιs, mul_one]) rfl

/-- `G` is `X` on wire 0 times `Gbar` (the Agda's `split`) … -/
theorem splitG : 4 ⊢ G ≈ ι (.Xₚ 0) * Gbar :=
  viaN 1 [PG.CXₚ 3 0] [PG.Xₚ 0, PG.Xₚ 3, PG.CXₚ 3 0, PG.Xₚ 3] rfl rfl (by decide +kernel)
    (by simp only [G, ιs, mul_one]) (by simp only [Gbar, G, ιs, mul_one, mul_assoc])

/-- … in either order. -/
theorem splitG_comm : Comm (ι (.Xₚ 0)) Gbar :=
  viaN 1 [PG.Xₚ 0, PG.Xₚ 3, PG.CXₚ 3 0, PG.Xₚ 3] [PG.Xₚ 3, PG.CXₚ 3 0, PG.Xₚ 3, PG.Xₚ 0] rfl rfl
    (by decide +kernel) (by simp only [Gbar, G, ιs, mul_one, mul_assoc])
    (by simp only [Gbar, G, ιs, mul_one, mul_assoc])

/-- `X` on wire 0 is the product of the four flips. -/
def w₀ : CW 8 := FreeMonoid.of s₀ * FreeMonoid.of s₂ * FreeMonoid.of s₄ * FreeMonoid.of s₆

theorem X₀_w₀ : 4 ⊢ ι (.Xₚ 0) ≈ Pc 0 w₀ := by
  have e := P_eq (w := X) (v := Width3.T 0 * Width3.T 2 * Width3.T 4 * Width3.T 6)
    (eqF_sound 3 _ _ (by decide +kernel))
  simp only [map_mul] at e
  rw [w₀, map_mul, map_mul, map_mul]
  exact ιX₀.trans e

private theorem comm_X₃_gen : ∀ g : Gn 3, Comm (Circuit.pad 1 (FreeMonoid.of g)) (ι (.Xₚ 3))
  | .gate0 (.gate g) => nomatch g
  | .gate1 (.gate .X_gate) => comm_circ _ (.Xₚ 3) rfl
  | .gate2 (.gate .CX_gate) => comm_circ _ (.Xₚ 3) rfl
  | .gate2 .swap => comm_circ _ (.Xₚ 3) rfl
  | .gate3 (.gate .CCX_gate) => comm_circ _ (.Xₚ 3) rfl
  | .up (.gate0 (.gate g)) => nomatch g
  | .up (.gate1 (.gate .X_gate)) => comm_circ _ (.Xₚ 3) rfl
  | .up (.gate2 (.gate .CX_gate)) => comm_circ _ (.Xₚ 3) rfl
  | .up (.gate2 .swap) => comm_circ _ (.Xₚ 3) rfl
  | .up (.up (.gate0 (.gate g))) => nomatch g
  | .up (.up (.gate1 (.gate .X_gate))) => comm_circ _ (.Xₚ 3) rfl
  | .up (.up (.up (.gate0 (.gate g)))) => nomatch g

/-- A three-wire circuit on the lower wires commutes with `X` on wire 3. -/
theorem comm_X₃ (w : Circ 3) : Comm (Circuit.pad 1 w) (ι (.Xₚ 3)) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact comm_ε
  | mul_of g w ih =>
    rw [map_mul]
    exact comm_mul (comm_X₃_gen g) ih

/-- So does the circuit of a Coxeter word … -/
theorem comm_Pc_X₃ (r : CW 8) : Comm (Pc 0 r) (ι (.Xₚ 3)) := by
  rw [Pc_down]
  exact comm_X₃ _

/-- Commuting with `μ₀`, decided. -/
def inC? (r : CW 8) : Bool := all8 fun x => eq8 (actF r (μ₀ x)) (μ₀ (actF r x))

theorem inC_sound (r : CW 8) (h : inC? r = true) : InC r := fun x => by
  have := eq8_sound _ _ (all8_sound (fun y => eq8 (actF r (μ₀ y)) (μ₀ (actF r y))) h x)
  rwa [actF_ok, actF_ok] at this

/-- … and if its permutation commutes with `μ₀` it commutes with `Gbar`. -/
theorem comm_Pc_Gbar (r : CW 8) (h : inC? r = true) : Comm (Pc 0 r) Gbar :=
  commGbar (W_core r (inC_sound r h)) (comm_Pc_X₃ r)

/-! ## The side conditions, decided on the labels -/

/-- The orbit word of a label. -/
def orbC (m : L) : CW 8 := nthD 1 orbCT m.1

/-- The base type of a label. -/
def orbK (m : L) : Fin 5 := nthD 0 orbKT m.1

private def bc_ok (F : CW 8) : Option L → Bool
  | some m => eqMatch F (orbC m * baseW (orbK m)) && (inC? (orbC m) && inC? (inv (orbC m)))
  | none => false

/-- `Gbar` against a frame of `G`, through the orbit table. -/
def BC₀_ok (F : CW 8) : Bool := bc_ok F (find (matchF F))

/-- `Qbar x` against `Xm y`. -/
def BC_ok (x y : L) : Bool :=
  eqMatch (frm x * (inv (frm x) * frm y)) (frm y) && BC₀_ok (inv (frm x) * frm y)

/-- The word of the lower part of `Xm x`, the matching `x` on both halves. -/
def cP (F : CW 8) : CW 8 := F * (w₀ * inv F)

/-- The side condition of conjugation. -/
def conj_ok (x y : L) : Bool := eqMatch (cP (frm x) * frm y) (frm (c3 x y)) && BC_ok x y

/-- The positions outside the orbit of `0` under `x` and `y`. -/
private def kout (x y : L) (p : Fin 8) : Bool :=
  !eq8 p 0 && (!eq8 p (tbl x 0) && (!eq8 p (tbl y 0) && !eq8 p (tbl x (tbl y 0))))

private def kfirst (x y : L) : List (Fin 8) → Fin 8
  | [] => 0
  | p :: ps => bif kout x y p then p else kfirst x y ps

/-- The positions of the Klein four-group of `x` and `y`: the orbit of 0
and of the first position outside it. -/
def kleinList (x y : L) : List (Fin 8) :=
  let b := kfirst x y [1, 2, 3, 4, 5, 6, 7]
  [0, tbl x 0, tbl y 0, tbl x (tbl y 0), b, tbl x b, tbl y b, tbl x (tbl y b)]

/-- The flip of wire 1, placed by the swap of wires 0, 1. -/
def κw : CW 8 := FreeMonoid.ofList [s₁, s₂, s₁, s₄, s₅, s₄]

private def ko (x y : L) : Bool :=
  eqMatch (frm x) (frame (kleinList x y) * 1)
    && (eqMatch (frm y) (frame (kleinList x y) * baseW 1)
    && eqMatch (frm (mul x y)) (frame (kleinList x y) * κw))

/-- The side condition of `klein`. -/
def klein_ok (x y : L) : Bool := distinct? (kleinList x y) && ko x y

/-- The matching `x` controlled by wire 3 = 0 … -/
def Qbar (F : CW 8) : Circ 4 := Fr Gbar F

/-- … and on both halves. -/
def P (F : CW 8) : Circ 4 := Fr (ι (.Xₚ 0)) F

/-! ## The calculus, given the five base commutations -/

namespace Calculus

/-! ### Involution -/

theorem X_inv (x : L) : 4 ⊢ Xm x * Xm x ≈ 1 := Fr_invol (frm x) GG

variable (base : ∀ k : Fin 5, Comm Gbar (Fr G (baseW k)))
include base

/-! ### Block commutation -/

private theorem bc (F : CW 8) : ∀ mm : Option L, bc_ok F mm = true → Comm Gbar (Fr G F)
  | some m, h => by
    simp only [bc_ok, Bool.and_eq_true] at h
    have e := W' F _ h.1
    rw [← Fr_conj] at e
    exact comm_eqv_r e (comm_sym (comm_mul (comm_mul (comm_Pc_Gbar _ h.2.1)
      (comm_sym (base (orbK m)))) (comm_Pc_Gbar _ h.2.2)))
  | none, h => nomatch h

theorem BC₀ (F : CW 8) (h : BC₀_ok F = true) : Comm Gbar (Fr G F) :=
  bc base F (find (matchF F)) h

theorem BC (x y : L) (h : BC_ok x y = true) : Comm (Qbar (frm x)) (Xm y) := by
  simp only [BC_ok, Bool.and_eq_true] at h
  have e := W' _ _ h.1
  rw [← Fr_conj] at e
  exact comm_eqv_r e.symm (Fr_comm (frm x) (BC₀ base _ h.2))

/-! ### Conjugation -/

omit base in
private theorem X_PQ (F : CW 8) : 4 ⊢ Fr G F ≈ P F * Qbar F :=
  (Fr_cong F splitG).trans (Fr_mul _ _ F).symm

omit base in
private theorem X_QP (F : CW 8) : 4 ⊢ Fr G F ≈ Qbar F * P F :=
  (X_PQ F).trans (Fr_comm F splitG_comm)

omit base in
private theorem QbarQbar (F : CW 8) : 4 ⊢ Qbar F * Qbar F ≈ 1 := Fr_invol F GbarGbar

omit base in
private theorem PP (F : CW 8) : 4 ⊢ P F * P F ≈ 1 := Fr_invol F X₀X₀

omit base in
private theorem P_Pc (F : CW 8) : 4 ⊢ P F ≈ Pc 0 (cP F) := by
  rw [cP, map_mul, map_mul, ← mul_assoc]
  exact ((Derivable.refl _).mul X₀_w₀).mul (Derivable.refl _)

omit base in
/-- `P F` is also the circuit of the inverse word. -/
private theorem P_Pc' (F : CW 8) : 4 ⊢ P F ≈ Pc 0 (inv (cP F)) := by
  apply cl_eq.1
  have h₁ := cl_eq.2 (PP F)
  have h₂ : cl4 (P F) = cl4 (Pc 0 (cP F)) := cl_eq.2 (P_Pc F)
  have h₃ := cl_eq.2 (Pc_inv 0 le_rfl (cP F))
  simp only [cl_mul, cl_one] at h₁ h₃
  calc cl4 (P F) = cl4 (P F) * (cl4 (P F) * cl4 (Pc 0 (inv (cP F)))) := by
        rw [h₂, h₃, mul_one]
    _ = cl4 (Pc 0 (inv (cP F))) := by rw [← mul_assoc, h₁, one_mul]

theorem X_conj (x y : L) (h : conj_ok x y = true) : 4 ⊢ Xm x * Xm y * Xm x ≈ Xm (c3 x y) := by
  simp only [conj_ok, Bool.and_eq_true] at h
  have hw := W' _ _ h.1
  rw [← Fr_conj] at hw
  refine Derivable.trans ?_ hw
  apply cl_eq.1
  have e1 : cl4 (Xm x) = cl4 (P (frm x)) * cl4 (Qbar (frm x)) := by
    rw [← cl_mul]; exact cl_eq.2 (X_PQ (frm x))
  have e2 : cl4 (Xm x) = cl4 (Qbar (frm x)) * cl4 (P (frm x)) := by
    rw [← cl_mul]; exact cl_eq.2 (X_QP (frm x))
  have e3 : cl4 (Qbar (frm x)) * cl4 (Xm y) = cl4 (Xm y) * cl4 (Qbar (frm x)) := by
    rw [← cl_mul, ← cl_mul]; exact cl_eq.2 (BC base x y h.2)
  have e4 : cl4 (Qbar (frm x)) * cl4 (Qbar (frm x)) = 1 := by
    rw [← cl_mul, ← cl_one]; exact cl_eq.2 (QbarQbar (frm x))
  have e5 : cl4 (P (frm x)) = cl4 (Pc 0 (cP (frm x))) := cl_eq.2 (P_Pc (frm x))
  have e6 : cl4 (P (frm x)) = cl4 (Pc 0 (inv (cP (frm x)))) := cl_eq.2 (P_Pc' (frm x))
  simp only [cl_mul]
  calc cl4 (Xm x) * cl4 (Xm y) * cl4 (Xm x)
      = cl4 (P (frm x)) * cl4 (Qbar (frm x)) * cl4 (Xm y)
          * (cl4 (Qbar (frm x)) * cl4 (P (frm x))) := by rw [← e1, ← e2]
    _ = cl4 (P (frm x)) * (cl4 (Qbar (frm x)) * cl4 (Xm y)) * cl4 (Qbar (frm x))
          * cl4 (P (frm x)) := by simp only [mul_assoc]
    _ = cl4 (P (frm x)) * (cl4 (Xm y) * cl4 (Qbar (frm x))) * cl4 (Qbar (frm x))
          * cl4 (P (frm x)) := by rw [e3]
    _ = cl4 (P (frm x)) * cl4 (Xm y) * (cl4 (Qbar (frm x)) * cl4 (Qbar (frm x)))
          * cl4 (P (frm x)) := by simp only [mul_assoc]
    _ = cl4 (P (frm x)) * cl4 (Xm y) * cl4 (P (frm x)) := by rw [e4, mul_one]
    _ = cl4 (Pc 0 (cP (frm x))) * cl4 (Xm y) * cl4 (Pc 0 (inv (cP (frm x)))) := by
        rw [← e5, ← e6]

/-! ### Klein pairs -/

omit base in
private theorem pc_cx : 4 ⊢ Pc 0 (baseW 1) ≈ ιs [PG.CXₚ 0 1] :=
  (pg_ok _).trans (nar 3 _ _ (by decide +kernel) rfl (by decide +kernel))

omit base in
private theorem pc_cx' : 4 ⊢ Pc 0 (inv (baseW 1)) ≈ ιs [PG.CXₚ 0 1] :=
  (pg_ok _).trans (nar 3 _ _ (by decide +kernel) rfl (by decide +kernel))

omit base in
private theorem pc_sw : 4 ⊢ Pc 0 κw ≈ ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0] :=
  (pg_ok _).trans (nar 3 _ _ (by decide +kernel) rfl (by decide +kernel))

omit base in
private theorem pc_sw' : 4 ⊢ Pc 0 (inv κw) ≈ ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0] :=
  (pg_ok _).trans (nar 3 _ _ (by decide +kernel) rfl (by decide +kernel))

omit base in
/-- The standard Klein pair: `μ₀`, `μ₀` under `CX₀₁` and their product, the
flip of wire 1, as frames on wires 0, 1, 3. -/
private theorem klein_base : 4 ⊢ G * Fr G (baseW 1) ≈ Fr G κw := by
  have l : 4 ⊢ G * Fr G (baseW 1) ≈ ιs [PG.CXₚ 3 0, PG.CXₚ 0 1, PG.CXₚ 3 0, PG.CXₚ 0 1] := by
    refine ((Derivable.refl G).mul ((pc_cx.mul (Derivable.refl G)).mul pc_cx')).trans ?_
    rw [show G * (ιs [PG.CXₚ 0 1] * G * ιs [PG.CXₚ 0 1])
        = ιs [PG.CXₚ 3 0, PG.CXₚ 0 1, PG.CXₚ 3 0, PG.CXₚ 0 1] by
      simp only [G, ιs, mul_one, mul_assoc]]
  have m : 4 ⊢ ιs [PG.CXₚ 3 0, PG.CXₚ 0 1, PG.CXₚ 3 0, PG.CXₚ 0 1]
      ≈ ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0, PG.CXₚ 3 0, PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0] :=
    nar 2 _ _ rfl rfl (by decide +kernel)
  have r : 4 ⊢ ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0, PG.CXₚ 3 0, PG.CXₚ 1 0, PG.CXₚ 0 1,
      PG.CXₚ 1 0] ≈ Fr G κw := by
    refine Derivable.trans ?_ ((pc_sw.mul (Derivable.refl G)).mul pc_sw').symm
    rw [show ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0, PG.CXₚ 3 0, PG.CXₚ 1 0, PG.CXₚ 0 1,
        PG.CXₚ 1 0] = ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0] * G
          * ιs [PG.CXₚ 1 0, PG.CXₚ 0 1, PG.CXₚ 1 0] by
      simp only [G, ιs, mul_one, mul_assoc]]
  exact l.trans (m.trans r)

omit base in
private theorem kl (x y : L) (h : ko x y = true) : 4 ⊢ Xm x * Xm y ≈ Xm (mul x y) := by
  simp only [ko, Bool.and_eq_true] at h
  have ex := W' _ _ h.1
  have ey := W' _ _ h.2.1
  have ez := W' _ _ h.2.2
  rw [← Fr_conj] at ex ey ez
  refine (ex.mul ey).trans ((Fr_mul (Fr G 1) (Fr G (baseW 1)) _).trans
    ((Fr_cong _ ?_).trans ((Fr_cong _ klein_base).trans ez.symm)))
  rw [Fr_one]

omit base in
theorem X_klein (x y : L) (h : klein_ok x y = true) : 4 ⊢ Xm x * Xm y ≈ Xm (mul x y) := by
  simp only [klein_ok, Bool.and_eq_true] at h
  exact kl x y h.2

end Calculus

end QCert.XCXCCX4bit.CRel
