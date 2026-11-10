/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Placed gates on four wires: X, CX and CCX on any wires

Translation of `Placed.agda`.  `PG` is the alphabet of the theory's gates
placed on any wires of a four-wire circuit, with black controls (a white
control is `X` on its wire on either side).  Wire 0 is the bottom wire:

    Xₚ t          X on wire t;
    CXₚ c t       CX with control c and target t (c ≠ t);
    CCXₚ a b t    CCX with controls a < b and target t, all distinct.

Wires are elements of `Fin 4`, and a side condition is a proof that a
Boolean test holds, an auto-parameter that a closed letter fills by
`decide`: a script writes `PG.CCXₚ 1 3 0`, and a letter with two equal
wires or its controls out of order does not typecheck.

`ι` places a letter by conjugation with a swap network: its gate on the
bottom wires (target on wire 0, controls on wires 1 and 2) between the
circuit of a Coxeter word of `S₄` that sends 0, 1, 2 to the target and the
controls (Coxeter's `frame`) and its inverse.  The swaps `sw d` of wires `d`
and `d + 1` satisfy the Coxeter relations (`σ_inv`, Yang–Baxter, `comm2`:
`cox`), so by the frame lemma the placement depends only on where the word
sends those wires (`ι_X`, `ι_CX`, `ι_CCX`; for `CCX` also with its controls
exchanged, by rule (5): `ι_CCX'`).  So:

* a gate shifted `k` wires up is its placement by the `k`-th power of the
  cycle 0 → 1 → 2 → 3 (`shiftFr`, from naturality), and the letters on
  consecutive wires are the gates of `Syntactics` shifted up (`ιX₀`, …,
  `ιCCX₂₃₁`, and `ιCCX₂₃₀` for `CCX₃₂₀`);
* a relabelling of the wires (`Relabel`: a permutation `π` with a Coxeter
  word whose network `S` carries it out; `ρ4 a b c d` sends the wires 0, 1,
  2, 3 to `a, b, c, d`, `fromPerm` takes any injective map) is conjugation
  by its network, `ι (relabel R g) ≈ S R * ι g * Sinv R` (`relabel_ι`, for
  every letter at once; `relabel_ιs` on words);
* letters on disjoint wires commute (`disj_comm`): one network places both,
  the one as a gate on the bottom wires and the other as a gate shifted
  above it, which the structural comm rules exchange.

`semP` is the function of a letter on bit vectors; `sem (ι g) ≐ semP g` is
decided by evaluation, once for all 28 letters (`sem_ok`).  Rule (7) holds
for the placed letters under every relabelling (`rule7`).  Given
completeness on three wires (`Complete₃`; `Narrow3` applies the theorems
below to `Width3.complete₃`), two words of letters on three of the four
wires with the same function are equal (`narrow`): relabelled by the
transposition `τ m` so that the idle wire `m` is wire 3, their circuits are
three-wire circuits widened (`low_ιs`), and `pad₃` carries the three-wire
derivation back.  A triple of wires is given by the wire `m` it leaves out.

Words of letters are lists, in diagram order: `ιs (g :: u) = ι g * ιs u`.

Names.  The Agda's `Xᵖ`, `CXᵖ`, `CCXᵖ` are `PG.Xₚ`, `PG.CXₚ`, `PG.CCXₚ`;
`_==_`, `_<<_` are `weq`, `wlt`; `ι*`, `ιʷ` are `ιs`, `ιw`; `⟦_⟧ᵖ`, `⟦_⟧ᵖ*`
are `semP`, `semPs`; `S⁻` is `Sinv`; `X↑₁` is `X_up₁`; `narrowᵖ` is
`narrowP`; hyphens are underscores.  The Agda's module `Narrow
complete₃` is the section `Narrow`, whose theorems take `complete₃` as their
first argument.

**Deviations from the Agda.**

* Associativity and the units are those of the free monoid, so
  conjugation (`conj_mul`, `peel`) is reasoned about in the quotient
  monoid of the theory (`CircuitProp.cl`), and the Agda's `assoc` steps
  disappear.
* `Coxeter.frame` is total, so the distinctness of a letter's wires
  (`dX`, `dCX`, `dCCX`) is used only where `frame_act` is.
* The Agda's `w ↓ᵏ 1 : Circuit (n + 1)` is `Circuit.pad 1 w : Circ (1 + n)`,
  so a widened state appends its new bit with `snoc : Bits n → Bool →
  Bits (1 + n)` (the Agda's `x V.++ (b V.∷ V.[])`).  The Agda's `V.lookup`
  and `_[_]%=_` on states are `bget` and `bmod`, by the wire's number.
* `lowW` and `cutW` read a circuit through its list of letters
  (`List.all`, `FreeMonoid.map`).
-/
import QCert.XCXCCX4bit.Kit
import QCert.XCXCCX4bit.Semantics
import QCert.XCXCCX4bit.Coxeter

namespace QCert.XCXCCX4bit.Placed

open QCert QCert.Circuit CircuitProp IndepProp
open Coxeter Coxeter.Circuits

/-! ## Wires -/

/-- The wires of a four-wire circuit. -/
abbrev Wire : Type := Fin 4

/-- Equality of wires, decided (the Agda's `_==_`). -/
def weq (a b : Wire) : Bool := Nat.beq a.1 b.1

/-- Order of wires, decided (the Agda's `_<<_`). -/
def wlt (a b : Wire) : Bool := Nat.blt a.1 b.1

theorem weq_sound : ∀ {a b : Wire}, weq a b = true → a = b := by decide

theorem weq_refl : ∀ a : Wire, weq a a = true := by decide

theorem weq_iff : ∀ {a b : Wire}, weq a b = true ↔ a = b := by decide

/-- Distinct wires, from a Boolean test (the Agda's `neq`). -/
theorem neq : ∀ {a b : Wire}, (!weq a b) = true → a ≠ b := by decide

theorem not_weq_iff : ∀ {a b : Wire}, (!weq a b) = true ↔ a ≠ b := by decide

theorem wlt_neq : ∀ {a b : Wire}, wlt a b = true → a ≠ b := by decide

/-- Of two distinct wires not in order, the other way round (the Agda's
`<<-flip`). -/
theorem wlt_flip : ∀ (a b : Wire), a ≠ b → wlt a b = false → wlt b a = true := by decide

/-! ## Placed gates -/

def okCX (c t : Wire) : Bool := !weq c t

def okCCX (a b t : Wire) : Bool := wlt a b && (!weq a t && !weq b t)

theorem okCX_iff : ∀ {c t : Wire}, okCX c t = true ↔ c ≠ t := by decide

theorem okCCX_iff : ∀ {a b t : Wire}, okCCX a b t = true ↔ wlt a b = true ∧ a ≠ t ∧ b ≠ t := by
  decide

/-- The alphabet of placed letters. -/
inductive PG : Type
  /-- `X` on wire `t`. -/
  | Xₚ (t : Wire)
  /-- `CX` with control `c` and target `t`. -/
  | CXₚ (c t : Wire) (ok : okCX c t = true := by decide)
  /-- `CCX` with controls `a < b` and target `t`. -/
  | CCXₚ (a b t : Wire) (ok : okCCX a b t = true := by decide)

export PG (Xₚ CXₚ CCXₚ)

/-- The gate of a letter on the bottom wires. -/
def base : PG → Circ 4
  | .Xₚ _ => X
  | .CXₚ _ _ _ => CX
  | .CCXₚ _ _ _ _ => CCX

def arity : PG → ℕ
  | .Xₚ _ => 1
  | .CXₚ _ _ _ => 2
  | .CCXₚ _ _ _ _ => 3

/-- The wires of a letter: the target first, then the controls. -/
def wires : PG → List Wire
  | .Xₚ t => [t]
  | .CXₚ c t _ => [t, c]
  | .CCXₚ a b t _ => [t, a, b]

/-! ### The wires of a letter are distinct -/

theorem dX (t : Wire) : Distinct [t] := List.nodup_singleton t

theorem dCX : ∀ (c t : Wire), okCX c t = true → Distinct [t, c] := by decide

theorem ok_ab {a b t : Wire} (p : okCCX a b t = true) : wlt a b = true := (okCCX_iff.1 p).1

theorem ok_at {a b t : Wire} (p : okCCX a b t = true) : a ≠ t := (okCCX_iff.1 p).2.1

theorem ok_bt {a b t : Wire} (p : okCCX a b t = true) : b ≠ t := (okCCX_iff.1 p).2.2

theorem dCCX : ∀ (a b t : Wire), okCCX a b t = true → Distinct [t, a, b] := by decide

/-- Every element of a list satisfies `p`. -/
def every {A : Type} (p : A → Bool) : List A → Bool
  | [] => true
  | x :: xs => p x && every p xs

theorem every_iff {A : Type} (p : A → Bool) : ∀ xs : List A, every p xs = true ↔ ∀ x ∈ xs, p x = true
  | [] => by simp [every]
  | x :: xs => by simp [every, every_iff p xs]

/-- Does the letter leave wire `m` alone? -/
def avoids (m : Wire) : PG → Bool
  | .Xₚ t => !weq m t
  | .CXₚ c t _ => !weq m c && !weq m t
  | .CCXₚ a b t _ => !weq m a && (!weq m b && !weq m t)

/-- Two lists of wires with no wire in common. -/
def apart (xs ys : List Wire) : Bool := every (fun x => every (fun y => !weq x y) ys) xs

/-- Letters on disjoint wires (together on at most four). -/
def disjoint (g h : PG) : Bool := Nat.ble (arity g + arity h) 4 && apart (wires g) (wires h)

/-! ## Properties of every letter, decided -/

def all4 (p : Wire → Bool) : Bool := p 0 && (p 1 && (p 2 && p 3))

theorem all4_sound (p : Wire → Bool) (h : all4 p = true) : ∀ w, p w = true := by
  simp only [all4, Bool.and_eq_true] at h
  intro w
  match w with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | 2 => exact h.2.2.1
  | 3 => exact h.2.2.2

def implB : (b : Bool) → (b = true → Bool) → Bool
  | true, f => f rfl
  | false, _ => true

theorem implB_sound : ∀ (b : Bool) (f : b = true → Bool), implB b f = true → ∀ q, f q = true
  | true, _, h, _ => h

def pX (p : PG → Bool) (t : Wire) : Bool := p (.Xₚ t)

def pCX (p : PG → Bool) (c t : Wire) : Bool := implB (okCX c t) fun ok => p (.CXₚ c t ok)

def pCCX (p : PG → Bool) (a b t : Wire) : Bool := implB (okCCX a b t) fun ok => p (.CCXₚ a b t ok)

/-- `p` holds of every letter, checked on all 28. -/
def forallPG (p : PG → Bool) : Bool :=
  all4 (pX p) && (all4 (fun c => all4 (pCX p c)) && all4 (fun a => all4 (fun b => all4 (pCCX p a b))))

theorem forallPG_sound (p : PG → Bool) (h : forallPG p = true) : ∀ g, p g = true := by
  simp only [forallPG, Bool.and_eq_true] at h
  intro g
  match g with
  | .Xₚ t => exact all4_sound _ h.1 t
  | .CXₚ c t ok => exact implB_sound _ _ (all4_sound _ (all4_sound _ h.2.1 c) t) ok
  | .CCXₚ a b t ok =>
    exact implB_sound _ _ (all4_sound _ (all4_sound _ (all4_sound _ h.2.2 a) b) t) ok

/-! ## Swap networks -/

/-- The swap of wires `d` and `d + 1`. -/
def sw : ℕ → Circ 4
  | 0 => σ
  | 1 => shift σ
  | 2 => shift (shift σ)
  | _ => 1

/-- The swaps satisfy the Coxeter relations of `S₄`. -/
theorem cox : Circuits.Coxeter 4 sw (VRel SRel 4) where
  order i hi := match i, hi with
    | 0, _ => σ_invol
    | 1, _ => by
      have := lemma_cong_up (σ_invol (Gate := PGate Gate) (SRel := SRel) (n := 1))
      simpa only [map_mul, map_one] using this
    | 2, _ => by
      have := lemma_cong_up (lemma_cong_up (σ_invol (Gate := PGate Gate) (SRel := SRel) (n := 0)))
      simpa only [map_mul, map_one] using this
    | _ + 3, h => absurd h (by omega)
  braid i hi := match i, hi with
    | 0, _ => by
      show 4 ⊢ σ * shift σ * σ ≈ shift σ * σ * shift σ
      rw [mul_assoc]; exact yang_baxter
    | 1, _ => by
      have := lemma_cong_up (yang_baxter (Gate := PGate Gate) (SRel := SRel) (n := 0))
      simp only [map_mul] at this
      show 4 ⊢ shift σ * shift (shift σ) * shift σ ≈ shift (shift σ) * shift σ * shift (shift σ)
      rw [mul_assoc]; exact this
    | _ + 2, h => absurd h (by omega)
  far i j hij hj := match i, j, hij, hj with
    | 0, 2, _, _ => (Derivable.of (Lift.comm2 PGate.swap (Gen.gate2 (n := 0) PGate.swap))).symm
    | 0, 0, h, _ => absurd h (by omega)
    | 0, 1, h, _ => absurd h (by omega)
    | 0, _ + 3, _, h => absurd h (by omega)
    | _ + 1, 0, h, _ => absurd h (by omega)
    | _ + 1, 1, h, _ => absurd h (by omega)
    | _ + 1, 2, h, _ => absurd h (by omega)
    | _ + 1, _ + 3, _, h => absurd h (by omega)

/-- The generators of `S₄` on the wires 0 1, 1 2 and 2 3. -/
def s₀ : SG 4 := ⟨0, by decide⟩
def s₁ : SG 4 := ⟨1, by decide⟩
def s₂ : SG 4 := ⟨2, by decide⟩

/-- The cycle 0 → 1 → 2 → 3 → 0 of the wires: its network is `σ⁻[ 3 ]`. -/
def Fc : CW 4 := FreeMonoid.of s₀ * (FreeMonoid.of s₁ * FreeMonoid.of s₂)

/-! ### The bottom gates commute with the swaps above them -/

theorem cX : CommGe 4 sw (VRel SRel 4) 1 X := fun i hi hi' => match i, hi, hi' with
  | 1, _, _ => Derivable.of (Lift.comm1 (PGate.gate Gate.X_gate) (Gen.gate2 (n := 1) PGate.swap))
  | 2, _, _ =>
    Derivable.of (Lift.comm1 (PGate.gate Gate.X_gate) (Gen.gate2 (n := 0) PGate.swap).up)
  | 0, h, _ => absurd h (by omega)
  | _ + 3, _, h => absurd h (by omega)

theorem cCX : CommGe 4 sw (VRel SRel 4) 2 CX := fun i hi hi' => match i, hi, hi' with
  | 2, _, _ => Derivable.of (Lift.comm2 (PGate.gate Gate.CX_gate) (Gen.gate2 (n := 0) PGate.swap))
  | 0, h, _ => absurd h (by omega)
  | 1, h, _ => absurd h (by omega)
  | _ + 3, _, h => absurd h (by omega)

theorem cCCX : CommGe 4 sw (VRel SRel 4) 3 CCX := fun i hi hi' => absurd hi' (by omega)

/-! ## Placing a letter -/

/-- A letter, placed by a swap network. -/
def ι : PG → Circ 4
  | .Xₚ t => Fr sw X (frame [t])
  | .CXₚ c t _ => Fr sw CX (frame [t, c])
  | .CCXₚ a b t _ => Fr sw CCX (frame [t, a, b])

/-- A list of letters, in diagram order (the Agda's `ι*`). -/
def ιs : List PG → Circ 4
  | [] => 1
  | g :: u => ι g * ιs u

/-- A word of letters (the Agda's `ιʷ`). -/
def ιw (w : Word PG) : Circ 4 := ιs (FreeMonoid.toList w)

theorem ιs_append : ∀ xs ys : List PG, ιs (xs ++ ys) = ιs xs * ιs ys
  | [], _ => (one_mul _).symm
  | x :: xs, ys => by rw [List.cons_append, ιs, ιs, ιs_append xs ys, mul_assoc]

theorem ιw_mul (u v : Word PG) : ιw (u * v) = ιw u * ιw v := by
  simp only [ιw, FreeMonoid.toList_mul, ιs_append]

theorem ιw_ofList (u : List PG) : ιw (FreeMonoid.ofList u) = ιs u := by
  simp only [ιw, FreeMonoid.toList_ofList]

/-! ## The function of a letter -/

/-- The bit on a wire of a state (the Agda's `V.lookup`). -/
def bget : {n : ℕ} → Bits n → ℕ → Bool
  | _, .nil, _ => false
  | _, a ∷ _, 0 => a
  | _, _ ∷ x, i + 1 => bget x i

/-- A state with the bit on a wire changed by `f` (the Agda's `_[_]%=_`). -/
def bmod : {n : ℕ} → Bits n → ℕ → (Bool → Bool) → Bits n
  | _, .nil, _, _ => .nil
  | _, a ∷ x, 0, f => f a ∷ x
  | _, a ∷ x, i + 1, f => a ∷ bmod x i f

/-- The function of a letter (the Agda's `⟦_⟧ᵖ`). -/
def semP : PG → Fun 4
  | .Xₚ t, x => bmod x t.1 (!·)
  | .CXₚ c t _, x => bmod x t.1 (· ^^ bget x c.1)
  | .CCXₚ a b t _, x => bmod x t.1 (· ^^ (bget x a.1 && bget x b.1))

/-- The function of a list of letters, in diagram order (the Agda's
`⟦_⟧ᵖ*`). -/
def semPs : List PG → Fun 4
  | [], x => x
  | g :: u, x => semPs u (semP g x)

theorem semPs_append (xs ys : List PG) (x : Bits 4) :
    semPs (xs ++ ys) x = semPs ys (semPs xs x) := by
  induction xs generalizing x with
  | nil => rfl
  | cons g xs ih => exact ih (semP g x)

private theorem sem_check : forallPG (fun g => eqF 4 (sem (ι g)) (semP g)) = true := by
  decide +kernel

/-- A placed letter computes its function. -/
theorem sem_ok (g : PG) : sem (ι g) ≐ semP g :=
  eqF_sound 4 _ _ (forallPG_sound (fun g => eqF 4 (sem (ι g)) (semP g)) sem_check g)

theorem ιs_sem : ∀ u : List PG, sem (ιs u) ≐ semPs u
  | [] => feq_refl
  | g :: u => fun x => by
    show sem (ι g * ιs u) x = semPs u (semP g x)
    rw [sem_mul, sem_ok g x, ιs_sem u]

/-! ## Conjugation -/

/-- The class of a four-wire circuit in the quotient monoid of the theory. -/
abbrev cl4 (w : Circ 4) := cl (PropRel SRel) 4 w

theorem Fr_cong {b b' : Circ 4} (F : CW 4) (e : 4 ⊢ b ≈ b') : 4 ⊢ Fr sw b F ≈ Fr sw b' F :=
  ((Derivable.refl _).mul e).mul (Derivable.refl _)

section Conj

variable {P Pinv : Circ 4} (inv_l : 4 ⊢ Pinv * P ≈ 1)
include inv_l

/-- Conjugation by `P` is multiplicative ... -/
theorem conj_mul (a b : Circ 4) : 4 ⊢ (P * a * Pinv) * (P * b * Pinv) ≈ P * (a * b) * Pinv := by
  apply cl_eq.1
  have h := cl_eq.2 inv_l
  simp only [cl_mul, cl_one] at h ⊢
  calc cl4 P * cl4 a * cl4 Pinv * (cl4 P * cl4 b * cl4 Pinv)
      = cl4 P * cl4 a * (cl4 Pinv * cl4 P) * cl4 b * cl4 Pinv := by simp only [mul_assoc]
    _ = cl4 P * (cl4 a * cl4 b) * cl4 Pinv := by rw [h, mul_one]; simp only [mul_assoc]

/-- ... and cancels. -/
theorem peel (a : Circ 4) : 4 ⊢ Pinv * (P * a * Pinv) * P ≈ a := by
  apply cl_eq.1
  have h := cl_eq.2 inv_l
  simp only [cl_mul, cl_one] at h ⊢
  calc cl4 Pinv * (cl4 P * cl4 a * cl4 Pinv) * cl4 P
      = (cl4 Pinv * cl4 P) * cl4 a * (cl4 Pinv * cl4 P) := by simp only [mul_assoc]
    _ = cl4 a := by rw [h, one_mul, mul_one]

theorem unconj {a b : Circ 4} (e : 4 ⊢ P * a * Pinv ≈ P * b * Pinv) : 4 ⊢ a ≈ b :=
  (peel inv_l a).symm.trans ((((Derivable.refl _).mul e).mul (Derivable.refl _)).trans (peel inv_l b))

end Conj

/-! ## A placement depends only on where the network sends the gate's wires -/

theorem ι_X (t : Wire) (F : CW 4) (h₀ : act F 0 = t) : 4 ⊢ ι (.Xₚ t) ≈ Fr sw X F :=
  frame_eq cox 1 3 le_rfl X cX (frame [t]) F fun x hx => by
    match x, hx with
    | ⟨0, _⟩, _ => exact (frame_act [t] (dX t) 0 t rfl).trans h₀.symm
    | ⟨k + 1, _⟩, h => exact absurd (show k + 1 < 1 from h) (by omega)

theorem ι_CX (c t : Wire) {ok : okCX c t = true} (F : CW 4) (h₀ : act F 0 = t)
    (h₁ : act F 1 = c) : 4 ⊢ ι (.CXₚ c t ok) ≈ Fr sw CX F :=
  frame_eq cox 2 2 le_rfl CX cCX (frame [t, c]) F fun x hx => by
    match x, hx with
    | ⟨0, _⟩, _ => exact (frame_act [t, c] (dCX c t ok) 0 t rfl).trans h₀.symm
    | ⟨1, _⟩, _ => exact (frame_act [t, c] (dCX c t ok) 1 c rfl).trans h₁.symm
    | ⟨k + 2, _⟩, h => exact absurd (show k + 2 < 2 from h) (by omega)

theorem ι_CCX (a b t : Wire) {ok : okCCX a b t = true} (F : CW 4) (h₀ : act F 0 = t)
    (h₁ : act F 1 = a) (h₂ : act F 2 = b) : 4 ⊢ ι (.CCXₚ a b t ok) ≈ Fr sw CCX F :=
  frame_eq cox 3 1 le_rfl CCX cCCX (frame [t, a, b]) F fun x hx => by
    match x, hx with
    | ⟨0, _⟩, _ => exact (frame_act [t, a, b] (dCCX a b t ok) 0 t rfl).trans h₀.symm
    | ⟨1, _⟩, _ => exact (frame_act [t, a, b] (dCCX a b t ok) 1 a rfl).trans h₁.symm
    | ⟨2, _⟩, _ => exact (frame_act [t, a, b] (dCCX a b t ok) 2 b rfl).trans h₂.symm
    | ⟨k + 3, _⟩, h => exact absurd (show k + 3 < 3 from h) (by omega)

/-- Rule (5) on the bottom wires of four. -/
theorem r5_4 : 4 ⊢ shift σ * CCX * shift σ ≈ CCX := ax_at SRel.r5 1

/-- `CCX` does not see the order of its controls (rule (5)). -/
theorem ι_CCX' (a b t : Wire) {ok : okCCX a b t = true} (F : CW 4) (h₀ : act F 0 = t)
    (h₁ : act F 1 = b) (h₂ : act F 2 = a) : 4 ⊢ ι (.CCXₚ a b t ok) ≈ Fr sw CCX F := by
  have e := ι_CCX a b t (ok := ok) (F * FreeMonoid.of s₁) (by rw [act_mul]; exact h₀)
    (by rw [act_mul]; exact h₂) (by rw [act_mul]; exact h₁)
  rw [← Fr_conj] at e
  exact e.trans (((Derivable.refl _).mul r5_4).mul (Derivable.refl _))

/-! ## A gate shifted up is its placement by the cycle of the wires -/

theorem Pc_Fc : Pc sw 0 Fc = (σcInv 3 : Circ 4) := rfl

theorem Pc_inv_Fc : Pc sw 0 (inv Fc) = (σc 3 : Circ 4) := rfl

/-- `σ⁻[ 3 ]` and `σ[ 3 ]` are the networks of `Fc` and its inverse, and a
three-wire circuit passes `σ[ 3 ]` one wire up (naturality, `nat₃`). -/
theorem shiftFr (w : Circ 3) : 4 ⊢ shift (Circuit.pad 0 w) ≈ Fr sw (Circuit.pad 1 w) Fc := by
  have h1 : 4 ⊢ (σcInv 3 : Circ 4) * σc 3 ≈ 1 := σInvσ 3
  have h2 : 4 ⊢ Circuit.pad 1 w * σc 3 ≈ σc 3 * shift (Circuit.pad 0 w) := nat₃ (n := 0) w
  apply cl_eq.1
  have h1 := cl_eq.2 h1
  have h2 := cl_eq.2 h2
  unfold Fr
  rw [Pc_Fc, Pc_inv_Fc]
  simp only [cl_mul, cl_one] at h1 h2 ⊢
  rw [mul_assoc, h2, ← mul_assoc, h1, one_mul]

theorem X_up₁ : 4 ⊢ shift X ≈ Fr sw X Fc := shiftFr X

theorem X_up₂ : 4 ⊢ shift (shift X) ≈ Fr sw X (Fc * Fc) := by
  have a : 4 ⊢ shift (shift X) ≈ Fr sw (shift X) Fc := shiftFr (shift X)
  have b := Fr_cong Fc X_up₁
  have c : Fr sw (Fr sw X Fc) Fc = Fr sw X (Fc * Fc) := Fr_conj X Fc Fc
  rw [c] at b
  exact a.trans b

theorem X_up₃ : 4 ⊢ shift (shift (shift X)) ≈ Fr sw X (Fc * (Fc * Fc)) := by
  have a : 4 ⊢ shift (shift (shift X)) ≈ Fr sw (shift (shift X)) Fc := shiftFr (shift (shift X))
  have b := Fr_cong Fc X_up₂
  have c : Fr sw (Fr sw X (Fc * Fc)) Fc = Fr sw X (Fc * (Fc * Fc)) := Fr_conj X Fc (Fc * Fc)
  rw [c] at b
  exact a.trans b

theorem CX_up₁ : 4 ⊢ shift CX ≈ Fr sw CX Fc := shiftFr CX

theorem CX_up₂ : 4 ⊢ shift (shift CX) ≈ Fr sw CX (Fc * Fc) := by
  have a : 4 ⊢ shift (shift CX) ≈ Fr sw (shift CX) Fc := shiftFr (shift CX)
  have b := Fr_cong Fc CX_up₁
  have c : Fr sw (Fr sw CX Fc) Fc = Fr sw CX (Fc * Fc) := Fr_conj CX Fc Fc
  rw [c] at b
  exact a.trans b

theorem CCX_up₁ : 4 ⊢ shift CCX ≈ Fr sw CCX Fc := shiftFr CCX

/-! ### Letters on consecutive wires, in the gate's own order, are the gates
shifted up -/

theorem ιX₀ : 4 ⊢ ι (.Xₚ 0) ≈ X := ι_X 0 1 rfl

theorem ιX₁ : 4 ⊢ ι (.Xₚ 1) ≈ shift X := (ι_X 1 Fc (by decide)).trans X_up₁.symm

theorem ιX₂ : 4 ⊢ ι (.Xₚ 2) ≈ shift (shift X) := (ι_X 2 (Fc * Fc) (by decide)).trans X_up₂.symm

theorem ιX₃ : 4 ⊢ ι (.Xₚ 3) ≈ shift (shift (shift X)) :=
  (ι_X 3 (Fc * (Fc * Fc)) (by decide)).trans X_up₃.symm

theorem ιCX₁₀ : 4 ⊢ ι (.CXₚ 1 0) ≈ CX := ι_CX 1 0 1 rfl rfl

theorem ιCX₂₁ : 4 ⊢ ι (.CXₚ 2 1) ≈ shift CX := (ι_CX 2 1 Fc (by decide) (by decide)).trans CX_up₁.symm

theorem ιCX₃₂ : 4 ⊢ ι (.CXₚ 3 2) ≈ shift (shift CX) :=
  (ι_CX 3 2 (Fc * Fc) (by decide) (by decide)).trans CX_up₂.symm

theorem ιCCX₁₂₀ : 4 ⊢ ι (.CCXₚ 1 2 0) ≈ CCX := ι_CCX 1 2 0 1 rfl rfl rfl

theorem ιCCX₂₃₁ : 4 ⊢ ι (.CCXₚ 2 3 1) ≈ shift CCX :=
  (ι_CCX 2 3 1 Fc (by decide) (by decide) (by decide)).trans CCX_up₁.symm

/-- The paper's `CCX_{12→4}` on four wires. -/
theorem ιCCX₂₃₀ : 4 ⊢ ι (.CCXₚ 2 3 0) ≈ CCX₃₂₀ := by
  have e := ι_CCX 2 3 0 (ok := by decide) (FreeMonoid.of s₀ * Fc) (by decide) (by decide)
    (by decide)
  rw [← Fr_conj] at e
  exact e.trans (((Derivable.refl _).mul CCX_up₁.symm).mul (Derivable.refl _))

/-! ## Relabelling the wires -/

/-- A permutation of the wires, with a Coxeter word whose network carries it
out. -/
structure Relabel where
  π : Wire → Wire
  net : CW 4
  net_π : ∀ w, act net w = π w

theorem Relabel.π_inj (R : Relabel) {a b : Wire} (e : R.π a = R.π b) : a = b := by
  rw [← act_inv R.net a, R.net_π a, e, ← R.net_π b, act_inv]

/-- The network of a relabelling. -/
def S (R : Relabel) : Circ 4 := Pc sw 0 R.net

/-- … and its inverse. -/
def Sinv (R : Relabel) : Circ 4 := Pc sw 0 (inv R.net)

theorem S_Sinv (R : Relabel) : 4 ⊢ S R * Sinv R ≈ 1 := Pc_inv cox 0 le_rfl R.net

theorem Sinv_S (R : Relabel) : 4 ⊢ Sinv R * S R ≈ 1 := Pc_inv' cox 0 le_rfl R.net

/-! ### `CCX` with controls `x` and `y` in either order, and target `z` -/

theorem ok_tt (x y z : Wire) (e : true = wlt x y) (xz : x ≠ z) (yz : y ≠ z) :
    okCCX x y z = true :=
  okCCX_iff.2 ⟨e.symm, xz, yz⟩

theorem ok_ff (x y z : Wire) (e : false = wlt x y) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) :
    okCCX y x z = true :=
  okCCX_iff.2 ⟨wlt_flip x y xy e.symm, yz, xz⟩

/-- The Agda's `ccx-by`. -/
def ccxBy (x y z : Wire) : (o : Bool) → o = wlt x y → x ≠ y → x ≠ z → y ≠ z → PG
  | true, e, _, xz, yz => .CCXₚ x y z (ok_tt x y z e xz yz)
  | false, e, xy, xz, yz => .CCXₚ y x z (ok_ff x y z e xy xz yz)

def ccx (x y z : Wire) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) : PG :=
  ccxBy x y z (wlt x y) rfl xy xz yz

theorem ι_ccxBy (x y z : Wire) : ∀ (o : Bool) (e : o = wlt x y) (xy : x ≠ y) (xz : x ≠ z)
    (yz : y ≠ z) (F : CW 4), act F 0 = z → act F 1 = x → act F 2 = y →
    4 ⊢ ι (ccxBy x y z o e xy xz yz) ≈ Fr sw CCX F
  | true, _, _, _, _, F, h₀, h₁, h₂ => ι_CCX x y z F h₀ h₁ h₂
  | false, _, _, _, _, F, h₀, h₁, h₂ => ι_CCX' y x z F h₀ h₁ h₂

theorem avoids_ccxBy (x y z : Wire) : ∀ (o : Bool) (e : o = wlt x y) (xy : x ≠ y) (xz : x ≠ z)
    (yz : y ≠ z) (m : Wire),
    avoids m (ccxBy x y z o e xy xz yz) = (!weq m x && (!weq m y && !weq m z))
  | true, _, _, _, _, _ => rfl
  | false, _, _, _, _, m => by
    show (!weq m y && (!weq m x && !weq m z)) = _
    cases weq m x <;> cases weq m y <;> rfl

section Relabelling

variable (R : Relabel)

theorem ok_π (c t : Wire) (ok : okCX c t = true) : okCX (R.π c) (R.π t) = true :=
  okCX_iff.2 fun e => okCX_iff.1 ok (R.π_inj e)

theorem π_ab {a b t : Wire} (ok : okCCX a b t = true) : R.π a ≠ R.π b :=
  fun e => wlt_neq (ok_ab ok) (R.π_inj e)

theorem π_at {a b t : Wire} (ok : okCCX a b t = true) : R.π a ≠ R.π t :=
  fun e => ok_at ok (R.π_inj e)

theorem π_bt {a b t : Wire} (ok : okCCX a b t = true) : R.π b ≠ R.π t :=
  fun e => ok_bt ok (R.π_inj e)

/-- A letter with its wires relabelled (the controls of `CCX` re-sorted). -/
def relabel : PG → PG
  | .Xₚ t => .Xₚ (R.π t)
  | .CXₚ c t ok => .CXₚ (R.π c) (R.π t) (ok_π R c t ok)
  | .CCXₚ a b t ok => ccx (R.π a) (R.π b) (R.π t) (π_ab R ok) (π_at R ok) (π_bt R ok)

theorem act_net_frame (ts : List Wire) (d : Distinct ts) (i x : Wire) (e : ts[i.1]? = some x) :
    act (R.net * frame ts) i = R.π x := by
  rw [act_mul, frame_act ts d i x e, R.net_π]

/-- Relabelling is conjugation by the network. -/
theorem relabel_ι : ∀ g : PG, 4 ⊢ ι (relabel R g) ≈ S R * ι g * Sinv R
  | .Xₚ t => by
    have e := ι_X (R.π t) (R.net * frame [t]) (act_net_frame R [t] (dX t) 0 t rfl)
    rw [← Fr_conj] at e
    exact e
  | .CXₚ c t ok => by
    have e := ι_CX (R.π c) (R.π t) (ok := ok_π R c t ok) (R.net * frame [t, c])
      (act_net_frame R [t, c] (dCX c t ok) 0 t rfl) (act_net_frame R [t, c] (dCX c t ok) 1 c rfl)
    rw [← Fr_conj] at e
    exact e
  | .CCXₚ a b t ok => by
    have e := ι_ccxBy (R.π a) (R.π b) (R.π t) (wlt (R.π a) (R.π b)) rfl (π_ab R ok) (π_at R ok)
      (π_bt R ok) (R.net * frame [t, a, b])
      (act_net_frame R [t, a, b] (dCCX a b t ok) 0 t rfl)
      (act_net_frame R [t, a, b] (dCCX a b t ok) 1 a rfl)
      (act_net_frame R [t, a, b] (dCCX a b t ok) 2 b rfl)
    rw [← Fr_conj] at e
    exact e

/-- … and so on words. -/
theorem relabel_ιs : ∀ u : List PG, 4 ⊢ ιs (u.map (relabel R)) ≈ S R * ιs u * Sinv R
  | [] => by
    show 4 ⊢ 1 ≈ S R * 1 * Sinv R
    rw [mul_one]; exact (S_Sinv R).symm
  | g :: u => ((relabel_ι R g).mul (relabel_ιs u)).trans (conj_mul (Sinv_S R) (ι g) (ιs u))

theorem relabel_eq {u v : List PG} (e : 4 ⊢ ιs u ≈ ιs v) :
    4 ⊢ ιs (u.map (relabel R)) ≈ ιs (v.map (relabel R)) :=
  (relabel_ιs R u).trans ((((Derivable.refl _).mul e).mul (Derivable.refl _)).trans
    (relabel_ιs R v).symm)

/-- Relabelling keeps the comparison of wires (the Agda's `==-π`). -/
theorem weq_π (a b : Wire) : weq (R.π a) (R.π b) = weq a b := by
  cases h : weq a b
  · cases h' : weq (R.π a) (R.π b)
    · rfl
    · exact absurd (R.π_inj (weq_sound h')) (fun e => by rw [e, weq_refl] at h; cases h)
  · rw [weq_sound h, weq_refl]

/-- Relabelling keeps a letter off the relabelled wire. -/
theorem avoids_relabel (m : Wire) : ∀ g : PG, avoids (R.π m) (relabel R g) = avoids m g
  | .Xₚ t => by simp only [relabel, avoids, weq_π]
  | .CXₚ c t _ => by simp only [relabel, avoids, weq_π]
  | .CCXₚ a b t ok => by
    rw [relabel, ccx, avoids_ccxBy]
    simp only [avoids, weq_π]

theorem every_avoids (m : Wire) : ∀ u : List PG, every (avoids m) u = true →
    every (avoids (R.π m)) (u.map (relabel R)) = true
  | [], _ => rfl
  | g :: u, h => by
    simp only [every, Bool.and_eq_true, List.map_cons] at h ⊢
    exact ⟨(avoids_relabel R m g).trans h.1, every_avoids m u h.2⟩

end Relabelling

/-! ### The relabelling sending the wires 0, 1, 2, 3 to `a, b, c, d` -/

def distinct4 (a b c d : Wire) : Bool :=
  okCX a b && (okCX a c && (okCX a d && (okCX b c && (okCX b d && okCX c d))))

theorem dist4 : ∀ (a b c d : Wire), distinct4 a b c d = true → Distinct [a, b, c, d] := by
  decide

def sel4 (a b c d : Wire) : Wire → Wire
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

def ρ4 (a b c d : Wire) (p : distinct4 a b c d = true := by decide) : Relabel where
  π := sel4 a b c d
  net := frame [a, b, c, d]
  net_π w := match w with
    | 0 => frame_act _ (dist4 a b c d p) 0 a rfl
    | 1 => frame_act _ (dist4 a b c d p) 1 b rfl
    | 2 => frame_act _ (dist4 a b c d p) 2 c rfl
    | 3 => frame_act _ (dist4 a b c d p) 3 d rfl

/-- Any permutation of the wires, given as an injective map. -/
def fromPerm (f : Wire → Wire) (inj : ∀ {a b}, f a = f b → a = b) : Relabel where
  π := f
  net := frame [f 0, f 1, f 2, f 3]
  net_π w :=
    have d : Distinct [f 0, f 1, f 2, f 3] :=
      List.Nodup.map (fun _ _ e => inj e) (by decide : ([0, 1, 2, 3] : List Wire).Nodup)
    match w with
    | 0 => frame_act _ d 0 (f 0) rfl
    | 1 => frame_act _ d 1 (f 1) rfl
    | 2 => frame_act _ d 2 (f 2) rfl
    | 3 => frame_act _ d 3 (f 3) rfl

/-- The transposition of wire `m` and wire 3. -/
def τ : Wire → Relabel
  | 0 => ρ4 3 1 2 0
  | 1 => ρ4 0 3 2 1
  | 2 => ρ4 0 1 3 2
  | 3 => ρ4 0 1 2 3

theorem τ_top : ∀ m : Wire, (τ m).π m = 3
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

/-! ## Letters on disjoint wires commute -/

theorem distinct_append (xs ys : List Wire) (dx : Distinct xs) (dy : Distinct ys)
    (h : apart xs ys = true) : Distinct (xs ++ ys) := by
  refine List.nodup_append.2 ⟨dx, dy, ?_⟩
  intro x hx y hy
  have := (every_iff _ ys).1 ((every_iff _ xs).1 h x hx) y hy
  exact neq this

/-- `g` placed by `F`, and `h` by `F` followed by `Fk`, which takes `h`'s gate
to `bh'` above `g`'s: so they commute when `bg` and `bh'` do. -/
theorem comm_via (g h : PG) (bg bh bh' : Circ 4) (F Fk : CW 4) (eg : 4 ⊢ ι g ≈ Fr sw bg F)
    (eh : 4 ⊢ ι h ≈ Fr sw bh (F * Fk)) (eb : 4 ⊢ bh' ≈ Fr sw bh Fk)
    (c : 4 ⊢ bg * bh' ≈ bh' * bg) : 4 ⊢ ι g * ι h ≈ ι h * ι g := by
  have il : 4 ⊢ Pc sw 0 (inv F) * Pc sw 0 F ≈ 1 := Pc_inv' cox 0 le_rfl F
  have eh' : 4 ⊢ ι h ≈ Fr sw bh' F := by
    rw [← Fr_conj] at eh
    exact eh.trans (((Derivable.refl _).mul eb.symm).mul (Derivable.refl _))
  exact (eg.mul eh').trans ((conj_mul il bg bh').trans
    ((((Derivable.refl _).mul c).mul (Derivable.refl _)).trans
      ((conj_mul il bh' bg).symm.trans (eh'.symm.mul eg.symm))))

theorem disj_comm : ∀ g h : PG, disjoint g h = true → 4 ⊢ ι g * ι h ≈ ι h * ι g
  | .Xₚ t, .Xₚ s, e => by
    have d := distinct_append [t] [s] (dX t) (dX s) e
    exact comm_via (.Xₚ t) (.Xₚ s) X X (shift X) (frame [t, s]) Fc
      (ι_X t _ (frame_act [t, s] d 0 t rfl))
      (ι_X s _ (by rw [act_mul]; exact frame_act [t, s] d 1 s rfl))
      X_up₁ (comm_gate₁_w (PGate.gate Gate.X_gate) X).symm
  | .Xₚ t, .CXₚ c s ok, e => by
    have d := distinct_append [t] [s, c] (dX t) (dCX c s ok) e
    exact comm_via (.Xₚ t) (.CXₚ c s ok) X CX (shift CX) (frame [t, s, c]) Fc
      (ι_X t _ (frame_act [t, s, c] d 0 t rfl))
      (ι_CX c s _ (by rw [act_mul]; exact frame_act [t, s, c] d 1 s rfl)
        (by rw [act_mul]; exact frame_act [t, s, c] d 2 c rfl))
      CX_up₁ (comm_gate₁_w (PGate.gate Gate.X_gate) CX).symm
  | .CXₚ c t ok, .Xₚ s, e => by
    have d := distinct_append [t, c] [s] (dCX c t ok) (dX s) e
    exact comm_via (.CXₚ c t ok) (.Xₚ s) CX X (shift (shift X)) (frame [t, c, s]) (Fc * Fc)
      (ι_CX c t _ (frame_act [t, c, s] d 0 t rfl) (frame_act [t, c, s] d 1 c rfl))
      (ι_X s _ (by rw [act_mul]; exact frame_act [t, c, s] d 2 s rfl))
      X_up₂ (comm_gate₂_w (PGate.gate Gate.CX_gate) X).symm
  | .Xₚ t, .CCXₚ a b s ok, e => by
    have d := distinct_append [t] [s, a, b] (dX t) (dCCX a b s ok) e
    exact comm_via (.Xₚ t) (.CCXₚ a b s ok) X CCX (shift CCX) (frame [t, s, a, b]) Fc
      (ι_X t _ (frame_act [t, s, a, b] d 0 t rfl))
      (ι_CCX a b s _ (by rw [act_mul]; exact frame_act [t, s, a, b] d 1 s rfl)
        (by rw [act_mul]; exact frame_act [t, s, a, b] d 2 a rfl)
        (by rw [act_mul]; exact frame_act [t, s, a, b] d 3 b rfl))
      CCX_up₁ (comm_gate₁_w (PGate.gate Gate.X_gate) CCX).symm
  | .CCXₚ a b t ok, .Xₚ s, e => by
    have d := distinct_append [t, a, b] [s] (dCCX a b t ok) (dX s) e
    exact comm_via (.CCXₚ a b t ok) (.Xₚ s) CCX X (shift (shift (shift X))) (frame [t, a, b, s])
      (Fc * (Fc * Fc))
      (ι_CCX a b t _ (frame_act [t, a, b, s] d 0 t rfl) (frame_act [t, a, b, s] d 1 a rfl)
        (frame_act [t, a, b, s] d 2 b rfl))
      (ι_X s _ (by rw [act_mul]; exact frame_act [t, a, b, s] d 3 s rfl))
      X_up₃ (comm_gate₃_w (PGate.gate Gate.CCX_gate) X).symm
  | .CXₚ c t ok, .CXₚ c' s ok', e => by
    have d := distinct_append [t, c] [s, c'] (dCX c t ok) (dCX c' s ok') e
    exact comm_via (.CXₚ c t ok) (.CXₚ c' s ok') CX CX (shift (shift CX)) (frame [t, c, s, c'])
      (Fc * Fc)
      (ι_CX c t _ (frame_act [t, c, s, c'] d 0 t rfl) (frame_act [t, c, s, c'] d 1 c rfl))
      (ι_CX c' s _ (by rw [act_mul]; exact frame_act [t, c, s, c'] d 2 s rfl)
        (by rw [act_mul]; exact frame_act [t, c, s, c'] d 3 c' rfl))
      CX_up₂ (comm_gate₂_w (PGate.gate Gate.CX_gate) CX).symm
  | .CXₚ _ _ _, .CCXₚ _ _ _ _, e => nomatch e
  | .CCXₚ _ _ _ _, .CXₚ _ _ _, e => nomatch e
  | .CCXₚ _ _ _ _, .CCXₚ _ _ _ _, e => nomatch e

/-! ## Rule (7) -/

/-- In our numbering, diagram order: `CCX_{3,2→1} CX_{1→0} CCX_{3,2→1} =
CCX_{3,2→0} CX_{1→0}`. -/
def lhs₇ : List PG := [.CCXₚ 2 3 1, .CXₚ 1 0, .CCXₚ 2 3 1]

def rhs₇ : List PG := [.CCXₚ 2 3 0, .CXₚ 1 0]

theorem rule7₀ : 4 ⊢ ιs lhs₇ ≈ ιs rhs₇ := by
  have a : 4 ⊢ ιs lhs₇ ≈ shift CCX * (CX * (shift CCX * 1)) :=
    ιCCX₂₃₁.mul (ιCX₁₀.mul (ιCCX₂₃₁.mul (Derivable.refl _)))
  have b : 4 ⊢ ιs rhs₇ ≈ CCX₃₂₀ * (CX * 1) := ιCCX₂₃₀.mul (ιCX₁₀.mul (Derivable.refl _))
  have r : 4 ⊢ shift CCX * CX * shift CCX ≈ CCX₃₂₀ * CX := srel_rule SRel.r7
  simp only [mul_one] at a b
  rw [← mul_assoc] at a
  exact a.trans (r.trans b.symm)

/-- Rule (7) placed on any wires. -/
theorem rule7 (R : Relabel) : 4 ⊢ ιs (lhs₇.map (relabel R)) ≈ ιs (rhs₇.map (relabel R)) :=
  relabel_eq R rule7₀

/-! ## Three-wire steps -/

/-- Completeness on three wires. -/
def Complete₃ : Prop := ∀ {c c' : Circ 3}, sem c ≐ sem c' → 3 ⊢ c ≈ c'

/-! ### A circuit that leaves the top wire alone is a narrower one widened -/

def low₂ : Gn 2 → Bool
  | .gate1 _ => true
  | _ => false

def cut₂ : Gn 2 → Gn 1
  | .gate1 h => .gate1 h
  | _ => .gate1 (.gate .X_gate)

theorem low₂_ok : ∀ g : Gn 2, low₂ g = true → g = Gen.pad 1 (cut₂ g)
  | .gate0 (.gate g), _ => nomatch g
  | .gate1 _, _ => rfl
  | .gate2 _, h => nomatch h
  | .up _, h => nomatch h

def low₃ : Gn 3 → Bool
  | .gate1 _ => true
  | .gate2 _ => true
  | .up g => low₂ g
  | _ => false

def cut₃ : Gn 3 → Gn 2
  | .gate1 h => .gate1 h
  | .gate2 h => .gate2 h
  | .up g => (cut₂ g).up
  | _ => .gate1 (.gate .X_gate)

theorem low₃_ok : ∀ g : Gn 3, low₃ g = true → g = Gen.pad 1 (cut₃ g)
  | .gate0 (.gate g), _ => nomatch g
  | .gate1 _, _ => rfl
  | .gate2 _, _ => rfl
  | .gate3 _, h => nomatch h
  | .up g, h => congrArg Gen.up (low₂_ok g h)

def low₄ : Gn 4 → Bool
  | .up g => low₃ g
  | _ => true

def cut₄ : Gn 4 → Gn 3
  | .gate1 h => .gate1 h
  | .gate2 h => .gate2 h
  | .gate3 h => .gate3 h
  | .up g => (cut₃ g).up
  | _ => .gate1 (.gate .X_gate)

theorem low₄_ok : ∀ g : Gn 4, low₄ g = true → g = Gen.pad 1 (cut₄ g)
  | .gate0 (.gate g), _ => nomatch g
  | .gate1 _, _ => rfl
  | .gate2 _, _ => rfl
  | .gate3 _, _ => rfl
  | .up g, h => congrArg Gen.up (low₃_ok g h)

/-- The letters of a circuit leave its top wire alone. -/
def lowW (w : Circ 4) : Bool := (FreeMonoid.toList w).all low₄

/-- The circuit on the lower three wires. -/
def cutW (w : Circ 4) : Circ 3 := FreeMonoid.map cut₄ w

theorem lowW_ok (w : Circ 4) (h : lowW w = true) : w = Circuit.pad 1 (cutW w) := by
  apply FreeMonoid.toList.injective
  show FreeMonoid.toList w =
    FreeMonoid.toList (FreeMonoid.map (Gen.pad 1) (FreeMonoid.map cut₄ w))
  rw [FreeMonoid.toList_map, FreeMonoid.toList_map, List.map_map]
  unfold lowW at h
  generalize FreeMonoid.toList w = l at h ⊢
  induction l with
  | nil => rfl
  | cons g l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, ← ih h.2, Function.comp_apply, ← low₄_ok g h.1]

private theorem low_check : forallPG (fun g => !avoids 3 g || lowW (ι g)) = true := by
  decide +kernel

/-- A letter off wire 3 is placed on the bottom three wires ... -/
theorem low_ι (g : PG) (h : avoids 3 g = true) : lowW (ι g) = true := by
  have := forallPG_sound _ low_check g
  rw [h] at this
  simpa using this

theorem lowW_mul (u v : Circ 4) : lowW (u * v) = (lowW u && lowW v) := by
  simp only [lowW, FreeMonoid.toList_mul, List.all_append]

/-- ... and so is a word of them. -/
theorem low_ιs : ∀ u : List PG, every (avoids 3) u = true → lowW (ιs u) = true
  | [], _ => rfl
  | g :: u, h => by
    simp only [every, Bool.and_eq_true] at h
    simp only [ιs, lowW_mul, low_ι g h.1, low_ιs u h.2, Bool.and_self]

/-! ### A widened circuit computes on the bottom wires -/

/-- A state with a bit on a new top wire (the Agda's `x V.++ (b V.∷ V.[])`). -/
def snoc : {n : ℕ} → Bits n → Bool → Bits (1 + n)
  | _, .nil, b => b ∷ .nil
  | _, a ∷ x, b => a ∷ snoc x b

theorem snoc_inj : ∀ {n : ℕ} (x y : Bits n) (b c : Bool), snoc x b = snoc y c → x = y
  | _, .nil, .nil, _, _, _ => rfl
  | _, a ∷ x, a' ∷ y, b, c, h => by
    simp only [snoc, Bits.cons.injEq] at h
    rw [h.1, snoc_inj x y b c h.2]

theorem gen_down : ∀ {n : ℕ} (g : Gn n) (x : Bits n) (b : Bool),
    semG (Gen.pad 1 g) (snoc x b) = snoc (semG g x) b
  | _, .gate0 (.gate g), _, _ => nomatch g
  | _, .gate1 (.gate .X_gate), _ ∷ _, _ => rfl
  | _, .gate2 (.gate .CX_gate), _ ∷ _ ∷ _, _ => rfl
  | _, .gate2 .swap, _ ∷ _ ∷ _, _ => rfl
  | _, .gate3 (.gate .CCX_gate), _ ∷ _ ∷ _ ∷ _, _ => rfl
  | _, .up g, a ∷ x, b => congrArg (a ∷ ·) (gen_down g x b)

theorem word_down {n : ℕ} (w : Circ n) (x : Bits n) (b : Bool) :
    sem (Circuit.pad 1 w) (snoc x b) = snoc (sem w x) b := by
  show semL (FreeMonoid.toList (FreeMonoid.map (Gen.pad 1) w)) (snoc x b) = _
  rw [FreeMonoid.toList_map]
  show _ = snoc (semL (FreeMonoid.toList w) x) b
  generalize FreeMonoid.toList w = l
  induction l generalizing x with
  | nil => rfl
  | cons g l ih =>
    show semL (l.map (Gen.pad 1)) (semG (Gen.pad 1 g) (snoc x b)) = _
    rw [gen_down, ih]
    rfl

section Narrow

variable (complete₃ : Complete₃)
include complete₃

/-- Two words on the bottom three wires with the same function are equal:
completeness on three wires, padded. -/
theorem narrow_low (u v : List PG) (hu : every (avoids 3) u = true)
    (hv : every (avoids 3) v = true) (e : sem (ιs u) ≐ sem (ιs v)) : 4 ⊢ ιs u ≈ ιs v := by
  have eu := lowW_ok (ιs u) (low_ιs u hu)
  have ev := lowW_ok (ιs v) (low_ιs v hv)
  have sem₃ : sem (cutW (ιs u)) ≐ sem (cutW (ιs v)) := fun x => by
    apply snoc_inj _ _ false false
    rw [← word_down, ← word_down, ← eu, ← ev]
    exact e _
  have d : 4 ⊢ Circuit.pad 1 (cutW (ιs u)) ≈ Circuit.pad 1 (cutW (ιs v)) :=
    pad₃ (complete₃ sem₃) 1
  rw [← eu, ← ev] at d
  exact d

/-- Two words on the three wires other than `m` with the same function are
equal. -/
theorem narrow (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (e : sem (ιs u) ≐ sem (ιs v)) : 4 ⊢ ιs u ≈ ιs v := by
  have hu' : every (avoids 3) (u.map (relabel (τ m))) = true := by
    have := every_avoids (τ m) m u hu
    rwa [τ_top] at this
  have hv' : every (avoids 3) (v.map (relabel (τ m))) = true := by
    have := every_avoids (τ m) m v hv
    rwa [τ_top] at this
  have eu := relabel_ιs (τ m) u
  have ev := relabel_ιs (τ m) v
  have mid : sem (S (τ m) * ιs u * Sinv (τ m)) ≐ sem (S (τ m) * ιs v * Sinv (τ m)) := fun x => by
    simp only [sem_mul]
    rw [e (sem (S (τ m)) x)]
  have sem' : sem (ιs (u.map (relabel (τ m)))) ≐ sem (ιs (v.map (relabel (τ m)))) :=
    feq_trans (sound eu) (feq_trans mid (feq_sym (sound ev)))
  exact unconj (Sinv_S (τ m))
    (eu.symm.trans ((narrow_low complete₃ _ _ hu' hv' sem').trans ev))

/-- The same, from the functions of the letters (the Agda's `narrowᵖ`). -/
theorem narrowP (m : Wire) (u v : List PG) (hu : every (avoids m) u = true)
    (hv : every (avoids m) v = true) (e : semPs u ≐ semPs v) : 4 ⊢ ιs u ≈ ιs v :=
  narrow complete₃ m u v hu hv (feq_trans (ιs_sem u) (feq_trans e (feq_sym (ιs_sem v))))

end Narrow

end QCert.XCXCCX4bit.Placed
