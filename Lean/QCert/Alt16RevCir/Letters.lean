/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Letter lists written as strings, for the generated derivations

Translation of `Letters.agda`.  The four-wire derivations are long lists of
steps on long lists of letters.  A letter list is written as a string,
`ℓ "suT…"`, one character per letter:

    a b d f     X on the wires 0, 1, 2, 3
    c e g       CX with target 0, 1, 2 and the control one wire up
    s t u       Ex on the wires 0 1, 1 2, 2 3
    T U         CCX with target 0, 1 and the controls above it

`ℓ₃` reads the letters of three wires (`a b d`, `c e`, `s t`, `T`) and `ℓʰ`
the NOT gates and swaps of `Frames`.  The steps of a derivation are written
with an index and strings, without parentheses: `bo` and `tp` (a step on the
bottom or the top three wires; the Agda's `to`, a keyword of Mathlib's
`lift … to …`), `hs` (two words in the NOT gates and swaps), `fr` (a change
of frame), `rw` and `rwˢ` (an equation, forwards or backwards).

**Deviations from the Agda.**

* *Strings.*  The Agda decodes a string by evaluation (`toList`, then a
  table).  Here `ℓ "…"`, `ℓ₃ "…"`, `ℓʰ "…"` are term elaborators that read
  the string literal and produce the list of names (`L4`, `L3`, `HL`), and
  `bo`, `tp`, `hs`, `fr`, `rw`, `rwˢ`, `deriveℓ` are notations taking the
  string literals; a character that is no letter is an error (the Agda's
  decoder skips it; the generator writes none).
* *Evidence.*  In the Agda a step whose evidence evaluation decides takes
  it as a hidden argument of type `T …`, which is solved by eta once
  evaluated.  Here such a step is a constructor of `Step4`, and its
  evidence is evaluated by the run itself (`Step4.sides`): a lemma is then
  one Boolean, `check4`, decided by the kernel once (`deriveℓ … (by decide
  +kernel)`), where a hidden proof for each step would be a kernel check of
  its own, eleven thousand of them.
-/
import QCert.Alt16RevCir.Frames
import Lean.Elab.Term

namespace QCert.Alt16RevCir.Letters

open QCert QCert.Circuit CircuitProp Engine FourWire Frames

/-- Equations between four-wire letter lists (the Agda's `Eqn 4`). -/
abbrev Eqn4 : Type := Eqn TRel L4

/-! ## Decoding -/

/-- The letters on four wires. -/
def l4 : Char → Option Lean.Name
  | 'a' => some ``L4.x0
  | 'b' => some ``L4.x1
  | 'd' => some ``L4.x2
  | 'f' => some ``L4.x3
  | 'c' => some ``L4.cx0
  | 'e' => some ``L4.cx1
  | 'g' => some ``L4.cx2
  | 's' => some ``L4.ex0
  | 't' => some ``L4.ex1
  | 'u' => some ``L4.ex2
  | 'T' => some ``L4.ccx0
  | 'U' => some ``L4.ccx1
  | _ => none

/-- The letters on three wires. -/
def l3 : Char → Option Lean.Name
  | 'a' => some ``L3.x0
  | 'b' => some ``L3.x1
  | 'd' => some ``L3.x2
  | 'c' => some ``L3.cx0
  | 'e' => some ``L3.cx1
  | 's' => some ``L3.ex0
  | 't' => some ``L3.ex1
  | 'T' => some ``L3.ccx
  | _ => none

/-- The NOT gates and the swaps. -/
def lh : Char → Option Lean.Name
  | 'a' => some ``HL.hx0
  | 'b' => some ``HL.hx1
  | 'd' => some ``HL.hx2
  | 'f' => some ``HL.hx3
  | 's' => some ``HL.he0
  | 't' => some ``HL.he1
  | 'u' => some ``HL.he2
  | _ => none

open Lean Elab Term in
/-- The list of the names of the letters of a string, over the alphabet
`ty`. -/
def decode (ty : Name) (f : Char → Option Name) (s : String) : TermElabM Expr := do
  let mut e := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ty)
  for c in s.toList.reverse do
    match f c with
    | some n => e := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ty) (mkConst n) e
    | none => throwError "not a letter: {c}"
  return e

/-- A list of four-wire letters, as a string. -/
scoped elab "ℓ " s:str : term => decode ``L4 l4 s.getString

/-- A list of three-wire letters, as a string. -/
scoped elab "ℓ₃ " s:str : term => decode ``L3 l3 s.getString

/-- A word in the NOT gates and swaps, as a string. -/
scoped elab "ℓʰ " s:str : term => decode ``HL lh s.getString

/-! ## Steps -/

/-- A step of a four-wire derivation, at a position. -/
inductive Step4 where
  /-- An equation. -/
  | rw (i : ℕ) (e : Eqn4)
  /-- An equation backwards (the Agda's `rwˢ`). -/
  | rws (i : ℕ) (e : Eqn4)
  /-- A step on the bottom three wires. -/
  | bo (i : ℕ) (l r : List L3)
  /-- A step on the top three wires (the Agda's `to`). -/
  | tp (i : ℕ) (l r : List L3)
  /-- Two words in the NOT gates and swaps. -/
  | hs (i : ℕ) (u v : List HL)
  /-- A change of frame. -/
  | fr (i : ℕ) (p p' : List HL) (b b' : List L3)

/-- The position of a step and the two sides of its equation, when its
evidence holds. -/
def Step4.sides : Step4 → Option (ℕ × List L4 × List L4)
  | .rw i e => some (i, e.lhs, e.rhs)
  | .rws i e => some (i, e.rhs, e.lhs)
  | .bo i l r => bif same3 l r then some (i, l.map dn34, r.map dn34) else none
  | .tp i l r => bif same3 l r then some (i, l.map up34, r.map up34) else none
  | .hs i u v => bif okSt (hnorm₀ u) (hnorm₀ v) then some (i, hl u, hl v) else none
  | .fr i p p' b b' =>
    bif frame_ok p p' b b' then
      some (i, hl p ++ (dn b ++ hl p.reverse), hl p' ++ (dn b' ++ hl p'.reverse))
    else none

theorem Step4.sides_sound : ∀ (s : Step4) {i : ℕ} {l r : List L4},
    s.sides = some (i, l, r) → 4 ⊢ᵀ word l ≈ word r
  | .rw _ e, _, _, _, h => by
    simp only [Step4.sides, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact e.prf
  | .rws _ e, _, _, _, h => by
    simp only [Step4.sides, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact e.prf.symm
  | .bo _ l r, _, _, _, h => by
    simp only [Step4.sides] at h
    cases hc : same3 l r
    · simp [hc] at h
    · simp only [hc, cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact (bot l r hc).prf
  | .tp _ l r, _, _, _, h => by
    simp only [Step4.sides] at h
    cases hc : same3 l r
    · simp [hc] at h
    · simp only [hc, cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact (top l r hc).prf
  | .hs _ u v, _, _, _, h => by
    simp only [Step4.sides] at h
    cases hc : okSt (hnorm₀ u) (hnorm₀ v)
    · simp [hc] at h
    · simp only [hc, cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact (hstep u v hc).prf
  | .fr _ p p' b b', _, _, _, h => by
    simp only [Step4.sides] at h
    cases hc : frame_ok p p' b b'
    · simp [hc] at h
    · simp only [hc, cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact (frame p p' b b' hc).prf

/-- Run the steps. -/
def run4 : List Step4 → List L4 → Option (List L4)
  | [], xs => some xs
  | s :: ss, xs =>
    match s.sides with
    | some (i, l, r) =>
      match rwAt l r i [] xs with
      | some ys => run4 ss ys
      | none => none
    | none => none

/-- The steps turn `l` into `r`. -/
def check4 (ss : List Step4) (l r : List L4) : Bool :=
  match run4 ss l with
  | some y => eqLA y r
  | none => false

theorem run4_sound : ∀ (ss : List Step4) (xs ys : List L4), run4 ss xs = some ys →
    4 ⊢ᵀ word xs ≈ word ys
  | [], xs, ys, h => by
    simp only [run4, Option.some.injEq] at h
    subst h; exact Derivable.refl _
  | s :: ss, xs, ys, h => by
    simp only [run4] at h
    cases hs : s.sides with
    | none => simp [hs] at h
    | some t =>
      obtain ⟨i, l, r⟩ := t
      simp only [hs] at h
      cases hr : rwAt l r i [] xs with
      | none => simp [hr] at h
      | some zs =>
        simp only [hr] at h
        exact (rwAt_sound (s.sides_sound hs) i [] xs zs hr).trans (run4_sound ss zs ys h)

theorem check4_sound {ss : List Step4} {l r : List L4} (h : check4 ss l r = true) :
    4 ⊢ᵀ word l ≈ word r := by
  unfold check4 at h
  cases hr : run4 ss l with
  | none => simp [hr] at h
  | some y =>
    simp only [hr] at h
    rw [← eqLA_sound _ _ h]; exact run4_sound ss l y hr

/-- A derivation between two letter lists (the Agda's `deriveℓ`, its strings
decoded). -/
def deriveL (l r : List L4) (ss : List Step4) (h : check4 ss l r = true) : Eqn4 :=
  ⟨l, r, check4_sound h⟩

/-! ## The steps, written with strings -/

/-- An equation at a position. -/
scoped syntax:max "rw " num ppSpace term:max : term

/-- An equation backwards. -/
scoped syntax:max "rwˢ " num ppSpace term:max : term

/-- A step on the bottom three wires. -/
scoped syntax:max "bo " num ppSpace str ppSpace str : term

/-- A step on the top three wires. -/
scoped syntax:max "tp " num ppSpace str ppSpace str : term

/-- Two words in the NOT gates and swaps. -/
scoped syntax:max "hs " num ppSpace str ppSpace str : term

/-- A change of frame. -/
scoped syntax:max "fr " num ppSpace str ppSpace str ppSpace str ppSpace str : term

/-- A derivation between two strings. -/
scoped syntax:lead "deriveℓ " str ppSpace str ppSpace term:max ppSpace term:max : term

macro_rules
  | `(rw $i:num $e) => `(Step4.rw $i $e)
  | `(rwˢ $i:num $e) => `(Step4.rws $i $e)
  | `(bo $i:num $l:str $r:str) => `(Step4.bo $i (ℓ₃ $l) (ℓ₃ $r))
  | `(tp $i:num $l:str $r:str) => `(Step4.tp $i (ℓ₃ $l) (ℓ₃ $r))
  | `(hs $i:num $u:str $v:str) => `(Step4.hs $i (ℓʰ $u) (ℓʰ $v))
  | `(fr $i:num $p:str $q:str $b:str $c:str) => `(Step4.fr $i (ℓʰ $p) (ℓʰ $q) (ℓ₃ $b) (ℓ₃ $c))
  | `(deriveℓ $l:str $r:str $ss $h) => `(deriveL (ℓ $l) (ℓ $r) $ss $h)

end QCert.Alt16RevCir.Letters
