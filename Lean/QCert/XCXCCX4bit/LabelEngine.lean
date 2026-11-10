/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Certificates over words of labels

Translation of `LabelEngine.agda`.  Labels stand for involutions of a group
(here perfect matchings of eight states), interpreted as words `X x` of some
theory.  Given that each `X x` is an involution (`inv`), that `X x`
conjugates `X y` to the label of `x y x` (`conj`, under a decided side
condition `cok`), and that two labels whose product is a label (side
condition `kok`, decided) multiply to it (`klein`), a word of labels can be
rewritten by moves whose side conditions are decided on the labels alone:

    H i     x y   ↦  (x y x) x          Hi i    x y   ↦  y (y x y)
    C i     x x   ↦  ε                  I i z   ε     ↦  z z
    K i     x y   ↦  (x y)              Ki i x y  z   ↦  x y  (x y = z)

`run` checks a certificate (a list of moves) as a Boolean computation, and
`check_sound` turns a successful check into a derivation between the
interpretations of the two words.

The Agda module's parameters (`_≟ᴸ_ c3 cok mul kok`) are explicit arguments
here, in that order (`eqLab` for `_≟ᴸ_`); those of its module `Sound`
(`Γ X ≟ᴸ-sound inv conj klein`) likewise.  Since `local` and `at` are Lean
keywords, the Agda's `local` and `at` are `localStep` and `atPos`.  The
interpretation's equations are stated with Lean's left-associated `*`:
`conj : X x * X y * X x ≈ X (c3 x y)` (the Agda's `X x • X y • X x`, bracketed
to the right).  The checks use `bif` and pattern matching, for the kernel.
-/
import QCert.Presentation

namespace QCert.XCXCCX4bit.LabelEngine

variable {L : Type*}

/-! ## Moves and their runs -/

/-- A move, at a position. -/
inductive Move (L : Type*) where
  | H : ℕ → Move L
  | Hi : ℕ → Move L
  | C : ℕ → Move L
  | I : ℕ → L → Move L
  | K : ℕ → Move L
  | Ki : ℕ → L → L → Move L

section Run

variable (eqLab : L → L → Bool) (c3 : L → L → L) (cok : L → L → Bool) (mul : L → L → L)
  (kok : L → L → Bool)

/-- A move applied at the head of a word (the Agda's `local`). -/
def localStep : Move L → List L → Option (List L)
  | .H _, x :: y :: r => bif cok x y then some (c3 x y :: x :: r) else none
  | .Hi _, x :: y :: r => bif cok y x then some (y :: c3 y x :: r) else none
  | .C _, x :: y :: r => bif eqLab x y then some r else none
  | .I _ z, r => some (z :: z :: r)
  | .K _, x :: y :: r => bif kok x y then some (mul x y :: r) else none
  | .Ki _ x y, z :: r => bif kok x y && eqLab (mul x y) z then some (x :: y :: r) else none
  | _, _ => none

/-- The position of a move. -/
def index : Move L → ℕ
  | .H i => i
  | .Hi i => i
  | .C i => i
  | .I i _ => i
  | .K i => i
  | .Ki i _ _ => i

/-- Apply a move at position `i` (the Agda's `at`). -/
def atPos : ℕ → Move L → List L → Option (List L)
  | 0, m, xs => localStep eqLab c3 cok mul kok m xs
  | _ + 1, _, [] => none
  | i + 1, m, x :: xs =>
    match atPos i m xs with
    | some ys => some (x :: ys)
    | none => none

/-- Apply a move at its position. -/
def step (m : Move L) (xs : List L) : Option (List L) :=
  atPos eqLab c3 cok mul kok (index m) m xs

/-- Equality of words of labels. -/
def eqL : List L → List L → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqLab x y && eqL xs ys
  | _, _ => false

/-- Run a list of moves. -/
def run : List (Move L) → List L → Option (List L)
  | [], xs => some xs
  | m :: ms, xs =>
    match step eqLab c3 cok mul kok m xs with
    | some ys => run ms ys
    | none => none

/-- A certificate: the run from `l` ends in `r`. -/
def check (ms : List (Move L)) (l r : List L) : Bool :=
  match run eqLab c3 cok mul kok ms l with
  | some r' => eqL eqLab r' r
  | none => false

end Run

/-! ## Soundness, for an interpretation satisfying the relations -/

section Sound

variable {eqLab : L → L → Bool} {c3 : L → L → L} {cok : L → L → Bool} {mul : L → L → L}
  {kok : L → L → Bool}
variable {A : Type*} (Γ : WRel A) (X : L → Word A)

/-- A word of labels as a word. -/
def Xs : List L → Word A
  | [] => 1
  | x :: xs => X x * Xs xs

theorem Xs_append (xs ys : List L) : Xs X (xs ++ ys) = Xs X xs * Xs X ys := by
  induction xs with
  | nil => exact (one_mul _).symm
  | cons x xs ih => rw [List.cons_append, Xs, Xs, ih, mul_assoc]

/-- The Agda's `Xs-++`, as a derivation. -/
theorem Xs_append' (xs ys : List L) : Derivable Γ (Xs X (xs ++ ys)) (Xs X xs * Xs X ys) := by
  rw [Xs_append]

variable {Γ X}
variable (eq_sound : ∀ x y, eqLab x y = true → x = y)
  (inv : ∀ x, Derivable Γ (X x * X x) 1)
  (conj : ∀ x y, cok x y = true → Derivable Γ (X x * X y * X x) (X (c3 x y)))
  (klein : ∀ x y, kok x y = true → Derivable Γ (X x * X y) (X (mul x y)))

include eq_sound in
theorem eqL_sound : ∀ xs ys : List L, eqL eqLab xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [eq_sound x y h.1, eqL_sound xs ys h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

/-- The class of a word modulo `Γ`. -/
private abbrev cl (w : Word A) : (conGen Γ).Quotient := (conGen Γ).mk' w

private theorem cl_eq {w v : Word A} : cl (Γ := Γ) w = cl v ↔ Derivable Γ w v := (conGen Γ).eq

include inv conj in
/-- `X x X y = X (x y x) X x` (the Agda's `h-move`). -/
theorem h_move (x y : L) (c : cok x y = true) :
    Derivable Γ (X x * X y) (X (c3 x y) * X x) := by
  have e1 := cl_eq.2 (inv x)
  have e2 := cl_eq.2 (conj x y c)
  apply cl_eq.1
  simp only [cl, map_mul, map_one] at e1 e2 ⊢
  rw [← e2, mul_assoc, e1, mul_one]

include inv conj in
/-- `X x X y = X y X (y x y)` (the Agda's `hi-move`). -/
theorem hi_move (x y : L) (c : cok y x = true) :
    Derivable Γ (X x * X y) (X y * X (c3 y x)) := by
  have e1 := cl_eq.2 (inv y)
  have e2 := cl_eq.2 (conj y x c)
  apply cl_eq.1
  simp only [cl, map_mul, map_one] at e1 e2 ⊢
  rw [← e2, ← mul_assoc, ← mul_assoc, e1, one_mul]

private theorem bif_some {b : Bool} {r ys : List L}
    (e : (bif b then some r else none) = some ys) : b = true ∧ r = ys := by
  cases b <;> simp_all

include eq_sound inv conj klein in
theorem localStep_sound (m : Move L) (xs ys : List L)
    (e : localStep eqLab c3 cok mul kok m xs = some ys) : Derivable Γ (Xs X xs) (Xs X ys) := by
  match m, xs, e with
  | .H _, x :: y :: r, e =>
    obtain ⟨b, rfl⟩ := bif_some e
    simp only [Xs, ← mul_assoc]
    exact (h_move inv conj x y b).mul (Derivable.refl _)
  | .Hi _, x :: y :: r, e =>
    obtain ⟨b, rfl⟩ := bif_some e
    simp only [Xs, ← mul_assoc]
    exact (hi_move inv conj x y b).mul (Derivable.refl _)
  | .C _, x :: y :: r, e =>
    obtain ⟨b, rfl⟩ := bif_some e
    obtain rfl := eq_sound x y b
    simp only [Xs, ← mul_assoc]
    exact ((inv x).mul (Derivable.refl _)).trans (by rw [one_mul])
  | .I _ z, r, e =>
    cases e
    simp only [Xs, ← mul_assoc]
    exact (by rw [one_mul] : Derivable Γ (Xs X r) (1 * Xs X r)).trans
      ((inv z).symm.mul (Derivable.refl _))
  | .K _, x :: y :: r, e =>
    obtain ⟨b, rfl⟩ := bif_some e
    simp only [Xs, ← mul_assoc]
    exact (klein x y b).mul (Derivable.refl _)
  | .Ki _ x y, z :: r, e =>
    obtain ⟨b, rfl⟩ := bif_some e
    simp only [Bool.and_eq_true] at b
    obtain rfl := eq_sound _ _ b.2
    simp only [Xs, ← mul_assoc]
    exact (klein x y b.1).symm.mul (Derivable.refl _)
  | .H _, [], e => cases e
  | .H _, [_], e => cases e
  | .Hi _, [], e => cases e
  | .Hi _, [_], e => cases e
  | .C _, [], e => cases e
  | .C _, [_], e => cases e
  | .K _, [], e => cases e
  | .K _, [_], e => cases e
  | .Ki _ _ _, [], e => cases e

include eq_sound inv conj klein in
theorem atPos_sound : ∀ (i : ℕ) (m : Move L) (xs ys : List L),
    atPos eqLab c3 cok mul kok i m xs = some ys → Derivable Γ (Xs X xs) (Xs X ys)
  | 0, m, xs, ys, e => localStep_sound eq_sound inv conj klein m xs ys e
  | _ + 1, _, [], _, e => by cases e
  | i + 1, m, x :: xs, ys, e => by
    simp only [atPos] at e
    split at e
    · next zs h =>
      cases e
      exact (Derivable.refl (X x)).mul (atPos_sound i m xs zs h)
    · cases e

include eq_sound inv conj klein in
theorem run_sound : ∀ (ms : List (Move L)) (xs ys : List L),
    run eqLab c3 cok mul kok ms xs = some ys → Derivable Γ (Xs X xs) (Xs X ys)
  | [], xs, ys, e => by cases e; exact Derivable.refl _
  | m :: ms, xs, ys, e => by
    simp only [run] at e
    split at e
    · next zs h =>
      exact (atPos_sound eq_sound inv conj klein _ m xs zs h).trans (run_sound ms zs ys e)
    · cases e

include eq_sound inv conj klein in
/-- A checked certificate is a derivation (the Agda's `check-sound`). -/
theorem check_sound (ms : List (Move L)) (l r : List L)
    (h : check eqLab c3 cok mul kok ms l r = true) : Derivable Γ (Xs X l) (Xs X r) := by
  unfold check at h
  split at h
  · next r' e =>
    rw [← eqL_sound eq_sound r' r h]
    exact run_sound eq_sound inv conj klein ms l r' e
  · cases h

end Sound

end QCert.XCXCCX4bit.LabelEngine
