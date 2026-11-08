/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the engine

Translation of `Engine.agda`: a proof engine for equations between concrete
words over any alphabet with an injective code.

An equation (`Eqn`) is a pair of letter lists with a derivation.  A
derivation of a new equation is a list of steps `rw i e`, each rewriting the
occurrence of `lhs e` at position `i` to `rhs e`; `run` executes them and
`derive` turns a successful run into an equation, so that a proof is a list
of steps closed by one evaluation.  The Agda closes it by `refl`, the
type checker running the steps; here the run is one Boolean (`check`)
decided by the kernel (`decide +kernel`).

Given that every letter is an involution (section `Invol`), equations
transform by `rev` (reversing both sides) and `rot k m`, which reads `l = r`
as the relator `l r⁻¹ = ε`, rotates it by `k` letters and splits it after
`m`.  Lists are in operator order, like words.

Words are the framework's `FreeMonoid`, which is `List` itself: the Agda's
`⟪_⟫` and `flat`, between letter lists and its tree-shaped words, are the
identity here (`FreeMonoid.ofList`, `FreeMonoid.toList`).
-/
import QCert.ToffoliHadamardRS.Gates
import Mathlib.GroupTheory.Congruence.Defs

namespace QCert.ToffoliHadamardRS.Engine

variable {A : Type} {Γ : WRel A}

/-! ## The quotient monoid -/

/-- The class of a word modulo the congruence of `Γ`. -/
abbrev cls (Γ : WRel A) (w : Word A) : (conGen Γ).Quotient := (conGen Γ).mk' w

theorem cls_eq {w v : Word A} : cls Γ w = cls Γ v ↔ Derivable Γ w v := (conGen Γ).eq

theorem cls_mul (w v : Word A) : cls Γ (w * v) = cls Γ w * cls Γ v := map_mul _ w v

theorem cls_one : cls Γ 1 = 1 := map_one _

/-! ## Equations -/

/-- An equation between letter lists, with its derivation. -/
structure Eqn (Γ : WRel A) where
  lhs : List A
  rhs : List A
  prf : Derivable Γ (FreeMonoid.ofList lhs) (FreeMonoid.ofList rhs)

/-- Both sides exchanged (the Agda's `sym⁼`). -/
def Eqn.symm (e : Eqn Γ) : Eqn Γ := ⟨e.rhs, e.lhs, e.prf.symm⟩

/-- An equation between words, as letter lists (the Agda's `of⁼`). -/
def ofDer {w v : Word A} (p : Derivable Γ w v) : Eqn Γ := ⟨w.toList, v.toList, p⟩

/-- An axiom (the Agda's `ax⁼`). -/
def ax {w v : Word A} (h : Γ w v) : Eqn Γ := ofDer (Derivable.of h)

/-- Back to words: an equation between any two words with its letters (the
Agda's `to≈`). -/
theorem Eqn.toDer (e : Eqn Γ) {w v : Word A} (hw : w.toList = e.lhs) (hv : v.toList = e.rhs) :
    Derivable Γ w v := by
  have ew : w = FreeMonoid.ofList e.lhs := by rw [← hw]; rfl
  have ev : v = FreeMonoid.ofList e.rhs := by rw [← hv]; rfl
  rw [ew, ev]; exact e.prf

/-! ## When every letter is an involution -/

section Invol

variable (invol : ∀ x : A, Derivable Γ (FreeMonoid.of x * FreeMonoid.of x) 1)
include invol

theorem cls_sq (x : A) : cls Γ (FreeMonoid.of x) * cls Γ (FreeMonoid.of x) = 1 := by
  rw [← cls_mul, ← cls_one]; exact cls_eq.2 (invol x)

theorem rev_inv (xs : List A) :
    cls Γ (FreeMonoid.ofList xs.reverse) * cls Γ (FreeMonoid.ofList xs) = 1 := by
  induction xs with
  | nil => simp [cls_one]
  | cons x xs ih =>
    have e1 : cls Γ (FreeMonoid.ofList (x :: xs).reverse) =
        cls Γ (FreeMonoid.ofList xs.reverse) * cls Γ (FreeMonoid.of x) := by
      rw [List.reverse_cons, FreeMonoid.ofList_append, cls_mul]; rfl
    have e2 : cls Γ (FreeMonoid.ofList (x :: xs)) =
        cls Γ (FreeMonoid.of x) * cls Γ (FreeMonoid.ofList xs) := by
      rw [FreeMonoid.ofList_cons, cls_mul]
    rw [e1, e2]
    calc cls Γ (FreeMonoid.ofList xs.reverse) * cls Γ (FreeMonoid.of x) *
          (cls Γ (FreeMonoid.of x) * cls Γ (FreeMonoid.ofList xs))
        = cls Γ (FreeMonoid.ofList xs.reverse) *
          (cls Γ (FreeMonoid.of x) * cls Γ (FreeMonoid.of x)) * cls Γ (FreeMonoid.ofList xs) := by
          simp only [mul_assoc]
      _ = 1 := by rw [cls_sq invol, mul_one, ih]

theorem inv_rev (xs : List A) :
    cls Γ (FreeMonoid.ofList xs) * cls Γ (FreeMonoid.ofList xs.reverse) = 1 := by
  have := rev_inv invol xs.reverse
  rwa [List.reverse_reverse] at this

/-- If `u • v ≈ ε` then `u ≈ v⁻¹`, the reversal of `v`. -/
theorem inverse_of (xs ys : List A)
    (e : Derivable Γ (FreeMonoid.ofList xs * FreeMonoid.ofList ys) 1) :
    Derivable Γ (FreeMonoid.ofList xs) (FreeMonoid.ofList ys.reverse) := by
  have e' : cls Γ (FreeMonoid.ofList xs) * cls Γ (FreeMonoid.ofList ys) = 1 := by
    rw [← cls_mul, ← cls_one]; exact cls_eq.2 e
  apply cls_eq.1
  calc cls Γ (FreeMonoid.ofList xs)
      = cls Γ (FreeMonoid.ofList xs) * (cls Γ (FreeMonoid.ofList ys) *
          cls Γ (FreeMonoid.ofList ys.reverse)) := by rw [inv_rev invol, mul_one]
    _ = cls Γ (FreeMonoid.ofList ys.reverse) := by rw [← mul_assoc, e', one_mul]

theorem rotate_relator (xs ys : List A)
    (e : Derivable Γ (FreeMonoid.ofList xs * FreeMonoid.ofList ys) 1) :
    Derivable Γ (FreeMonoid.ofList ys * FreeMonoid.ofList xs) 1 := by
  have h := inverse_of invol xs ys e
  apply cls_eq.1
  rw [cls_mul, cls_eq.2 h, inv_rev invol, cls_one]

theorem rev_cong (xs ys : List A)
    (e : Derivable Γ (FreeMonoid.ofList xs) (FreeMonoid.ofList ys)) :
    Derivable Γ (FreeMonoid.ofList xs.reverse) (FreeMonoid.ofList ys.reverse) := by
  apply inverse_of invol
  apply cls_eq.1
  rw [cls_mul, ← cls_eq.2 e, rev_inv invol, cls_one]

/-- Both sides reversed (the Agda's `rev⁼`). -/
def rev (e : Eqn Γ) : Eqn Γ := ⟨e.lhs.reverse, e.rhs.reverse, rev_cong invol _ _ e.prf⟩

omit invol in
/-- The relator `l r⁻¹ = ε`. -/
def relator (e : Eqn Γ) : List A := e.lhs ++ e.rhs.reverse

omit invol in
/-- The relator rotated by `k`. -/
def rotated (k : ℕ) (e : Eqn Γ) : List A := (relator e).drop k ++ (relator e).take k

theorem relator_eps (e : Eqn Γ) : Derivable Γ (FreeMonoid.ofList (relator e)) 1 := by
  apply cls_eq.1
  rw [relator, FreeMonoid.ofList_append, cls_mul, cls_eq.2 e.prf, inv_rev invol, cls_one]

omit invol in
theorem split_eps (k : ℕ) (xs : List A) (e : Derivable Γ (FreeMonoid.ofList xs) 1) :
    Derivable Γ (FreeMonoid.ofList (xs.take k) * FreeMonoid.ofList (xs.drop k)) 1 := by
  rw [← FreeMonoid.ofList_append, List.take_append_drop]; exact e

theorem rotated_eps (k : ℕ) (e : Eqn Γ) : Derivable Γ (FreeMonoid.ofList (rotated k e)) 1 := by
  rw [rotated, FreeMonoid.ofList_append]
  exact rotate_relator invol _ _ (split_eps k _ (relator_eps invol e))

/-- The relator of `e` rotated by `k` and split after `m`: the rule
`u → v⁻¹` (the Agda's `rot⁼`). -/
def rot (k m : ℕ) (e : Eqn Γ) : Eqn Γ :=
  ⟨(rotated k e).take m, ((rotated k e).drop m).reverse,
    inverse_of invol _ _ (split_eps m _ (rotated_eps invol k e))⟩

end Invol

/-! ## Equality of letters and lists -/

variable [Coded A]

/-- Letters compared by their codes. -/
def eqA (x y : A) : Bool := Nat.beq (Coded.code x) (Coded.code y)

theorem eqA_sound {x y : A} (h : eqA x y = true) : x = y :=
  Coded.inj (Nat.eq_of_beq_eq_true h)

/-- Lists compared letter by letter. -/
def eqL : List A → List A → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqA x y && eqL xs ys
  | _, _ => false

theorem eqL_sound : ∀ {xs ys : List A}, eqL xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [eqA_sound h.1, eqL_sound h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

/-! ## Running a derivation -/

/-- A step: rewrite at position `pos` by the equation `eqn`. -/
structure Step (Γ : WRel A) where
  pos : ℕ
  eqn : Eqn Γ

/-- The step `rw i e`. -/
abbrev rw (i : ℕ) (e : Eqn Γ) : Step Γ := ⟨i, e⟩

/-- The occurrence of `lhs e` at position `i` replaced by `rhs e`. -/
def rewriteAt (i : ℕ) (e : Eqn Γ) (xs : List A) : List A :=
  xs.take i ++ (e.rhs ++ (xs.drop i).drop e.lhs.length)

/-- Whether `lhs e` occurs at position `i`. -/
def matchesAt (i : ℕ) (e : Eqn Γ) (xs : List A) : Bool :=
  eqL ((xs.drop i).take e.lhs.length) e.lhs

/-- Run the steps. -/
def run : List (Step Γ) → List A → Option (List A)
  | [], xs => some xs
  | s :: ss, xs => bif matchesAt s.pos s.eqn xs then run ss (rewriteAt s.pos s.eqn xs) else none

/-- The steps turn `l` into `r`. -/
def check (ss : List (Step Γ)) (l r : List A) : Bool :=
  match run ss l with
  | some y => eqL y r
  | none => false

theorem rw_sound (i : ℕ) (e : Eqn Γ) (xs : List A) (h : matchesAt i e xs = true) :
    Derivable Γ (FreeMonoid.ofList xs) (FreeMonoid.ofList (rewriteAt i e xs)) := by
  have hm : (xs.drop i).take e.lhs.length = e.lhs := eqL_sound h
  have hx : xs = xs.take i ++ (e.lhs ++ (xs.drop i).drop e.lhs.length) := by
    conv_lhs => rw [← List.take_append_drop i xs, ← List.take_append_drop e.lhs.length (xs.drop i)]
    rw [hm]
  rw [rewriteAt]
  conv_lhs => rw [hx]
  simp only [FreeMonoid.ofList_append]
  exact (Derivable.refl _).mul (e.prf.mul (Derivable.refl _))

theorem run_sound : ∀ (ss : List (Step Γ)) (xs ys : List A), run ss xs = some ys →
    Derivable Γ (FreeMonoid.ofList xs) (FreeMonoid.ofList ys)
  | [], xs, ys, h => by
    simp only [run, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | s :: ss, xs, ys, h => by
    simp only [run] at h
    cases hm : matchesAt s.pos s.eqn xs
    · rw [hm] at h; simp at h
    · rw [hm] at h
      exact (rw_sound s.pos s.eqn xs hm).trans (run_sound ss _ ys h)

theorem check_sound {ss : List (Step Γ)} {l r : List A} (h : check ss l r = true) :
    Derivable Γ (FreeMonoid.ofList l) (FreeMonoid.ofList r) := by
  unfold check at h
  split at h
  · rename_i y hy
    rw [← eqL_sound h]; exact run_sound ss l y hy
  · simp at h

/-- A derivation: an equation from the steps that turn `l` into `r`. -/
def derive (l r : List A) (ss : List (Step Γ)) (h : check ss l r = true) : Eqn Γ :=
  ⟨l, r, check_sound h⟩

end QCert.ToffoliHadamardRS.Engine
