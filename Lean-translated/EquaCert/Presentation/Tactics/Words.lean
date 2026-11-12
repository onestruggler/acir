/-
# Tactics on words: lists of generators, and canonical forms up to commutation

Translation of the parts of `Presentation/Tactics/Words.agda` that the
developments use: `Associative`'s `word-of-list`, `list-of-word` and
`lemma-list-of-word`, and `Commuting`'s canonical forms (`split`,
`unsplit`, `insert`, `comm-canonical`, `lemma-comm-canonical`).

Words being Mathlib's free monoid (lists), `word-of-list` is
`FreeMonoid.ofList` and `list-of-word` is `FreeMonoid.toList`; they are
mutually inverse on the nose, so the Agda's `lemma-list-of-word` and
`lemma-append` are equalities.

The canonical form of a word modulo commutation is the least equivalent
word in the reverse lexicographic order, computed by inserting the
letters one at a time from the right (see the Agda for the algorithm).

**Deviation.**  The Agda's `comm` returns `Maybe (commutes Γ x y)`, a
decision carrying its proof; here it is a Boolean `comm` with a soundness
hypothesis `comm_sound`, so that the canonical form is a plain function
that the kernel evaluates.
-/
import EquaCert.Presentation.Base

namespace EquaCert.Tactics

universe u

open EquaCert.Word

variable {X : Type u}

/-- `x` and `y` commute in the theory `Γ` (the Agda's `commutes Γ x y`). -/
def commutes (Γ : WRel X) (x y : X) : Prop :=
  Derivable Γ ([x]ʷ * [y]ʷ) ([y]ʷ * [x]ʷ)

namespace Associative

/-- The word of a list of generators (the Agda's `word-of-list`). -/
abbrev wordOfList (xs : List X) : Word X := FreeMonoid.ofList xs

/-- The list of generators of a word (the Agda's `list-of-word`). -/
abbrev listOfWord (w : Word X) : List X := FreeMonoid.toList w

/-- The Agda's `lemma-list-of-word`, an equality here. -/
theorem lemma_list_of_word (w : Word X) : wordOfList (listOfWord w) = w := rfl

/-- The Agda's `lemma-append`, an equality here. -/
theorem lemma_append (xs ys : List X) :
    wordOfList xs * wordOfList ys = wordOfList (xs ++ ys) := rfl

theorem wordOfList_cons (x : X) (xs : List X) :
    wordOfList (x :: xs) = [x]ʷ * wordOfList xs := rfl

end Associative

open Associative

/-! ## Canonical forms -/

section Commuting

variable (comm : X → X → Bool) (less : X → X → Bool)

/-- `List.reverseAux ys zs`, the reverse of `ys` followed by `zs` (the
Agda's `reverse-append`). -/
abbrev reverseAppend (ys zs : List X) : List X := List.reverseAux ys zs

/-- Given `ys`, `x` and `zs`, the pair `(reverse zs₁ ++ ys, zs₂)` where `zs₁`
is the longest prefix of `zs` whose letters commute with `x` (the Agda's
`split`). -/
def split : List X → X → List X → List X × List X
  | ys, _, [] => (ys, [])
  | ys, x, z :: zs =>
    match comm x z with
    | true => split (z :: ys) x zs
    | false => (ys, z :: zs)

/-- The lexicographically least way of inserting `x` into `ys`, reversed and
followed by `zs` (the Agda's `unsplit`). -/
def unsplit : List X → X → List X → List X
  | [], x, zs => x :: zs
  | y :: ys, x, zs =>
    match less x y with
    | true => unsplit ys x (y :: zs)
    | false => reverseAppend (y :: ys) (x :: zs)

/-- The canonical form of `x :: xs`, given that of `xs` (the Agda's
`insert`). -/
def insert (x : X) (xs : List X) : List X :=
  let p := split comm [] x xs
  unsplit less p.1 x p.2

/-- The canonical form of a list modulo commutation (the Agda's
`comm-canonical`). -/
def commCanonical : List X → List X
  | [] => []
  | x :: xs => insert comm less x (commCanonical xs)

variable {comm less} {Γ : WRel X}

/-- `split` only moves letters. -/
theorem lemma_split1 :
    ∀ (ys : List X) (x : X) (zs : List X),
      reverseAppend ys zs =
        reverseAppend (split comm ys x zs).1 (split comm ys x zs).2
  | _, _, [] => rfl
  | ys, x, z :: zs => by
    unfold split
    cases comm x z with
    | true => exact lemma_split1 (z :: ys) x zs
    | false => rfl

/-- The letters `split` moves commute with `x`. -/
theorem lemma_split2 (comm_sound : ∀ x y, comm x y = true → commutes Γ x y) :
    ∀ (ys : List X) (x : X) (zs : List X), (∀ y ∈ ys, commutes Γ x y) →
      ∀ y ∈ (split comm ys x zs).1, commutes Γ x y
  | _, _, [], ih => ih
  | ys, x, z :: zs, ih => by
    unfold split
    cases h : comm x z with
    | true =>
      refine lemma_split2 comm_sound (z :: ys) x zs ?_
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact comm_sound x y h
      · exact ih y hy
    | false => exact ih

/-- The Agda's `lemma-reverse-append`. -/
theorem lemma_reverse_append :
    ∀ (ys : List X) (x : X) (zs : List X), (∀ y ∈ ys, commutes Γ x y) →
      Derivable Γ (wordOfList (x :: reverseAppend ys zs))
        (wordOfList (reverseAppend ys (x :: zs)))
  | [], _, _, _ => Derivable.refl _
  | y :: ys, x, zs, hyp => by
    have ih := lemma_reverse_append ys x (y :: zs) (fun z hz => hyp z (List.mem_cons_of_mem _ hz))
    refine ih.trans ?_
    -- reverseAppend ys (x :: y :: zs) ≈ reverseAppend ys (y :: x :: zs)
    have claim : Derivable Γ (wordOfList (x :: y :: zs)) (wordOfList (y :: x :: zs)) := by
      have h := hyp y List.mem_cons_self
      have := Derivable.cleft (u := wordOfList zs) h
      simpa [wordOfList_cons, mul_assoc] using this
    show Derivable Γ (wordOfList (List.reverseAux ys (x :: y :: zs)))
      (wordOfList (List.reverseAux ys (y :: x :: zs)))
    rw [List.reverseAux_eq, List.reverseAux_eq]
    exact Derivable.cright (u := wordOfList ys.reverse) claim

/-- The Agda's `lemma-unsplit`. -/
theorem lemma_unsplit :
    ∀ (ys : List X) (x : X) (zs : List X), (∀ y ∈ ys, commutes Γ x y) →
      Derivable Γ (wordOfList (x :: reverseAppend ys zs)) (wordOfList (unsplit less ys x zs))
  | [], _, _, _ => Derivable.refl _
  | y :: ys, x, zs, hyp => by
    unfold unsplit
    cases less x y with
    | true => exact lemma_unsplit ys x (y :: zs) (fun z hz => hyp z (List.mem_cons_of_mem _ hz))
    | false => exact lemma_reverse_append (y :: ys) x zs hyp

/-- The Agda's `lemma-insert`. -/
theorem lemma_insert (comm_sound : ∀ x y, comm x y = true → commutes Γ x y) (x : X)
    (xs : List X) :
    Derivable Γ (wordOfList (x :: xs)) (wordOfList (insert comm less x xs)) := by
  unfold insert
  have e := lemma_split1 (comm := comm) [] x xs
  have h1 : Derivable Γ (wordOfList (x :: xs))
      (wordOfList (x :: reverseAppend (split comm [] x xs).1 (split comm [] x xs).2)) := by
    rw [← e]; exact Derivable.refl _
  exact h1.trans (lemma_unsplit _ x _
    (lemma_split2 comm_sound [] x xs (fun _ h => absurd h List.not_mem_nil)))

/-- Every list is equivalent to its canonical form (the Agda's
`lemma-comm-canonical`). -/
theorem lemma_comm_canonical (comm_sound : ∀ x y, comm x y = true → commutes Γ x y) :
    ∀ xs : List X, Derivable Γ (wordOfList xs) (wordOfList (commCanonical comm less xs))
  | [] => Derivable.refl _
  | x :: xs => by
    have ih := lemma_comm_canonical comm_sound xs
    have : Derivable Γ (wordOfList (x :: xs)) (wordOfList (x :: commCanonical comm less xs)) :=
      Derivable.cright (u := [x]ʷ) ih
    exact this.trans (lemma_insert comm_sound x _)

end Commuting

end EquaCert.Tactics
