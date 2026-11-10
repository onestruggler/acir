/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Words up to associativity and commutation

Translation of what the four-bit development uses of
`Presentation/Tactics/Words.agda`: `commutes` (two generators commute under
a theory), the module `Associative`'s `word-of-list`, and the module
`Commuting`'s canonical forms modulo commutation (`comm-canonical`, the
least equivalent word in the reverse lexicographic order) with their
soundness (`lemma-comm-canonical`).  `PlacedEngine` instantiates them at
the placed letters.

**Deviations from the Agda.**

* Words are `FreeMonoid`, which is `List`, so associativity is free and
  `word-of-list` is `FreeMonoid.ofList` (`Associative.wordOfList`); the
  Agda's `general-assoc` and its relatives are not needed.
* The Agda's `Commuting X Γ comm less` takes `comm : X → X → Maybe
  (commutes Γ x y)`.  Here `comm` is a Boolean test and its soundness a
  separate hypothesis (`∀ x y, comm x y = true → commutes Γ x y`), so that
  the canonical form is a function the kernel evaluates.  The algorithm
  (`split`, `unsplit`, `insert`) is the Agda's, as `Lib/Engine`'s section
  `Canon` (the foundation part's translation of the same Agda code, for the
  engine of `Kit`), which is reused here: `Commuting.commCanonical` is
  `Engine.canon` and `Commuting.lemma_comm_canonical` is
  `Engine.canon_sound`.
-/
import QCert.XCXCCX4bit.Lib.Engine

namespace QCert.XCXCCX4bit.Words

open QCert

variable {X : Type}

/-- Two generators commute under `Γ`. -/
def commutes (Γ : WRel X) (x y : X) : Prop :=
  Derivable Γ (FreeMonoid.of x * FreeMonoid.of y) (FreeMonoid.of y * FreeMonoid.of x)

/-- Two words commute under `Γ`. -/
def commutesWord (Γ : WRel X) (u v : Word X) : Prop := Derivable Γ (u * v) (v * u)

namespace Associative

/-- A list as a word (the Agda's `word-of-list`). -/
abbrev wordOfList (xs : List X) : Word X := FreeMonoid.ofList xs

theorem wordOfList_cons (x : X) (xs : List X) :
    wordOfList (x :: xs) = FreeMonoid.of x * wordOfList xs := rfl

theorem wordOfList_append (xs ys : List X) :
    wordOfList (xs ++ ys) = wordOfList xs * wordOfList ys := rfl

end Associative

namespace Commuting

variable (comm : X → X → Bool) (less : X → X → Bool)

/-- The canonical form of a word modulo commutation of generators (the
Agda's `comm-canonical`). -/
abbrev commCanonical (xs : List X) : List X := Engine.canon comm less xs

/-- Every word is equivalent to its canonical form (the Agda's
`lemma-comm-canonical`). -/
theorem lemma_comm_canonical {Γ : WRel X} (hc : ∀ x y, comm x y = true → commutes Γ x y)
    (xs : List X) :
    Derivable Γ (FreeMonoid.ofList xs) (FreeMonoid.ofList (commCanonical comm less xs)) :=
  Engine.canon_sound comm less hc xs

end Commuting

end QCert.XCXCCX4bit.Words
