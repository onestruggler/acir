------------------------------------------------------------------------
-- Presentations of groups
--
-- A small rewriting engine for equations between concrete words of any
-- presentation.
--
-- After Examples.Groups.CCX+HH.Natural.Engine, without its commutation
-- step: an equation is a pair of letter lists with a derivation
-- (`Eqn`); a derivation of a new equation is a list of steps
-- `rw i e`, each rewriting the occurrence of lhs e at position i to
-- rhs e, run on the letters and closed by refl (`derive`).  The
-- alphabet needs a Boolean equality that implies propositional
-- equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel)

module Presentation.Rewrite
  {A : Set} (Γ : WRel A)
  (eqA : A → A → Bool) (eqA-sound : ∀ x y → eqA x y ≡ true → x ≡ y)
  where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (module Associative)
open Associative using (word-of-list ; lemma-append)

open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

------------------------------------------------------------------------
-- Letter lists as words

⟪_⟫ : List A → Word A
⟪_⟫ = word-of-list

⟪++⟫ : (xs ys : List A) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
⟪++⟫ xs ys = sym (lemma-append xs ys)

⟪≈⟫ : {xs ys : List A} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
⟪≈⟫ Eq.refl = refl

eqL : List A → List A → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqA x y ∧ eqL xs ys

eqL-sound : (xs ys : List A) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = Eq.refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h with eqA x y in e
eqL-sound (x ∷ xs) (y ∷ ys) h  | true  = Eq.cong₂ _∷_ (eqA-sound x y e) (eqL-sound xs ys h)
eqL-sound (x ∷ xs) (y ∷ ys) () | false

------------------------------------------------------------------------
-- Equations

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List A
    prf     : ⟪ lhs ⟫ ≈ ⟪ rhs ⟫

open Eqn public

sym⁼ : Eqn → Eqn
sym⁼ (eqn l r p) = eqn r l (sym p)

-- An equation between words, with its letter lists.
eqnʷ : (l r : List A) → ⟪ l ⟫ ≈ ⟪ r ⟫ → Eqn
eqnʷ = eqn

------------------------------------------------------------------------
-- Running a derivation

data Step : Set where
  rw : ℕ → Eqn → Step

rewrite-at : ℕ → Eqn → List A → List A
rewrite-at i e xs = take i xs ++ (rhs e ++ drop (length (lhs e)) (drop i xs))

matches-at : ℕ → Eqn → List A → Bool
matches-at i e xs = eqL (take (length (lhs e)) (drop i xs)) (lhs e)

run : List Step → List A → Maybe (List A)
run []            xs = just xs
run (rw i e ∷ ss) xs =
  if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

rw-sound : (i : ℕ) (e : Eqn) (xs : List A) → matches-at i e xs ≡ true →
           ⟪ xs ⟫ ≈ ⟪ rewrite-at i e xs ⟫
rw-sound i e xs h = begin
  ⟪ xs ⟫                                          ≈⟨ ⟪≈⟫ (Eq.sym (take++drop≡id i xs)) ⟩
  ⟪ take i xs ++ drop i xs ⟫                      ≈⟨ ⟪++⟫ (take i xs) (drop i xs) ⟩
  ⟪ take i xs ⟫ • ⟪ drop i xs ⟫                   ≈⟨ cong refl (⟪≈⟫ (Eq.sym (take++drop≡id m (drop i xs)))) ⟩
  ⟪ take i xs ⟫ • ⟪ take m (drop i xs) ++ rest ⟫  ≈⟨ cong refl (⟪++⟫ (take m (drop i xs)) rest) ⟩
  ⟪ take i xs ⟫ • (⟪ take m (drop i xs) ⟫ • ⟪ rest ⟫)
                                                  ≈⟨ cong refl (cong (⟪≈⟫ (eqL-sound _ _ h)) refl) ⟩
  ⟪ take i xs ⟫ • (⟪ lhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (cong (prf e) refl) ⟩
  ⟪ take i xs ⟫ • (⟪ rhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (sym (⟪++⟫ (rhs e) rest)) ⟩
  ⟪ take i xs ⟫ • ⟪ rhs e ++ rest ⟫               ≈⟨ sym (⟪++⟫ (take i xs) (rhs e ++ rest)) ⟩
  ⟪ rewrite-at i e xs ⟫                           ∎
  where
  open SR (PP.word-setoid Γ)
  m = length (lhs e)
  rest = drop m (drop i xs)

run-sound : (ss : List Step) (xs ys : List A) → run ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
run-sound []            xs ys Eq.refl = refl
run-sound (rw i e ∷ ss) xs ys h with matches-at i e xs in c
run-sound (rw i e ∷ ss) xs ys h  | true  = trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
run-sound (rw i e ∷ ss) xs ys () | false

-- A derivation: an equation from the steps that turn lhs into rhs.
derive : (l r : List A) (ss : List Step) → run ss l ≡ just r → Eqn
derive l r ss h = eqn l r (run-sound ss l r h)
