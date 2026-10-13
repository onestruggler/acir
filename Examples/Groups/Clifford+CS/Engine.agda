------------------------------------------------------------------------
-- Presentations of groups
--
-- Machine-found derivations, checked by running them
--
-- The derivations of Lemmas.TwoWire and Lemmas.TwoWireMacro are found
-- off-line by a Knuth–Bendix completion, which records how each rule
-- it adds follows from the ones before.  Here an equation is a pair of
-- letter lists with a proof (Eqn), and a derivation of a new one is a
-- list of steps — `rw i e` rewrites the occurrence of lhs e at
-- position i to rhs e, and `rw⁻ i e` the other way — that `run`
-- executes on the letters.  `derive l r ss refl` checks by evaluation
-- that the steps take l to r, and run-sound turns that into a proof:
-- what is elaborated and stored is the list of steps, each naming the
-- equation it uses, rather than every intermediate list.  This is the
-- engine of Real-Clifford over any alphabet whose letters have an
-- injective code in ℕ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

module Examples.Groups.Clifford+CS.Engine
  {X : Set} (Γ : WRel X)
  (code : X → ℕ) (decode : ℕ → X) (decode-code : ∀ x → decode (code x) ≡ x)
  where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (_≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)

import Presentation.Base as PB
open PB Γ using (_≈_ ; refl ; sym ; trans ; cong)
open import Presentation.Tactic.AssociativitySolver using (module Assoc)
open Assoc Γ public using (to-list ; from-list)
open Assoc Γ using (fl-homo ; lemma-ft)

------------------------------------------------------------------------
-- Equality of letters and of lists, decided

eqX : X → X → Bool
eqX x y = code x ≡ᵇ code y

eqX-sound : ∀ x y → eqX x y ≡ true → x ≡ y
eqX-sound x y h =
  Eq.trans (Eq.sym (decode-code x))
    (Eq.trans (Eq.cong decode (≡ᵇ⇒≡ (code x) (code y) (Eq.subst T (Eq.sym h) tt)))
              (decode-code y))

eqL : List X → List X → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqX x y ∧ eqL xs ys

eqL-sound : (xs ys : List X) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = Eq.refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h with eqX x y in e
eqL-sound (x ∷ xs) (y ∷ ys) h  | true  = Eq.cong₂ _∷_ (eqX-sound x y e) (eqL-sound xs ys h)
eqL-sound (x ∷ xs) (y ∷ ys) () | false

------------------------------------------------------------------------
-- Equations

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List X
    prf     : from-list lhs ≈ from-list rhs

open Eqn public

sym⁼ : Eqn → Eqn
sym⁼ (eqn l r p) = eqn r l (sym p)

-- An equation of words, as the equation of their letter lists.
⌊_⌋⁼ : ∀ {w v} → w ≈ v → Eqn
⌊_⌋⁼ {w} {v} e = eqn (to-list w) (to-list v) (trans lemma-ft (trans e (sym lemma-ft)))

-- And back.
⌈_⌉⁼ : ∀ {w v} (e : Eqn) → to-list w ≡ lhs e → to-list v ≡ rhs e → w ≈ v
⌈_⌉⁼ {w} {v} e p q =
  trans (sym lemma-ft) (trans (≡⇒≈ p) (trans (prf e) (trans (≡⇒≈ (Eq.sym q)) lemma-ft)))
  where
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → from-list xs ≈ from-list ys
  ≡⇒≈ Eq.refl = refl

------------------------------------------------------------------------
-- Running a derivation

data Step : Set where
  rw rw⁻ : ℕ → Eqn → Step

rewrite-at : ℕ → List X → List X → List X → List X
rewrite-at i l r xs = take i xs ++ (r ++ drop (length l) (drop i xs))

matches-at : ℕ → List X → List X → Bool
matches-at i l xs = eqL (take (length l) (drop i xs)) l

run : List Step → List X → Maybe (List X)
run []              xs = just xs
run (rw i e ∷ ss)   xs =
  if matches-at i (lhs e) xs then run ss (rewrite-at i (lhs e) (rhs e) xs) else nothing
run (rw⁻ i e ∷ ss)  xs =
  if matches-at i (rhs e) xs then run ss (rewrite-at i (rhs e) (lhs e) xs) else nothing

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → from-list xs ≈ from-list ys
  ≡⇒≈ Eq.refl = refl

  fl++ : ∀ xs ys → from-list (xs ++ ys) ≈ from-list xs • from-list ys
  fl++ = fl-homo

  -- Rewriting l to r inside xs, where l is found.
  rw-sound : ∀ i l r xs → from-list l ≈ from-list r → matches-at i l xs ≡ true →
             from-list xs ≈ from-list (rewrite-at i l r xs)
  rw-sound i l r xs e h =
    trans (≡⇒≈ (Eq.sym (take++drop≡id i xs)))
    (trans (fl++ (take i xs) (drop i xs))
    (trans (cong refl (trans (≡⇒≈ (Eq.sym (take++drop≡id m (drop i xs))))
                      (trans (fl++ (take m (drop i xs)) rest)
                      (trans (cong (trans (≡⇒≈ (eqL-sound _ _ h)) e) refl)
                             (sym (fl++ r rest))))))
           (sym (fl++ (take i xs) (r ++ rest)))))
    where
    m = length l
    rest = drop m (drop i xs)

run-sound : (ss : List Step) (xs ys : List X) → run ss xs ≡ just ys →
            from-list xs ≈ from-list ys
run-sound []             xs ys Eq.refl = refl
run-sound (rw i e ∷ ss)  xs ys h with matches-at i (lhs e) xs in c
run-sound (rw i e ∷ ss)  xs ys h  | true  =
  trans (rw-sound i (lhs e) (rhs e) xs (prf e) c)
        (run-sound ss (rewrite-at i (lhs e) (rhs e) xs) ys h)
run-sound (rw i e ∷ ss)  xs ys () | false
run-sound (rw⁻ i e ∷ ss) xs ys h with matches-at i (rhs e) xs in c
run-sound (rw⁻ i e ∷ ss) xs ys h  | true  =
  trans (rw-sound i (rhs e) (lhs e) xs (sym (prf e)) c)
        (run-sound ss (rewrite-at i (rhs e) (lhs e) xs) ys h)
run-sound (rw⁻ i e ∷ ss) xs ys () | false

-- A derivation: the equation from the steps that take l to r.
derive : (l r : List X) (ss : List Step) → run ss l ≡ just r → Eqn
derive l r ss h = eqn l r (run-sound ss l r h)
