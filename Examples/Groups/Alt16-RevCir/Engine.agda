------------------------------------------------------------------------
-- Presentations of groups
--
-- A proof engine for equations between concrete circuits over the
-- gates X, CX, CCX and Ex
--
-- After Examples.Independence.Engine, for this folder's gates and any
-- relation on them lifted to a PROP.  An equation is a pair of letter
-- lists with a derivation (Eqn).  A derivation of a new equation is a
-- list of steps run on the letters: rw i e rewrites the occurrence of
-- the left side of e at position i to its right side.  run executes
-- the steps, and run-sound turns a successful run into a derivation, so
-- that a proof is a list of steps closed by refl.  Equations are
-- transformed by sym⁼ and lift⁼ (one wire up), built from equations
-- between words by eqnʷ, and read as equations between words by
-- eqn→.  Lists are in the order of words: diagram order, the head
-- first.
--
-- There is no step for the commutation of letters on disjoint wires:
-- the derivations run here come from a Knuth–Bendix completion in which
-- a commutation is a rule like any other.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

open import Examples.Groups.Alt16-RevCir.Syntactics
  using ( Gate ; X-gate ; CX-gate ; Ex-gate ; CCX-gate
        ; Gen ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; _↥
        ; Circuit ; CRel ; _↑ ; module Lift-To-Prop )

module Examples.Groups.Alt16-RevCir.Engine
  (_SRel,_===_ : (n : ℕ) → CRel n)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.List.Base
  using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop ; map)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open Lift-To-Prop _SRel,_===_ using (_VRel,_===_ ; _⊢_≈_ ; lemma-cong↑)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Equality of letters

private
  eqᵍ : Gate k → Gate k → Bool
  eqᵍ X-gate   X-gate   = true
  eqᵍ CX-gate  CX-gate  = true
  eqᵍ CX-gate  Ex-gate  = false
  eqᵍ Ex-gate  CX-gate  = false
  eqᵍ Ex-gate  Ex-gate  = true
  eqᵍ CCX-gate CCX-gate = true

  eqᵍ-sound : (a b : Gate k) → eqᵍ a b ≡ true → a ≡ b
  eqᵍ-sound X-gate   X-gate   _ = refl
  eqᵍ-sound CX-gate  CX-gate  _ = refl
  eqᵍ-sound Ex-gate  Ex-gate  _ = refl
  eqᵍ-sound CCX-gate CCX-gate _ = refl
  eqᵍ-sound CX-gate  Ex-gate  ()
  eqᵍ-sound Ex-gate  CX-gate  ()

eqG : Gen n → Gen n → Bool
eqG (gate₀ a) (gate₀ b) = eqᵍ a b
eqG (gate₀ a) (gate₁ b) = false
eqG (gate₀ a) (gate₂ b) = false
eqG (gate₀ a) (gate₃ b) = false
eqG (gate₀ a) (y ↥)     = false
eqG (gate₁ a) (gate₀ b) = false
eqG (gate₁ a) (gate₁ b) = eqᵍ a b
eqG (gate₁ a) (gate₂ b) = false
eqG (gate₁ a) (gate₃ b) = false
eqG (gate₁ a) (y ↥)     = false
eqG (gate₂ a) (gate₀ b) = false
eqG (gate₂ a) (gate₁ b) = false
eqG (gate₂ a) (gate₂ b) = eqᵍ a b
eqG (gate₂ a) (gate₃ b) = false
eqG (gate₂ a) (y ↥)     = false
eqG (gate₃ a) (gate₀ b) = false
eqG (gate₃ a) (gate₁ b) = false
eqG (gate₃ a) (gate₂ b) = false
eqG (gate₃ a) (gate₃ b) = eqᵍ a b
eqG (gate₃ a) (y ↥)     = false
eqG (x ↥)     (gate₀ b) = false
eqG (x ↥)     (gate₁ b) = false
eqG (x ↥)     (gate₂ b) = false
eqG (x ↥)     (gate₃ b) = false
eqG (x ↥)     (y ↥)     = eqG x y

eqG-sound : (x y : Gen n) → eqG x y ≡ true → x ≡ y
eqG-sound (gate₀ a) (gate₀ b) h = Eq.cong gate₀ (eqᵍ-sound a b h)
eqG-sound (gate₁ a) (gate₁ b) h = Eq.cong gate₁ (eqᵍ-sound a b h)
eqG-sound (gate₂ a) (gate₂ b) h = Eq.cong gate₂ (eqᵍ-sound a b h)
eqG-sound (gate₃ a) (gate₃ b) h = Eq.cong gate₃ (eqᵍ-sound a b h)
eqG-sound (x ↥)     (y ↥)     h = Eq.cong _↥ (eqG-sound x y h)
eqG-sound (gate₀ a) (gate₁ b) ()
eqG-sound (gate₀ a) (gate₂ b) ()
eqG-sound (gate₀ a) (gate₃ b) ()
eqG-sound (gate₀ a) (y ↥)     ()
eqG-sound (gate₁ a) (gate₀ b) ()
eqG-sound (gate₁ a) (gate₂ b) ()
eqG-sound (gate₁ a) (gate₃ b) ()
eqG-sound (gate₁ a) (y ↥)     ()
eqG-sound (gate₂ a) (gate₀ b) ()
eqG-sound (gate₂ a) (gate₁ b) ()
eqG-sound (gate₂ a) (gate₃ b) ()
eqG-sound (gate₂ a) (y ↥)     ()
eqG-sound (gate₃ a) (gate₀ b) ()
eqG-sound (gate₃ a) (gate₁ b) ()
eqG-sound (gate₃ a) (gate₂ b) ()
eqG-sound (gate₃ a) (y ↥)     ()
eqG-sound (x ↥)     (gate₀ b) ()
eqG-sound (x ↥)     (gate₁ b) ()
eqG-sound (x ↥)     (gate₂ b) ()
eqG-sound (x ↥)     (gate₃ b) ()

eqL : List (Gen n) → List (Gen n) → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqG x y ∧ eqL xs ys

eqL-sound : (xs ys : List (Gen n)) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h with eqG x y in e
eqL-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_ (eqG-sound x y e) (eqL-sound xs ys h)
eqL-sound (x ∷ xs) (y ∷ ys) () | false

------------------------------------------------------------------------
-- Letter lists as circuits

⟪_⟫ : List (Gen n) → Circuit n
⟪ [] ⟫     = ε
⟪ x ∷ xs ⟫ = [ x ]ʷ • ⟪ xs ⟫

-- Shifting the letters shifts the word.
⟪map↥⟫ : (xs : List (Gen n)) → ⟪ map _↥ xs ⟫ ≡ ⟪ xs ⟫ ↑
⟪map↥⟫ []       = refl
⟪map↥⟫ (x ∷ xs) = Eq.cong ([ x ↥ ]ʷ •_) (⟪map↥⟫ xs)

module _ {n : ℕ} where

  open PB (n VRel,_===_)
    using (_≈_ ; sym ; trans ; cong ; assoc ; left-unit)
    renaming (refl to refl≈)

  ⟪++⟫ : (xs ys : List (Gen n)) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
  ⟪++⟫ []       ys = sym left-unit
  ⟪++⟫ (x ∷ xs) ys = trans (cong refl≈ (⟪++⟫ xs ys)) (sym assoc)

  ⟪≈⟫ : {xs ys : List (Gen n)} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  ⟪≈⟫ refl = refl≈

------------------------------------------------------------------------
-- Equations

record Eqn (n : ℕ) : Set where
  constructor eqn
  field
    lhs⁼ rhs⁼ : List (Gen n)
    prf       : n ⊢ ⟪ lhs⁼ ⟫ ≈ ⟪ rhs⁼ ⟫

open Eqn public

sym⁼ : Eqn n → Eqn n
sym⁼ (eqn l r p) = eqn r l (PB.sym p)

-- An equation between words, read as one between letter lists: the
-- lists are the words' letters, whatever their bracketing (both
-- typically by refl).
eqnʷ : {w v : Circuit n} (l r : List (Gen n)) → n ⊢ w ≈ v →
       PP.to-list (n VRel,_===_) ⟪ l ⟫ ≡ PP.to-list (n VRel,_===_) w →
       PP.to-list (n VRel,_===_) v ≡ PP.to-list (n VRel,_===_) ⟪ r ⟫ →
       Eqn n
eqnʷ {n} l r p e₁ e₂ =
  eqn l r (PB.trans (by-assoc e₁) (PB.trans p (by-assoc e₂)))
  where open PP (n VRel,_===_) using (by-assoc)

-- And back: an equation between any two words with those letters.
eqn→ : (e : Eqn n) {w v : Circuit n} →
       PP.to-list (n VRel,_===_) w ≡
         PP.to-list (n VRel,_===_) ⟪ lhs⁼ e ⟫ →
       PP.to-list (n VRel,_===_) ⟪ rhs⁼ e ⟫ ≡
         PP.to-list (n VRel,_===_) v →
       n ⊢ w ≈ v
eqn→ {n} (eqn l r p) e₁ e₂ =
  PB.trans (by-assoc e₁) (PB.trans p (by-assoc e₂))
  where open PP (n VRel,_===_) using (by-assoc)

-- One wire up.
lift⁼ : Eqn n → Eqn (₁₊ n)
lift⁼ {n} (eqn l r p) = eqn (map _↥ l) (map _↥ r)
  (Eq.subst₂ (₁₊ n ⊢_≈_) (Eq.sym (⟪map↥⟫ l)) (Eq.sym (⟪map↥⟫ r))
             (lemma-cong↑ ⟪ l ⟫ ⟪ r ⟫ p))

------------------------------------------------------------------------
-- Running a derivation

data Step (n : ℕ) : Set where
  rw : ℕ → Eqn n → Step n

rewrite-at : ℕ → Eqn n → List (Gen n) → List (Gen n)
rewrite-at i e xs =
  take i xs ++ (rhs⁼ e ++ drop (length (lhs⁼ e)) (drop i xs))

matches-at : ℕ → Eqn n → List (Gen n) → Bool
matches-at i e xs = eqL (take (length (lhs⁼ e)) (drop i xs)) (lhs⁼ e)

run : List (Step n) → List (Gen n) → Maybe (List (Gen n))
run []            xs = just xs
run (rw i e ∷ ss) xs =
  if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; sym ; trans ; cong)
    renaming (refl to refl≈)

  rw-sound : (i : ℕ) (e : Eqn n) (xs : List (Gen n)) →
             matches-at i e xs ≡ true → ⟪ xs ⟫ ≈ ⟪ rewrite-at i e xs ⟫
  rw-sound i e xs h = begin
    ⟪ xs ⟫
      ≈⟨ ⟪≈⟫ (Eq.sym (take++drop≡id i xs)) ⟩
    ⟪ take i xs ++ drop i xs ⟫
      ≈⟨ ⟪++⟫ (take i xs) (drop i xs) ⟩
    ⟪ take i xs ⟫ • ⟪ drop i xs ⟫
      ≈⟨ cong refl≈ (⟪≈⟫ (Eq.sym (take++drop≡id m (drop i xs)))) ⟩
    ⟪ take i xs ⟫ • ⟪ take m (drop i xs) ++ rest ⟫
      ≈⟨ cong refl≈ (⟪++⟫ (take m (drop i xs)) rest) ⟩
    ⟪ take i xs ⟫ • (⟪ take m (drop i xs) ⟫ • ⟪ rest ⟫)
      ≈⟨ cong refl≈ (cong (⟪≈⟫ (eqL-sound _ _ h)) refl≈) ⟩
    ⟪ take i xs ⟫ • (⟪ lhs⁼ e ⟫ • ⟪ rest ⟫)
      ≈⟨ cong refl≈ (cong (prf e) refl≈) ⟩
    ⟪ take i xs ⟫ • (⟪ rhs⁼ e ⟫ • ⟪ rest ⟫)
      ≈⟨ cong refl≈ (sym (⟪++⟫ (rhs⁼ e) rest)) ⟩
    ⟪ take i xs ⟫ • ⟪ rhs⁼ e ++ rest ⟫
      ≈⟨ sym (⟪++⟫ (take i xs) (rhs⁼ e ++ rest)) ⟩
    ⟪ rewrite-at i e xs ⟫
      ∎
    where
    open SR (PP.word-setoid (n VRel,_===_))
    m = length (lhs⁼ e)
    rest = drop m (drop i xs)

  run-sound : (ss : List (Step n)) (xs ys : List (Gen n)) →
              run ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  run-sound []            xs ys refl = refl≈
  run-sound (rw i e ∷ ss) xs ys h with matches-at i e xs in c
  run-sound (rw i e ∷ ss) xs ys h  | true  =
    trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
  run-sound (rw i e ∷ ss) xs ys () | false

-- A derivation: an equation from the steps that turn lhs into rhs.
derive : (l r : List (Gen n)) (ss : List (Step n)) →
         run ss l ≡ just r → Eqn n
derive l r ss h = eqn l r (run-sound ss l r h)
