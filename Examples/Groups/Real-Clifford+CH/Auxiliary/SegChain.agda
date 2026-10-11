------------------------------------------------------------------------
-- Presentations of groups
--
-- Chains of segment replacements, over any presentation
--
-- A long derivation in the paper is a sequence of lines, each obtained
-- from the one before by rewriting a few adjacent letters.  Here a line
-- is a list of words (`⟪_⟫` reads it right-nested), a step replaces the
-- n letters from position k by a list proved equal to them (`Step`),
-- and `run` turns a chain of steps into one equation.  Each step's
-- equation is typed by the line it is applied to, so no intermediate
-- line is ever written.  (Auxiliary.Eq80 has the same machinery for the
-- words of P; this is it once for every relation.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (Word ; WRel ; ε ; _•_)

module Examples.Groups.Real-Clifford+CH.Auxiliary.SegChain {X : Set} (Γ : WRel X) where

open import Data.List using (List ; [] ; _∷_ ; _++_ ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools Γ

private
  W : Set
  W = Word X

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- Words as lists of letters, and replacing a segment

⟪_⟫ : List W → W
⟪ [] ⟫         = ε
⟪ x ∷ [] ⟫     = x
⟪ x ∷ y ∷ xs ⟫ = x • ⟪ y ∷ xs ⟫

⟪⟫-∷ : ∀ (x : W) (xs : List W) → ⟪ x ∷ xs ⟫ ≈ x • ⟪ xs ⟫
⟪⟫-∷ x []       = sym right-unit
⟪⟫-∷ x (y ∷ xs) = refl

⟪⟫-++ : ∀ (xs ys : List W) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
⟪⟫-++ []       ys = sym left-unit
⟪⟫-++ (x ∷ xs) ys =
  trans (⟪⟫-∷ x (xs ++ ys))
  (trans (back x (⟪⟫-++ xs ys))
  (trans (sym assoc) (front ⟪ ys ⟫ (sym (⟪⟫-∷ x xs)))))

private
  seg : ∀ (p x y s : List W) → ⟪ x ⟫ ≈ ⟪ y ⟫ → ⟪ p ++ x ++ s ⟫ ≈ ⟪ p ++ y ++ s ⟫
  seg p x y s e =
    trans (⟪⟫-++ p (x ++ s))
    (trans (back ⟪ p ⟫ (trans (⟪⟫-++ x s) (trans (front ⟪ s ⟫ e) (sym (⟪⟫-++ y s)))))
           (sym (⟪⟫-++ p (y ++ s))))

  drop-drop′ : ∀ (k n : ℕ) (xs : List W) → drop n (drop k xs) ≡ drop (k + n) xs
  drop-drop′ zero    n xs       = Eq.refl
  drop-drop′ (suc k) zero    [] = Eq.refl
  drop-drop′ (suc k) (suc n) [] = Eq.refl
  drop-drop′ (suc k) n (x ∷ xs) = drop-drop′ k n xs

-- Replace the n letters from position k by ys.
step : ∀ (k n : ℕ) (xs ys : List W) → ⟪ take n (drop k xs) ⟫ ≈ ⟪ ys ⟫ →
       ⟪ xs ⟫ ≈ ⟪ take k xs ++ ys ++ drop (k + n) xs ⟫
step k n xs ys e =
  trans (refl≡ (Eq.cong ⟪_⟫ split))
  (trans (seg (take k xs) (take n (drop k xs)) ys (drop n (drop k xs)) e)
         (refl≡ (Eq.cong (λ r → ⟪ take k xs ++ ys ++ r ⟫) (drop-drop′ k n xs))))
  where
  split : xs ≡ take k xs ++ (take n (drop k xs) ++ drop n (drop k xs))
  split = Eq.trans (Eq.sym (take++drop≡id k xs))
                   (Eq.cong (take k xs ++_) (Eq.sym (take++drop≡id n (drop k xs))))

-- A chain of replacements.
record Step (xs : List W) : Set where
  constructor at
  field
    k n : ℕ
    ys  : List W
    e   : ⟪ take n (drop k xs) ⟫ ≈ ⟪ ys ⟫

next : ∀ {xs : List W} → Step xs → List W
next {xs} (at k n ys _) = take k xs ++ ys ++ drop (k + n) xs

infixr 4 _▸_
data Chain : List W → List W → Set where
  done : ∀ {xs : List W} → Chain xs xs
  _▸_  : ∀ {xs zs : List W} (s : Step xs) → Chain (next s) zs → Chain xs zs

run : ∀ {xs zs : List W} → Chain xs zs → ⟪ xs ⟫ ≈ ⟪ zs ⟫
run done                   = refl
run {xs} (at k n ys e ▸ c) = trans (step k n xs ys e) (run c)
