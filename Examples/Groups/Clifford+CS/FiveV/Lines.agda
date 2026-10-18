------------------------------------------------------------------------
-- Presentations of groups
--
-- Derivations as chains of segment replacements, at any width, over any
-- alphabet of macro letters, in the theory of Five.Rules
--
-- Four.Chain's engine made generic: a line is a list of letters, spelled
-- by ⟪_⟫ʷ; a step replaces the n letters from position k by a list with
-- an equation for the segment, and `run` assembles a chain of steps into
-- the equation of its first and last line (Real-Clifford+CH's Eq80).
-- Five.Win and Five.Chain instantiate it at the same arguments, so their
-- lines are one function.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)

module Examples.Groups.Clifford+CS.FiveV.Lines
  (W : ℕ) (Mac : Set) (⟪_⟫ : Mac → Circuit W) where

open import Data.List using (List ; [] ; _∷_ ; _++_ ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.FiveV.Rules using (_XVRel,_===_)

private
  open module T = Tools (_XVRel,_===_ W)

------------------------------------------------------------------------
-- Lines

⟪_⟫ʷ : List Mac → Circuit W
⟪ [] ⟫ʷ           = ε
⟪ ℓ ∷ [] ⟫ʷ       = ⟪ ℓ ⟫
⟪ ℓ ∷ (m ∷ ls) ⟫ʷ = ⟪ ℓ ⟫ • ⟪ m ∷ ls ⟫ʷ

⟪⟫-∷ : ∀ ℓ ls → ⟪ ℓ ∷ ls ⟫ʷ ≈ ⟪ ℓ ⟫ • ⟪ ls ⟫ʷ
⟪⟫-∷ ℓ []       = sym right-unit
⟪⟫-∷ ℓ (m ∷ ls) = refl

⟪⟫-++ : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
⟪⟫-++ []       ys = sym left-unit
⟪⟫-++ (x ∷ xs) ys =
  trans (⟪⟫-∷ x (xs ++ ys))
  (trans (back ⟪ x ⟫ (⟪⟫-++ xs ys))
  (trans (sym assoc) (front ⟪ ys ⟫ʷ (sym (⟪⟫-∷ x xs)))))

private
  seg : ∀ p x y s → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ p ++ x ++ s ⟫ʷ ≈ ⟪ p ++ y ++ s ⟫ʷ
  seg p x y s e =
    trans (⟪⟫-++ p (x ++ s))
    (trans (back ⟪ p ⟫ʷ (trans (⟪⟫-++ x s) (trans (front ⟪ s ⟫ʷ e) (sym (⟪⟫-++ y s)))))
           (sym (⟪⟫-++ p (y ++ s))))

  drop-drop : ∀ (k n : ℕ) (xs : List Mac) → drop n (drop k xs) ≡ drop (k + n) xs
  drop-drop zero    n xs       = Eq.refl
  drop-drop (suc k) zero    [] = Eq.refl
  drop-drop (suc k) (suc n) [] = Eq.refl
  drop-drop (suc k) n (x ∷ xs) = drop-drop k n xs

  refl≡ : ∀ {w v : Circuit W} → w ≡ v → w ≈ v
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- Replacing the n letters from position k

step : ∀ (k n : ℕ) (xs ys : List Mac) → ⟪ take n (drop k xs) ⟫ʷ ≈ ⟪ ys ⟫ʷ →
       ⟪ xs ⟫ʷ ≈ ⟪ take k xs ++ ys ++ drop (k + n) xs ⟫ʷ
step k n xs ys e =
  trans (refl≡ (Eq.cong ⟪_⟫ʷ split))
  (trans (seg (take k xs) (take n (drop k xs)) ys (drop n (drop k xs)) e)
         (refl≡ (Eq.cong (λ r → ⟪ take k xs ++ ys ++ r ⟫ʷ) (drop-drop k n xs))))
  where
  split : xs ≡ take k xs ++ (take n (drop k xs) ++ drop n (drop k xs))
  split = Eq.trans (Eq.sym (take++drop≡id k xs))
                   (Eq.cong (take k xs ++_) (Eq.sym (take++drop≡id n (drop k xs))))

record Step (xs : List Mac) : Set where
  constructor at
  field
    k n : ℕ
    ys  : List Mac
    e   : ⟪ take n (drop k xs) ⟫ʷ ≈ ⟪ ys ⟫ʷ

next : ∀ {xs : List Mac} → Step xs → List Mac
next {xs} (at k n ys _) = take k xs ++ ys ++ drop (k + n) xs

infixr 4 _▸_
data Chain : List Mac → List Mac → Set where
  done : ∀ {xs : List Mac} → Chain xs xs
  _▸_  : ∀ {xs zs : List Mac} (s : Step xs) → Chain (next s) zs → Chain xs zs

run : ∀ {xs zs : List Mac} → Chain xs zs → ⟪ xs ⟫ʷ ≈ ⟪ zs ⟫ʷ
run done                   = refl
run {xs} (at k n ys e ▸ c) = trans (step k n xs ys e) (run c)
