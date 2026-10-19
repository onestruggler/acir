------------------------------------------------------------------------
-- Presentations of groups
--
-- Chains of segment replacements on three wires (Real-Clifford+CH's
-- SegChain, for the CCX+H rules).
--
-- A line is a list of circuits read right-nested (`⦅_⦆`); a step
-- replaces the n entries from position k by a list proved equal to them,
-- and `run` turns a chain of steps into one equation.  Each step's
-- equation is typed by the line it is applied to, so no intermediate
-- line is written out.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Chain where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit

private
  W : Set
  W = Circuit 3

  refl≡ : ∀ {u v : W} → u ≡ v → 3 ⊢ u ≈ v
  refl≡ Eq.refl = refl

⦅_⦆ : List W → W
⦅ [] ⦆         = ε
⦅ x ∷ [] ⦆     = x
⦅ x ∷ y ∷ xs ⦆ = x • ⦅ y ∷ xs ⦆

⦅⦆-∷ : ∀ (x : W) (xs : List W) → 3 ⊢ ⦅ x ∷ xs ⦆ ≈ x • ⦅ xs ⦆
⦅⦆-∷ x []       = sym right-unit
⦅⦆-∷ x (y ∷ xs) = refl

⦅⦆-++ : ∀ (xs ys : List W) → 3 ⊢ ⦅ xs ++ ys ⦆ ≈ ⦅ xs ⦆ • ⦅ ys ⦆
⦅⦆-++ []       ys = sym left-unit
⦅⦆-++ (x ∷ xs) ys =
  trans (⦅⦆-∷ x (xs ++ ys))
  (trans (cong refl (⦅⦆-++ xs ys))
  (trans (sym assoc) (cong (sym (⦅⦆-∷ x xs)) refl)))

private
  seg : ∀ (p x y s : List W) → 3 ⊢ ⦅ x ⦆ ≈ ⦅ y ⦆ → 3 ⊢ ⦅ p ++ x ++ s ⦆ ≈ ⦅ p ++ y ++ s ⦆
  seg p x y s e =
    trans (⦅⦆-++ p (x ++ s))
    (trans (cong refl (trans (⦅⦆-++ x s) (trans (cong e refl) (sym (⦅⦆-++ y s)))))
           (sym (⦅⦆-++ p (y ++ s))))

  drop-drop′ : ∀ (k n : ℕ) (xs : List W) → drop n (drop k xs) ≡ drop (k + n) xs
  drop-drop′ zero    n xs       = Eq.refl
  drop-drop′ (suc k) zero    [] = Eq.refl
  drop-drop′ (suc k) (suc n) [] = Eq.refl
  drop-drop′ (suc k) n (x ∷ xs) = drop-drop′ k n xs

-- Replace the n entries from position k by ys.
step : ∀ (k n : ℕ) (xs ys : List W) → 3 ⊢ ⦅ take n (drop k xs) ⦆ ≈ ⦅ ys ⦆ →
       3 ⊢ ⦅ xs ⦆ ≈ ⦅ take k xs ++ ys ++ drop (k + n) xs ⦆
step k n xs ys e =
  trans (refl≡ (Eq.cong ⦅_⦆ split))
  (trans (seg (take k xs) (take n (drop k xs)) ys (drop n (drop k xs)) e)
         (refl≡ (Eq.cong (λ r → ⦅ take k xs ++ ys ++ r ⦆) (drop-drop′ k n xs))))
  where
  split : xs ≡ take k xs ++ (take n (drop k xs) ++ drop n (drop k xs))
  split = Eq.trans (Eq.sym (take++drop≡id k xs))
                   (Eq.cong (take k xs ++_) (Eq.sym (take++drop≡id n (drop k xs))))

record Step (xs : List W) : Set where
  constructor at
  field
    k n : ℕ
    ys  : List W
    e   : 3 ⊢ ⦅ take n (drop k xs) ⦆ ≈ ⦅ ys ⦆

next : ∀ {xs : List W} → Step xs → List W
next {xs} (at k n ys _) = take k xs ++ ys ++ drop (k + n) xs

infixr 4 _▸_
data Chain : List W → List W → Set where
  done : ∀ {xs : List W} → Chain xs xs
  _▸_  : ∀ {xs zs : List W} (s : Step xs) → Chain (next s) zs → Chain xs zs

run : ∀ {xs zs : List W} → Chain xs zs → 3 ⊢ ⦅ xs ⦆ ≈ ⦅ zs ⦆
run done                   = refl
run {xs} (at k n ys e ▸ c) = trans (step k n xs ys e) (run c)
