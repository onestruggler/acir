------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire derivations as chains of segment replacements over macro
-- letters
--
-- A derivation of `scratchpad/deriv.py`, lowered to primitive steps
-- (`scratchpad/four/lower.py`), is a list of lines of macro letters
-- (Four.Letters) and, between consecutive lines, the replacement of one
-- segment by a word with the same operator.  `run` assembles the
-- equation of the first and the last line from the segments' equations,
-- each typed by the line it is applied to (Real-Clifford+CH's Eq80).
-- The segments' equations come from `Windows.win` (a literal window on
-- three wires, one evaluation at width 3), `low-comm` (a structural
-- commutation of wires 0 1 against 2 3), `by-assoc` (a re-bracketing),
-- the two four-wire rules at their canonical placement, and earlier
-- lemmas; `scratchpad/four/emit.py` writes them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Chain where

open import Data.List using (List ; [] ; _∷_ ; _++_ ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Four.Letters public

open Tools (_VRel,_===_ 4) public

------------------------------------------------------------------------
-- The structural commutation of the bottom three wires against the top

low₃-comm : (u : Circuit 3) (v : Circuit 1) → (u ↓ᵏ 1) • v ↑ ↑ ↑ ≈ v ↑ ↑ ↑ • (u ↓ᵏ 1)
low₃-comm [ gate₀ h ]ʷ v = sym (comm-gate₀-w h (v ↑ ↑ ↑))
low₃-comm [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑ ↑))
low₃-comm [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h (v ↑))
low₃-comm [ g ↥ ]ʷ    v = lemma-cong↑ (([ g ]ʷ ↓ᵏ 1) • v ↑ ↑) (v ↑ ↑ • ([ g ]ʷ ↓ᵏ 1)) (low-comm [ g ]ʷ v)
low₃-comm ε           v = trans left-unit (sym right-unit)
low₃-comm (u • t)     v =
  trans assoc (trans (back (u ↓ᵏ 1) (low₃-comm t v))
  (trans (sym assoc) (trans (front (t ↓ᵏ 1) (low₃-comm u v)) assoc)))

------------------------------------------------------------------------
-- Lines

⟪_⟫ʷ : List Mac → Circuit 4
⟪ [] ⟫ʷ           = ε
⟪ ℓ ∷ [] ⟫ʷ       = ⟪ ℓ ⟫
⟪ ℓ ∷ (m ∷ ls) ⟫ʷ = ⟪ ℓ ⟫ • ⟪ m ∷ ls ⟫ʷ

private
  ⟪⟫-∷ : ∀ ℓ ls → ⟪ ℓ ∷ ls ⟫ʷ ≈ ⟪ ℓ ⟫ • ⟪ ls ⟫ʷ
  ⟪⟫-∷ ℓ []       = sym right-unit
  ⟪⟫-∷ ℓ (m ∷ ls) = refl

  ⟪⟫-++ : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
  ⟪⟫-++ []       ys = sym left-unit
  ⟪⟫-++ (x ∷ xs) ys =
    trans (⟪⟫-∷ x (xs ++ ys))
    (trans (back ⟪ x ⟫ (⟪⟫-++ xs ys))
    (trans (sym assoc) (front ⟪ ys ⟫ʷ (sym (⟪⟫-∷ x xs)))))

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

  refl≡ : ∀ {w v : Circuit 4} → w ≡ v → w ≈ v
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
