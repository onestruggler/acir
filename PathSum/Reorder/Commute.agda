------------------------------------------------------------------------
-- Presentations of groups
--
-- Two renumberings against one
--
-- A rule of figure 2 (Amy, QPL 2018) at a path variable is a head rule
-- after a renumbering, front j of PathSum.Reorder, which lists y_j
-- first and the other variables in their original order.
-- PathSum.Full nests two of them, front l′ ∘ front j, so its steps
-- include a head rule after a double renumbering.  This module relates
-- such a double renumbering to the single one at the same variable,
-- which is what it takes to read a step after two renumberings as a
-- step after one (PathSum.Full.Order2).
--
-- Position 0 of front (suc l) (front j ξ) is the original variable
-- v = punchIn j l, so both renumberings move the same variable to the
-- front.  They differ only in how they list the others: the single
-- one in their original order, the double one with y_j first.  So the
-- double renumbering is the single one followed by a renumbering of the
-- remaining variables alone, moving the remaining y_j -- at position
-- swapIdx j l among them -- to their front (front-front).  On
-- monomials this is a commutation of two insertions into a vector
-- (insertAt-comm):
--
--   insertAt (insertAt s l a) j b
--     ≡ insertAt (insertAt s (swapIdx j l) b) (punchIn j l) a,
--
-- both sides putting a at position punchIn j l, b at position j, and s
-- in order elsewhere.
--
-- Consequences, coefficient by coefficient: the quotient of the phase
-- by the head of the double renumbering is the quotient by y_v,
-- renumbered (/ʸ-front-front, and every monomial is reached: /ʸ-onto);
-- the two have the same constant coefficient (/ʸ-1ᵐ), and the
-- coefficient of a single path variable is that of another single
-- path variable (/ʸ-⟪⟫, the variable being moved j″ i); a quotient
-- vanishing in one vanishes in the other (≈0-front-front); and y_v is
-- absent from a polynomial when the head of its double renumbering is
-- (NoVar-front-front).  Nothing here depends on M or on the semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Reorder.Commute where

open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Subset using (Subset; Side; inside; outside; ⊥; ⁅_⁆)
open import Data.Integer.Base using (ℤ; 0ℤ; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using
  (Vec; []; _∷_; insertAt; removeAt; lookup; here)
open import Data.Vec.Properties using (insertAt-removeAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import PathSum.Base using (head-part)
open import PathSum.Polynomial using
  (Poly; 1ᵐ; y[_]; ⟪_⟫; 0ᴾ; _≈[_]_; NoVar)
open import PathSum.Reorder using (frontᴾ; _/ʸ_)

private
  variable
    A : Set
    n m : ℕ


------------------------------------------------------------------------
-- Two insertions commute

-- swapIdx j l is the position of the original j among the variables
-- other than punchIn j l (which is never j).

swapIdx : Fin (suc (suc m)) → Fin (suc m) → Fin (suc m)
swapIdx         zero    l       = zero
swapIdx         (suc j) zero    = j
swapIdx {zero}  (suc j) (suc ())
swapIdx {suc m} (suc j) (suc l) = suc (swapIdx j l)

-- Inserting a at l and then b at j is inserting b at swapIdx j l and
-- then a at punchIn j l.

insertAt-comm : (s : Vec A m) (j : Fin (suc (suc m))) (l : Fin (suc m))
                (a b : A) →
                insertAt (insertAt s l a) j b ≡
                insertAt (insertAt s (swapIdx j l) b) (punchIn j l) a
insertAt-comm s       zero    l       a b = refl
insertAt-comm s       (suc j) zero    a b = refl
insertAt-comm []      (suc j) (suc ()) a b
insertAt-comm (x ∷ s) (suc j) (suc l) a b =
  cong (x ∷_) (insertAt-comm s j l a b)


------------------------------------------------------------------------
-- The empty set and the singletons

insertAt-⊥ : (j : Fin (suc m)) → insertAt (⊥ {m}) j outside ≡ ⊥
insertAt-⊥         zero    = refl
insertAt-⊥ {zero}  (suc ())
insertAt-⊥ {suc m} (suc j) = cong (outside ∷_) (insertAt-⊥ j)

insertAt-⊥-inside : (j : Fin (suc m)) → insertAt (⊥ {m}) j inside ≡ ⁅ j ⁆
insertAt-⊥-inside         zero    = refl
insertAt-⊥-inside {zero}  (suc ())
insertAt-⊥-inside {suc m} (suc j) = cong (outside ∷_) (insertAt-⊥-inside j)

insertAt-⁅⁆ : (j : Fin (suc m)) (t : Fin m) →
              insertAt ⁅ t ⁆ j outside ≡ ⁅ punchIn j t ⁆
insertAt-⁅⁆ zero    t       = refl
insertAt-⁅⁆ (suc j) zero    = cong (inside ∷_) (insertAt-⊥ j)
insertAt-⁅⁆ (suc j) (suc t) = cong (outside ∷_) (insertAt-⁅⁆ j t)

-- The original variable that front j lists at position i.

moved : Fin (suc m) → Fin (suc m) → Fin (suc m)
moved j zero    = j
moved j (suc t) = punchIn j t


------------------------------------------------------------------------
-- Polynomials

-- The double renumbering is the single one at punchIn j l followed by
-- a renumbering of the other variables at swapIdx j l.

front-front : (j : Fin (suc (suc m))) (l : Fin (suc m))
              (R : Poly n (suc (suc m))) (α : Subset n) (a b : Side)
              (s : Subset m) →
              frontᴾ (suc l) (frontᴾ j R) (α , a ∷ b ∷ s) ≡
              frontᴾ (punchIn j l) R (α , a ∷ insertAt s (swapIdx j l) b)
front-front j l R α a b s = cong (λ t → R (α , t)) (insertAt-comm s j l a b)

-- Every monomial of the single renumbering is one of the double's.

front-front-onto : (j : Fin (suc (suc m))) (l : Fin (suc m))
                   (R : Poly n (suc (suc m))) (α : Subset n) (a : Side)
                   (t : Subset (suc m)) →
                   frontᴾ (punchIn j l) R (α , a ∷ t) ≡
                   frontᴾ (suc l) (frontᴾ j R)
                     (α , a ∷ lookup t (swapIdx j l) ∷
                          removeAt t (swapIdx j l))
front-front-onto j l R α a t = trans
  (cong (λ u → frontᴾ (punchIn j l) R (α , a ∷ u))
        (sym (insertAt-removeAt t (swapIdx j l))))
  (sym (front-front j l R α a (lookup t (swapIdx j l))
                    (removeAt t (swapIdx j l))))


------------------------------------------------------------------------
-- Quotients

-- The quotient by the head of the double renumbering is the quotient
-- by y_(punchIn j l), renumbered at swapIdx j l ...

/ʸ-front-front : (j : Fin (suc (suc m))) (l : Fin (suc m))
                 (R : Poly n (suc (suc m))) (α : Subset n) (b : Side)
                 (s : Subset m) →
                 head-part (frontᴾ (suc l) (frontᴾ j R)) (α , b ∷ s) ≡
                 (R /ʸ punchIn j l) (α , insertAt s (swapIdx j l) b)
/ʸ-front-front j l R α b s = front-front j l R α inside b s

-- ... so every coefficient of the latter is one of the former ...

/ʸ-onto : (j : Fin (suc (suc m))) (l : Fin (suc m))
          (R : Poly n (suc (suc m))) (α : Subset n) (t : Subset (suc m)) →
          (R /ʸ punchIn j l) (α , t) ≡
          head-part (frontᴾ (suc l) (frontᴾ j R))
            (α , lookup t (swapIdx j l) ∷ removeAt t (swapIdx j l))
/ʸ-onto j l R α t = front-front-onto j l R α inside t

-- ... the constant coefficients agree ...

/ʸ-1ᵐ : (j : Fin (suc (suc m))) (l : Fin (suc m))
        (R : Poly n (suc (suc m))) →
        head-part (frontᴾ (suc l) (frontᴾ j R)) 1ᵐ ≡ (R /ʸ punchIn j l) 1ᵐ
/ʸ-1ᵐ j l R = trans (/ʸ-front-front j l R ⊥ outside ⊥)
  (cong (λ t → (R /ʸ punchIn j l) (⊥ , t)) (insertAt-⊥ (swapIdx j l)))

-- ... and the coefficient of a path variable is that of the variable
-- the renumbering moves there.

/ʸ-⟪⟫ : (j : Fin (suc (suc m))) (l : Fin (suc m))
        (R : Poly n (suc (suc m))) (i : Fin (suc m)) →
        head-part (frontᴾ (suc l) (frontᴾ j R)) ⟪ y[ i ] ⟫ ≡
        (R /ʸ punchIn j l) ⟪ y[ moved (swapIdx j l) i ] ⟫
/ʸ-⟪⟫ j l R zero    = trans (/ʸ-front-front j l R ⊥ inside ⊥)
  (cong (λ t → (R /ʸ punchIn j l) (⊥ , t)) (insertAt-⊥-inside (swapIdx j l)))
/ʸ-⟪⟫ j l R (suc t) = trans (/ʸ-front-front j l R ⊥ outside ⁅ t ⁆)
  (cong (λ u → (R /ʸ punchIn j l) (⊥ , u)) (insertAt-⁅⁆ (swapIdx j l) t))

-- A quotient vanishing after two renumberings vanishes after one.

≈0-front-front : (c : ℤ) (j : Fin (suc (suc m))) (l : Fin (suc m))
                 (R : Poly n (suc (suc m))) →
                 head-part (frontᴾ (suc l) (frontᴾ j R)) ≈[ c ] 0ᴾ →
                 (R /ʸ punchIn j l) ≈[ c ] 0ᴾ
≈0-front-front c j l R eq (α , t) =
  subst (λ z → c ∣ (z - 0ℤ)) (sym (/ʸ-onto j l R α t))
    (eq (α , lookup t (swapIdx j l) ∷ removeAt t (swapIdx j l)))


------------------------------------------------------------------------
-- Occurrences of the moved variable

-- y_(punchIn j l) is absent from R when the head of the double
-- renumbering is absent from it.

NoVar-front-front : {c : ℤ} (j : Fin (suc (suc m))) (l : Fin (suc m))
                    (R : Poly n (suc (suc m))) →
                    NoVar c y[ zero ] (frontᴾ (suc l) (frontᴾ j R)) →
                    NoVar c y[ zero ] (frontᴾ (punchIn j l) R)
NoVar-front-front {c = c} j l R h (α , _ ∷ t) here =
  subst (c ∣_) (sym (front-front-onto j l R α inside t))
    (h (α , inside ∷ lookup t (swapIdx j l) ∷ removeAt t (swapIdx j l))
       here)

-- front zero lists the variables as they are.

NoVar-unfront-zero : {c : ℤ} (R : Poly n (suc m)) →
                     NoVar c y[ zero ] (frontᴾ zero R) →
                     NoVar c y[ zero ] R
NoVar-unfront-zero R h (α , _ ∷ s) here = h (α , inside ∷ s) here
