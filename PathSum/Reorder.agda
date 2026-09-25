------------------------------------------------------------------------
-- Presentations of groups
--
-- Moving a path variable to the front
--
-- Figure 2 of Amy's paper (QPL 2018) states every rule at a path
-- variable y₀, which "is an internal path variable": any of them, not
-- the first.  PathSum.Reduction states the rules at the first
-- variable only.  This module supplies the renumbering that
-- transports a rule from the first variable to y_j: front j moves y_j
-- to position 0 and keeps the other variables in their original
-- order, so that position 0 of the new numbering is the old j and
-- position suc l is the old punchIn j l.
--
-- The renumbering acts on three things, each defined by recursion on
-- j so that the proofs below are inductions on j in lockstep:
--
--  * assignments: insertᵃ j c g is the assignment that gives y_j the
--    value c and the other variables, in order, the values of g (the
--    analogue of Vec.insertAt); unfront j y′ reads back the original
--    assignment from one to the renumbered variables;
--  * monomials, through Vec.insertAt: the renumbered monomial b ∷ s
--    is the original insertAt s j b;
--  * polynomials and path-sums: frontᴾ and front.
--
-- The quotient of a polynomial by y_j and the part free of y_j are
-- then the head and tail parts of the renumbered polynomial, and live
-- over the remaining variables in their original order (_/ʸ_, _∖ʸ_).
-- eval-front says that renumbering commutes with evaluation.
-- Renumbering also keeps the degree of every monomial (∣insertAt∣),
-- and a variable absent from a polynomial stays absent once it and
-- the others are renumbered (NoVar-front, NoVar-front-suc), so a
-- path-sum all of whose path variables are internal keeps that
-- property (Internal-front).  Nothing here depends on M or on the
-- semantics; that front preserves the denotation is
-- PathSum.Anywhere.Sound.front-≋.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Reorder where

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Subset using (Subset; Side; inside; outside; ∣_∣)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([]; _∷_; insertAt; here; there)
open import Data.Vec.Properties using
  (insertAt-lookup; insertAt-punchIn; []=⇒lookup; lookup⇒[]=)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Base
open import PathSum.Polynomial
open import PathSum.Polynomial.Properties using
  (Σsub-cong; Σsub-+; Σsub-splitAt)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Assignments

-- insertᵃ j c g gives position j the value c and the remaining
-- positions, in order, the values of g.

insertᵃ : Fin (suc m) → Bool → (Fin m → Bool) → Fin (suc m) → Bool
insertᵃ         zero    c g zero    = c
insertᵃ         zero    c g (suc i) = g i
insertᵃ {zero}  (suc ()) c g i
insertᵃ {suc m} (suc j) c g zero    = g zero
insertᵃ {suc m} (suc j) c g (suc i) = insertᵃ j c (λ l → g (suc l)) i

insertᵃ-here : (j : Fin (suc m)) (c : Bool) (g : Fin m → Bool) →
               insertᵃ j c g j ≡ c
insertᵃ-here         zero    c g = refl
insertᵃ-here {zero}  (suc ()) c g
insertᵃ-here {suc m} (suc j) c g = insertᵃ-here j c (λ l → g (suc l))

insertᵃ-punchIn : (j : Fin (suc m)) (c : Bool) (g : Fin m → Bool)
                  (i : Fin m) → insertᵃ j c g (punchIn j i) ≡ g i
insertᵃ-punchIn zero    c g i       = refl
insertᵃ-punchIn (suc j) c g zero    = refl
insertᵃ-punchIn (suc j) c g (suc i) =
  insertᵃ-punchIn j c (λ l → g (suc l)) i

-- The assignment to the original variables that an assignment to the
-- renumbered ones stands for: new 0 is old j, new suc l is old
-- punchIn j l.

unfront : Fin (suc m) → (Fin (suc m) → Bool) → Fin (suc m) → Bool
unfront j y′ = insertᵃ j (y′ zero) (λ i → y′ (suc i))


------------------------------------------------------------------------
-- Polynomials and path-sums

-- The coefficient of the renumbered monomial b ∷ s is that of the
-- original monomial insertAt s j b.

frontᴾ : Fin (suc m) → Poly n (suc m) → Poly n (suc m)
frontᴾ j P (α , b ∷ s) = P (α , insertAt s j b)

front : Fin (suc m) → PathSum n k (suc m) → PathSum n k (suc m)
front j ξ = ⟨ frontᴾ j (phase ξ) , (λ w → frontᴾ j (out ξ w)) ⟩

-- The quotient by y_j and the part free of y_j, over the remaining
-- variables in their original order: P = y_j · (P /ʸ j) + P ∖ʸ j.

infix 8 _/ʸ_ _∖ʸ_

_/ʸ_ : Poly n (suc m) → Fin (suc m) → Poly n m
P /ʸ j = head-part (frontᴾ j P)

_∖ʸ_ : Poly n (suc m) → Fin (suc m) → Poly n m
P ∖ʸ j = tail-part (frontᴾ j P)

-- Renumbering is a bijection, so it cannot be a rewrite rule of its
-- own: on two path variables, moving the second to the front twice
-- gives back the original polynomial.

frontᴾ-swap : (P : Poly n 2) (α : Subset n) (a b : Side) →
              frontᴾ (suc zero) (frontᴾ (suc zero) P) (α , a ∷ b ∷ []) ≡
              P (α , a ∷ b ∷ [])
frontᴾ-swap P α a b = refl


------------------------------------------------------------------------
-- Satisfaction and evaluation

-- A monomial containing y_j is satisfied when y_j is and the rest of
-- it is; one not containing it ignores y_j.

private
  ∧-mid : ∀ b p q → b ∧ (p ∧ q) ≡ p ∧ (b ∧ q)
  ∧-mid true  p q = refl
  ∧-mid false p q = sym (∧-zeroʳ p)

sat-insertᵃ-in : (s : Subset m) (j : Fin (suc m)) (c : Bool)
                 (g : Fin m → Bool) →
                 sat (insertAt s j inside) (insertᵃ j c g) ≡ c ∧ sat s g
sat-insertᵃ-in s             zero    c g = refl
sat-insertᵃ-in (inside  ∷ s) (suc j) c g = trans
  (cong (g zero ∧_) (sat-insertᵃ-in s j c (λ l → g (suc l))))
  (∧-mid (g zero) c (sat s (λ l → g (suc l))))
sat-insertᵃ-in (outside ∷ s) (suc j) c g =
  sat-insertᵃ-in s j c (λ l → g (suc l))

sat-insertᵃ-out : (s : Subset m) (j : Fin (suc m)) (c : Bool)
                  (g : Fin m → Bool) →
                  sat (insertAt s j outside) (insertᵃ j c g) ≡ sat s g
sat-insertᵃ-out s             zero    c g = refl
sat-insertᵃ-out (inside  ∷ s) (suc j) c g =
  cong (g zero ∧_) (sat-insertᵃ-out s j c (λ l → g (suc l)))
sat-insertᵃ-out (outside ∷ s) (suc j) c g =
  sat-insertᵃ-out s j c (λ l → g (suc l))

-- Renumbering commutes with evaluation.  The sum over the renumbered
-- path monomials splits, by definition, at the head; the sum over the
-- original ones is split at j (Σsub-splitAt), and the two halves
-- agree term by term.

eval-front : (j : Fin (suc m)) (P : Poly n (suc m)) (x : Fin n → Bool)
             (y′ : Fin (suc m) → Bool) →
             eval (frontᴾ j P) x y′ ≡ eval P x (unfront j y′)
eval-front {m = m} {n = n} j P x y′ = Σsub-cong per
  where
  t : Fin m → Bool
  t i = y′ (suc i)

  F : Subset n → Subset (suc m) → ℤ
  F α β = if sat α x ∧ sat β (unfront j y′) then P (α , β) else 0ℤ

  -- The summands of the two halves, as the renumbered sum has them.
  Fᵢ Fₒ : Subset n → Subset m → ℤ
  Fᵢ α s = if sat α x ∧ (y′ zero ∧ sat s t)
             then P (α , insertAt s j inside) else 0ℤ
  Fₒ α s = if sat α x ∧ sat s t
              then P (α , insertAt s j outside) else 0ℤ

  half-in : ∀ α s → F α (insertAt s j inside) ≡ Fᵢ α s
  half-in α s =
    cong (λ b → if sat α x ∧ b then P (α , insertAt s j inside) else 0ℤ)
         (sat-insertᵃ-in s j (y′ zero) t)

  half-out : ∀ α s → F α (insertAt s j outside) ≡ Fₒ α s
  half-out α s =
    cong (λ b → if sat α x ∧ b then P (α , insertAt s j outside) else 0ℤ)
         (sat-insertᵃ-out s j (y′ zero) t)

  per : ∀ α → Σsub (λ s → Fᵢ α s) + Σsub (λ s → Fₒ α s) ≡ Σsub (F α)
  per α = sym (trans (Σsub-splitAt j (F α))
    (trans (Σsub-+ (λ s → F α (insertAt s j inside))
                   (λ s → F α (insertAt s j outside)))
           (cong₂ _+_ (Σsub-cong (half-in α)) (Σsub-cong (half-out α)))))


------------------------------------------------------------------------
-- Occurrences of the moved variable

-- A variable absent from P is, once moved to the front, absent from
-- the renumbered polynomial at position 0.

NoVar-front : {c : ℤ} (j : Fin (suc m)) (P : Poly n (suc m)) →
              NoVar c y[ j ] P → NoVar c y[ zero ] (frontᴾ j P)
NoVar-front j P h (α , _ ∷ s) here = h (α , insertAt s j inside)
  (lookup⇒[]= j (insertAt s j inside) (insertAt-lookup s j inside))

-- The other variables keep their relative order: the renumbered
-- variable suc i is the original punchIn j i.

NoVar-front-suc : {c : ℤ} (j : Fin (suc m)) (i : Fin m)
                  (P : Poly n (suc m)) →
                  NoVar c y[ punchIn j i ] P →
                  NoVar c y[ suc i ] (frontᴾ j P)
NoVar-front-suc j i P h (α , b ∷ s) (there i∈s) = h (α , insertAt s j b)
  (lookup⇒[]= (punchIn j i) (insertAt s j b)
    (trans (insertAt-punchIn s j b i) ([]=⇒lookup i∈s)))

-- Hence renumbering keeps every path variable internal.

Internal-front : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) →
                 Internal ξ → Internal (front j ξ)
Internal-front j ξ int zero    w = NoVar-front j (out ξ w) (int j w)
Internal-front j ξ int (suc i) w =
  NoVar-front-suc j i (out ξ w) (int (punchIn j i) w)


------------------------------------------------------------------------
-- Degrees

-- Renumbering permutes the variables of a monomial, so it keeps its
-- degree; this is what makes the order of a polynomial invariant
-- (PathSum.Anywhere.Ord≤-front).

∣insertAt∣ : (s : Subset m) (j : Fin (suc m)) (b : Side) →
             ∣ insertAt s j b ∣ ≡ ∣ b ∷ s ∣
∣insertAt∣ s             zero    b       = refl
∣insertAt∣ (inside  ∷ s) (suc j) inside  = cong suc (∣insertAt∣ s j inside)
∣insertAt∣ (inside  ∷ s) (suc j) outside = cong suc (∣insertAt∣ s j outside)
∣insertAt∣ (outside ∷ s) (suc j) b       = ∣insertAt∣ s j b
