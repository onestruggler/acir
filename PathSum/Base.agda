------------------------------------------------------------------------
-- Presentations of groups
--
-- Path-sums (Amy, QPL 2018, definition 2.1)
--
-- A path-sum on n qubits with m path variables is the map
--
--    |x⟩ ↦ 1/√2^m Σ_{y ∈ Z₂^m} e^{2πi P(x,y)} |f (x , y)⟩
--
-- and is presented here by its phase polynomial P together with its
-- output polynomials f, one for each output wire.  The analytic
-- content -- the associated operator -- is not formalised; it enters
-- only through the interface of PathSum.Semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Base where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_; there)

open import PathSum.Polynomial

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Path-sums

-- k is the exponent of the normalisation 1/√2^k and m the number of
-- path variables.  Definition 2.1 takes k to be m, but the rules of
-- figure 2 do not preserve that: [HH] removes a path variable and
-- leaves the normalisation alone, and [Elim] removes one path
-- variable but two units of normalisation.  The two indices are
-- therefore kept apart.

record PathSum (n k m : ℕ) : Set where
  constructor ⟨_,_⟩
  field
    phase : Poly n m
    -- The output polynomials, whose coefficients are read modulo 2.
    out   : Fin n → Poly n m

open PathSum public

-- The identity path-sum |x⟩ ↦ |x⟩.

idPS : PathSum n 0 0
idPS = ⟨ 0ᴾ , (λ i → μ x[ i ]) ⟩


------------------------------------------------------------------------
-- The distinguished path variable y₀

-- Every rule of figure 2 eliminates the first path variable, which
-- the paper calls y₀.

y₀ : Var n (suc m)
y₀ = y[ zero ]

-- P = y₀ · head-part P + tail-part P, definitionally.

head-part : Poly n (suc m) → Poly n m
head-part P (α , β) = P (α , inside ∷ β)

tail-part : Poly n (suc m) → Poly n m
tail-part P (α , β) = P (α , outside ∷ β)


------------------------------------------------------------------------
-- Internal path variables

-- A path variable is internal when it does not occur in the outputs;
-- ξ has only internal path variables when this holds of all of them.

Internal : PathSum n k m → Set
Internal {n} {m = m} ξ = ∀ (j : Fin m) (w : Fin n) → NoVar (+ 2) y[ j ] (out ξ w)

-- Dropping y₀ from the outputs of a path-sum all of whose path
-- variables are internal leaves them internal.

tail-Internal : (ξ : PathSum n k (suc m)) → Internal ξ →
                ∀ (j : Fin m) (w : Fin n) →
                NoVar (+ 2) y[ j ] (λ γ → tail-part (out ξ w) γ)
tail-Internal ξ int j w (α , β) j∈β =
  int (suc j) w (α , outside ∷ β) (there j∈β)
