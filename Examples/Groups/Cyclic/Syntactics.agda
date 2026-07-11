------------------------------------------------------------------------
-- Presentations of groups
--
-- Cyclic groups Z/NZ and their normal form
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Cyclic.Syntactics where

open import Data.Fin using (zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]')

open import Notations

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike)
import Normalization.NormalForm.Propositional as NFBase
open NFBase using (NormalFormInjective ; NormalForm)
open import Word.Base hiding (wfoldl)

------------------------------------------------------------------------
-- Generators and relation

-- The generating set is a singleton: the only generator is tt.
X = ⊤

-- The word consisting of the single generator.
T : Word X
T = [ tt ]ʷ

-- There is only one relation for a cyclic group: the generator has
-- order N. rel is indexed by the order of the cyclic group.
infix 4 _Cn,_===_
data _Cn,_===_ (N : ℕ) : WRel X where
  order : N Cn, T ^' N === ε

------------------------------------------------------------------------
-- The presentation is group-like (for a nonzero order)

-- Appending one more generator: Tᵏ • T ≈ Tᵏ⁺¹.  Holds for any relation,
-- using only the left-unit law (k = 0) and the definition of _^'_.
pow-suc : ∀ (Γ : WRel X) k → PB._≈_ Γ ((T ^' k) • T) (T ^' suc k)
pow-suc Γ zero    = PB.left-unit
pow-suc Γ (suc k) = PB.refl

-- Every generator (there is only tt) has the left inverse Tᴺ: the order
-- relation T^(1+N) ≈ ε makes Tᴺ • T ≈ ε.  This fails at order 0 (the
-- free monoid ℕ), so the order is taken to be positive.
grouplike : ∀ N → Grouplike (suc N Cn,_===_)
grouplike N tt =
  T ^' N , PB.trans (pow-suc (suc N Cn,_===_) N) (PB.axiom order)

