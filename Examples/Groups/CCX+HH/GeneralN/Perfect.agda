------------------------------------------------------------------------
-- Presentations of groups
--
-- At every width at least four the physical HH circuit group is
-- perfect: its universal commutative quotient is trivial.  The base
-- uses explicit commutators; the induction only adds idle wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.Perfect where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
import Presentation.Base as PB
import Examples.Groups.CCX+HH.Abelianization as Abel
import Examples.Groups.CCX+HH.GeneralN.Commutators as W

generator : ∀ n (g : Gen (4 + n)) → Abel.At._≈_ (4 + n) [ g ]ʷ ε
generator n g = PB.trans
  (PB.sym (Abel.At.source-cong (4 + n) (W.Witness.correct w)))
  (Abel.At.involution-commutator (4 + n) (W.Witness.first w) (W.Witness.second w)
    (W.Witness.first-involutive w) (W.Witness.second-involutive w))
  where w = W.witness n g

abelian-trivial : ∀ n (w : Circuit (4 + n)) → Abel.At._≈_ (4 + n) w ε
abelian-trivial n [ g ]ʷ = generator n g
abelian-trivial n ε = PB.refl
abelian-trivial n (u • v) = PB.trans
  (PB.cong (abelian-trivial n u) (abelian-trivial n v)) PB.left-unit

abelian-equal : ∀ n (u v : Circuit (4 + n)) → Abel.At._≈_ (4 + n) u v
abelian-equal n u v = PB.trans (abelian-trivial n u)
  (PB.sym (abelian-trivial n v))
