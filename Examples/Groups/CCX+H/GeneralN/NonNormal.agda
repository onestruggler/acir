------------------------------------------------------------------------
-- Presentations of groups
--
-- The physical H image is a non-normal subgroup of the scaled ambient
-- two-level group when the circuit width is at least four.  The global
-- IH is realizable, while conjugating it by one basis-state sign is
-- not: its four-state action sends 00 to 01.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.NonNormal (n : ℕ) where

open import Data.Nat.Base using (_*_ ; _<_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin ; fromℕ<)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_ ; ε)
import Presentation.Base as PB
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Physical
import Examples.Groups.CCX+H.GeneralN.Generation as Generation
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.CCX+H.GeneralN.Action using (c00 ; c01)

width = 4 + n
k = 2 ^ℕ (3 + n)
N = k * 2
module C = Sem.At (3 + n)
module M = S.Dim k
module G = Generation n

private
  dimension : 2 ^ℕ width ≡ N
  dimension = NP.*-comm 2 k

  first : Fin N
  first = fromℕ< (Eq.subst (0 <_) dimension (NP.m^n>0 2 width))

sign : Word (T.Genᴸ N)
sign = T.Mᴸ first

sign-involutive : PB._≈_ T._===ᴸ_ (sign • sign) ε
sign-involutive = PB.axiom (T.table1 U.r1b)

-- The middle word lies in the physical image.
hadamard-generated : Σ (H.Circuit width) λ c → C.interpret c ≡ M.⟦ T.H ⟧ᴸ
hadamard-generated = G.generated T.H Eq.refl

conjugate : Word (T.Genᴸ N)
conjugate = sign • T.H • sign

conjugate-state : G.Auxiliary.state c00 conjugate ≡ c01
conjugate-state = Eq.refl

private
  distinct : c01 ≡ c00 → ⊥
  distinct ()

not-generated : ∀ (c : H.Circuit width) → C.interpret c ≡ M.⟦ conjugate ⟧ᴸ → ⊥
not-generated c eq = distinct (G.necessary conjugate c eq)

-- The same exclusion for ordinary 2^width by 2^width gate matrices.
not-generated-physical : ∀ (c : H.Circuit width) →
  Physical.interpret c ≡ Physical.cast-matrix (Eq.sym dimension) M.⟦ conjugate ⟧ᴸ → ⊥
not-generated-physical c eq = distinct (G.physical-necessary conjugate c eq)
