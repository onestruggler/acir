------------------------------------------------------------------------
-- Presentations of groups
--
-- The Symplectic ≅ Symplectic-Derived-Gen (extended gate set) group
-- isomorphism.  (Moved out of ExtendedGate.Iso-Sym-Derived.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
{-# OPTIONS --termination-depth=2 #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Sim-Ext-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic ; module Symplectic-GroupLike)
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime as SD using ()
open import Examples.Groups.Symplectic.ExtendedGate.Iso-Sym-Derived p-2 p-prime public

open Symplectic                  renaming (_QRel,_===_ to _QRel,_===₁_) using ()
open Symplectic-GroupLike        renaming (grouplike to grouplike₁)     using ()
open SD.Symplectic-Derived-Gen      renaming (_QRel,_===_ to _QRel,_===₂_) using ()
open SD.Symplectic-Derived-GroupLike renaming (grouplike to grouplike₂)  using ()

open GroupMorphisms

private
  variable
    n : ℕ

Theorem-Sym-iso-Ext :
  IsGroupIsomorphism (Group.rawGroup (G1.•-ε-group {n})) (Group.rawGroup (G2.•-ε-group {n})) (f'* {n})
Theorem-Sym-iso-Ext {n} =
  StarGroupIsomorphism.isGroupIsomorphism f' g f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen
  where
  open import Presentation.Morphism ((n) QRel,_===₁_) ((n) QRel,_===₂_)
  open GroupMorphism (grouplike₁ {n}) (grouplike₂ {n})
