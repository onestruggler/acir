------------------------------------------------------------------------
-- Presentations of groups
--
-- The Simplified ≅ Derived group isomorphism for the extended gate set
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Construct.Composition
open import Algebra.Morphism.Structures using (IsGroupIsomorphism ; module GroupMorphisms)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Function using (_∘_ ; id)
open import Notations
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Zp.Fermats-little-theorem
open import Zp.ModularArithmetic

module Examples.Groups.Symplectic.Sim-Ext-Sym-Iso
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime hiding (act))
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where
open Primitive-Root-Modp' g* g-gen

private
  variable
    n : ℕ

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime as SD
-- Simplified.Syntactics re-exports `module Symplectic`, which line 37
-- already brings in.  The two are separate applications of the same
-- parameterised module, so having both in scope is ambiguous rather
-- than harmless; take Symplectic from the direct import only.
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  hiding (module Symplectic)
-- Symplectic-Sim-GroupLike, and the Iso theorems that used to be the
-- submodule Iso, moved out when Simplified.Syntactics was split up.
open import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.Simplified.Iso p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.Sim-Ext-Sym p-2 p-prime hiding (module G1 ; module G2)
open Simplified-Relations

open Symplectic  renaming (_QRel,_===_ to _QRel,_===₁_) using ()
open Sim         renaming (_QRel,_===_ to _QRel,_===₂_) using ()
open SymDerived  renaming (_QRel,_===_ to _QRel,_===₃_) using ()

open Symplectic-GroupLike         renaming (grouplike to grouplike₁) using ()
open Symplectic-Sim-GroupLike     renaming (grouplike to grouplike₂) using ()
open Symplectic-Derived-GroupLike renaming (grouplike to grouplike₃) using ()

open GroupMorphisms

Theorem-Sim-iso-Der : ∀ {n} ->
  let
  module G1 = Group-Lemmas (n QRel,_===₁_) grouplike₁
  module G2 = Group-Lemmas (n QRel,_===₂_) grouplike₂
  module G3 = Group-Lemmas (n QRel,_===₃_) grouplike₃
  in
  IsGroupIsomorphism (Group.rawGroup G2.•-ε-group) (Group.rawGroup G3.•-ε-group) ((f'* {n}) ∘ id)
Theorem-Sim-iso-Der {n} = isGroupIsomorphism PB.trans Theorem-Sym-iso-Sim' Theorem-Sym-iso-Ext
