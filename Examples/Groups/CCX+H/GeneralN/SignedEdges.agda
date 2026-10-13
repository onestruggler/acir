------------------------------------------------------------------------
-- Presentations of groups
--
-- Explicit normalization of every signed factor in the four-state
-- decoder.  The target alphabet consists of sign pairs and double
-- exchanges.  Repeated or overlapping indices need no separate cases.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; s≤s ; z≤n)

module Examples.Groups.CCX+H.GeneralN.SignedEdges (N : ℕ) where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Product.Base using (_,_)
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
import Examples.Groups.CCX+HH.Subgroup.Presentation as Sub
open import Examples.Groups.CCX+HH.Subgroup.Action
  using (Coset ; c00 ; c10 ; c11 ; c01 ; dyadic-step)
import Examples.Groups.CCX+H.GeneralN.SignedNormalization as Normal
open import Presentation.Base (U._===_ {2 + N}) hiding (_===_)
open import Presentation.Properties (U._===_ {2 + N}) using (by-assoc)

private
  module P = Sub N
  open P using (rep)
  open D using (_⁻¹)
  open Normal using (swap)

data Atom : Set where
  MM : (a b : Fin (2 + N)) → Atom
  XX : (a b c d : Fin (2 + N)) → .(a < b) → .(c < d) → Atom

e : Atom → Word (U.Gen (2 + N))
e (MM a b) = U.M a • U.M b
e (XX a b c d ab cd) = U.X a b ab • U.X c d cd

decode : Word Atom → Word (U.Gen (2 + N))
decode = e ʷ

record Decoded (w : Word (U.Gen (2 + N))) : Set where
  constructor normal
  field
    atoms : Word Atom
    correct : w ≈ decode atoms

private
  i j : Fin (2 + N)
  i = zero
  j = suc zero
  ij : i < j
  ij = s≤s z≤n
  σ : Fin (2 + N) → Fin (2 + N)
  σ = swap i j
  module II = Normal.Pair i j i j ij ij

sign-edge : ∀ q a → Decoded (P.e (q , U.M-gen a))
sign-edge c00 a = normal [ MM a i ]ʷ (by-assoc Eq.refl)
sign-edge c10 a = normal [ MM i a ]ʷ (by-assoc Eq.refl)
sign-edge c11 a = normal
  ([ MM (σ a) (σ (σ i)) ]ʷ • [ XX i j i j ij ij ]ʷ)
  (II.XMXM a i)
sign-edge c01 a = normal
  ([ MM i (σ a) ]ʷ • [ XX i j i j ij ij ]ʷ)
  (trans (by-assoc Eq.refl) (II.MXMX i a))

exchange-edge : ∀ q a b .(ab : a < b) → Decoded (P.e (q , U.X-gen a b ab))
exchange-edge c00 a b ab = normal [ XX a b i j ab ij ]ʷ (by-assoc Eq.refl)
exchange-edge c10 a b ab = normal
  ([ MM i (swap a b (σ i)) ]ʷ • [ XX a b i j ab ij ]ʷ)
  (trans (by-assoc Eq.refl) (Normal.Pair.MXXM a b i j ab ij i i))
exchange-edge c11 a b ab = normal [ XX i j a b ij ab ]ʷ (by-assoc Eq.refl)
exchange-edge c01 a b ab = normal
  ([ MM i (σ (swap a b i)) ]ʷ • [ XX i j a b ij ab ]ʷ)
  (trans (by-assoc Eq.refl) (Normal.Pair.MXXM i j a b ij ab i i))

-- These are definitionally the T and S words of DyadicSchreier.Block;
-- their normalization does not use that block's disjointness premises.
module KFactors
  (a b c d e f : Fin (2 + N))
  .(ab : a < b) .(bc : b < c) .(cd : c < d) .(ef : e < f) where

  private
    K = U.K-gen a b c d ab bc cd
    A = U.M a • U.X b c bc
    R : Coset → Word (U.Gen (2 + N))
    R q = rep (dyadic-step q K) ⁻¹
    Z : Coset → Word (U.Gen (2 + N))
    Z c00 = U.M e • U.X e f ef
    Z c10 = U.X e f ef
    Z c11 = U.M e
    Z c01 = ε
    τ = swap b c
    ρ = swap e f
    module BI = Normal.Pair b c i j bc ij
    module IB = Normal.Pair i j b c ij bc
    module EI = Normal.Pair e f i j ef ij

  T S : Coset → Word (U.Gen (2 + N))
  T q = (rep q • A ⁻¹) • R q
  S q = Z q • R q

  normalize-T : ∀ q → Decoded (T q)
  normalize-T c00 = normal
    ([ MM (τ a) (τ (σ i)) ]ʷ • [ XX b c i j bc ij ]ʷ)
    (trans (by-assoc Eq.refl) (BI.XMXM a i))
  normalize-T c10 = normal
    ([ MM i (τ a) ]ʷ • [ XX b c i j bc ij ]ʷ)
    (trans (by-assoc Eq.refl) (BI.MXMX i a))
  normalize-T c11 = normal
    ([ MM (σ (τ a)) (σ (τ i)) ]ʷ • [ XX i j b c ij bc ]ʷ)
    (trans (by-assoc Eq.refl) (IB.XXMM a i))
  normalize-T c01 = normal
    ([ MM i (σ (τ a)) ]ʷ • [ XX i j b c ij bc ]ʷ)
    (trans (by-assoc Eq.refl) (IB.MXXM i a))

  normalize-S : ∀ q → Decoded (S q)
  normalize-S c00 = normal
    ([ MM e (ρ (σ i)) ]ʷ • [ XX e f i j ef ij ]ʷ)
    (trans (by-assoc Eq.refl) (EI.MXXM e i))
  normalize-S c10 = normal [ XX e f i j ef ij ]ʷ refl
  normalize-S c11 = normal [ MM e i ]ʷ refl
  normalize-S c01 = normal ε left-unit
