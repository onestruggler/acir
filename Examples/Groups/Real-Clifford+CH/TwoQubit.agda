------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-qubit completeness (Clément, Section 7.2)
--
-- On two qubits the circuits denote all of O₄(ℤ[1/√2]) (Lemma 4.7), so
-- the auxiliary language is the whole of Section 4's: words over the
-- 1- and 2-level matrices on four basis vectors, with the theory of
-- Figure 7.  This module is the two-qubit instance of BackAndForth:
--
--   * the encoding E (Definition 7.2) on the six generators — a gate
--     on a wire is the product of its two-level copies over the other
--     wire's basis — and that it preserves the semantics, checked on
--     4 × 4 integer matrices;
--   * the decoding D (Definition 7.3), the paper's table of twenty-
--     eight circuits;
--   * Lemma 7.6, two-qubit completeness, from Theorem 4.4 and Lemmas
--     7.4 and 7.5.  Here they are module parameters; Lemmas 7.4 and
--     7.5 (Appendix C) are proved in TwoQubit.Decoding, which needs
--     the encoding and decoding below, and Theorem 4.4 is quoted by
--     the paper from the literature.
--
-- Basis vectors are indexed 0 … 3 as in the paper, k = 2 x₁ + x₀ with
-- x₁ the upper wire (the paper's first qubit) and x₀ the lower one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.TwoQubit where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])
import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth

------------------------------------------------------------------------
-- The basis, and the matrices of the auxiliary generators

-- The index k = 2 x₁ + x₀ as a bit vector, wire 0 first.
bits : Fin 4 → Bits 2
bits ₀ = false ∷ false ∷ []
bits ₁ = true  ∷ false ∷ []
bits ₂ = false ∷ true  ∷ []
bits ₃ = true  ∷ true  ∷ []

private
  eqᵇ : Bool → Bool → Bool
  eqᵇ true  true  = true
  eqᵇ false false = true
  eqᵇ _     _     = false

  eqB : Bits 2 → Bits 2 → Bool
  eqB (a ∷ b ∷ []) (c ∷ d ∷ []) = eqᵇ a c ∧ eqᵇ b d

  -- (−1)_[i]: the sign −1 on basis vector i.
  negOp : Bits 2 → Op 2
  negOp i x y = (if eqB x i then -1# else 1#) * δb x y

  -- X_[i,j]: the exchange of basis vectors i and j.
  swapOp : Bits 2 → Bits 2 → Op 2
  swapOp i j x y = δb (if eqB x i then j else if eqB x j then i else x) y

  -- √2 H_[i,j]: the Hadamard on the span of i and j (in that order),
  -- √2 times the identity elsewhere.
  hadOp : Bits 2 → Bits 2 → Op 2
  hadOp i j x y =
    if eqB x i then (if eqB y i then 1# else if eqB y j then 1# else 0#)
    else if eqB x j then (if eqB y i then 1# else if eqB y j then -1# else 0#)
    else √2 * δb x y

-- The generators' matrices over ℤ[1/√2]; H carries one power of 1/√2.
⟦_⟧ʸ : G.Gen 4 → Scaled 2
⟦ −1[ a ]    ⟧ʸ = 0 , negOp (bits a)
⟦ X[ a , b ] ⟧ʸ = 0 , swapOp (bits a) (bits b)
⟦ H[ a , b ] ⟧ʸ = 1 , hadOp (bits a) (bits b)

module BF = BackAndForth 2 (4 G.G,_===_) ⟦_⟧ʸ
open BF using (⟦_⟧Y)

------------------------------------------------------------------------
-- The encoding (Definition 7.2), on generators

e : Gen 2 → Word (G.Gen 4)
e (gate₀ ())
e H-gen        = G.H ₀ ₁ • G.H ₂ ₃
e Z-gen        = G.−1 ₁ • G.−1 ₃
e CZ-gen       = G.−1 ₃
e CH-gen       = G.H ₂ ₃
e (H-gen ↥)    = G.H ₀ ₂ • G.H ₁ ₃
e (Z-gen ↥)    = G.−1 ₂ • G.−1 ₃
e (gate₀ () ↥)
e (gate₀ () ↥ ↥)

------------------------------------------------------------------------
-- The decoding (Definition 7.3), on generators

d : G.Gen 4 → Circuit 2
-- (−1)_[k]: the phase −1 on |k⟩, a CZ with the controls negated where
-- k has a 0.
d −1[ ₀ ] = °CZ°
d −1[ ₁ ] = °CZ
d −1[ ₂ ] = CZ°
d −1[ ₃ ] = CZ
-- X_[a,b], symmetric in a and b.
d X[ ₂ , ₃ ] = CX
d X[ ₃ , ₂ ] = CX
d X[ ₀ , ₁ ] = °CX
d X[ ₁ , ₀ ] = °CX
d X[ ₀ , ₂ ] = XC°
d X[ ₂ , ₀ ] = XC°
d X[ ₁ , ₃ ] = XC
d X[ ₃ , ₁ ] = XC
d X[ ₁ , ₂ ] = Ex
d X[ ₂ , ₁ ] = Ex
d X[ ₀ , ₃ ] = Ex • X ↑ • X ↓
d X[ ₃ , ₀ ] = Ex • X ↑ • X ↓
d X[ ₀ , ₀ ] = ε
d X[ ₁ , ₁ ] = ε
d X[ ₂ , ₂ ] = ε
d X[ ₃ , ₃ ] = ε
-- H_[a,b].
d H[ ₂ , ₃ ] = CH
d H[ ₀ , ₁ ] = °CH
d H[ ₀ , ₂ ] = HC°
d H[ ₁ , ₃ ] = HC
d H[ ₃ , ₂ ] = X ↓ • CH • X ↓
d H[ ₁ , ₀ ] = X ↓ • °CH • X ↓
d H[ ₂ , ₀ ] = X ↑ • HC° • X ↑
d H[ ₃ , ₁ ] = X ↑ • HC • X ↑
d H[ ₂ , ₁ ] = XC • CH • XC
d H[ ₁ , ₂ ] = CX • HC • CX
d H[ ₀ , ₃ ] = XC • °CH • XC
d H[ ₃ , ₀ ] = X ↓ • (XC • CH • XC) • X ↓
d H[ ₀ , ₀ ] = ε
d H[ ₁ , ₁ ] = ε
d H[ ₂ , ₂ ] = ε
d H[ ₃ , ₃ ] = ε

------------------------------------------------------------------------
-- The encoding preserves the semantics
--
-- Both readings are stored as tries and compared by `refl`, scaled by
-- each other's power of √2 as in Interpretation.by-matrix.

-- The stored reading of an auxiliary word.
⟦_⟧YM : Word (G.Gen 4) → Mat 2
⟦ [ y ]ʷ ⟧YM = matOf (proj₂ ⟦ y ⟧ʸ)
⟦ ε ⟧YM      = idM
⟦ u • t ⟧YM  = mulM ⟦ u ⟧YM ⟦ t ⟧YM

private
  Y-ix : (u : Word (G.Gen 4)) → proj₂ ⟦ u ⟧Y ≐ ix ⟦ u ⟧YM
  Y-ix [ y ]ʷ  = ≐-sym (ix-matOf (proj₂ ⟦ y ⟧ʸ))
  Y-ix ε       = ≐-sym ix-id
  Y-ix (u • t) = ≐-trans (⊙-cong (Y-ix u) (Y-ix t)) (≐-sym (ix-mul ⟦ u ⟧YM ⟦ t ⟧YM))

  -- The encoding of a gate denotes the gate.
  by-tries : (g : Gen 2) →
             scaleM (√2^ len [ g ]ʷ) ⟦ e g ⟧YM ≡ scaleM (√2^ proj₁ ⟦ e g ⟧Y) ⟦ [ g ]ʷ ⟧M →
             ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
  by-tries g eq =
    ≐-trans (·-cong Eq.refl (Y-ix (e g)))
      (≐-trans (≐-sym (ix-scaleM _ _))
        (≐-trans (ix-≡ eq)
          (≐-trans (ix-scaleM _ _) (·-cong Eq.refl (≐-sym (⟦⟧-ix [ g ]ʷ))))))

-- Two auxiliary words with the same matrix, decided on tries (for the
-- soundness of Figure 7, Auxiliary.Soundness).
by-triesY : (u t : Word (G.Gen 4)) →
            scaleM (√2^ proj₁ ⟦ t ⟧Y) ⟦ u ⟧YM ≡ scaleM (√2^ proj₁ ⟦ u ⟧Y) ⟦ t ⟧YM →
            ⟦ u ⟧Y ~ ⟦ t ⟧Y
by-triesY u t eq =
  ≐-trans (·-cong Eq.refl (Y-ix u))
    (≐-trans (≐-sym (ix-scaleM _ _))
      (≐-trans (ix-≡ eq)
        (≐-trans (ix-scaleM _ _) (·-cong Eq.refl (≐-sym (Y-ix t))))))

e-sem : (g : Gen 2) → ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
e-sem (gate₀ ())
e-sem H-gen        = by-tries H-gen     Eq.refl
e-sem Z-gen        = by-tries Z-gen     Eq.refl
e-sem CZ-gen       = by-tries CZ-gen    Eq.refl
e-sem CH-gen       = by-tries CH-gen    Eq.refl
e-sem (H-gen ↥)    = by-tries (H-gen ↥) Eq.refl
e-sem (Z-gen ↥)    = by-tries (Z-gen ↥) Eq.refl
e-sem (gate₀ () ↥)
e-sem (gate₀ () ↥ ↥)

------------------------------------------------------------------------
-- Two-qubit completeness (Lemma 7.6)
--
-- From the completeness of Figure 7 for the matrix group (Theorem 4.4,
-- [Fang, Heunen and Kaarsgaard]) and the two lemmas of Appendix C:
-- the decoding respects Figure 7 (Lemma 7.5) and inverts the encoding
-- (Lemma 7.4, here on the generators, since circuits are words).

open PB (4 G.G,_===_) using () renaming (_≈_ to _≈G_)

module Lemma-7-6
  (theorem-4-4 : ∀ {u t : Word (G.Gen 4)} → ⟦ u ⟧Y ~ ⟦ t ⟧Y → u ≈G t)
  (lemma-7-4   : ∀ g → 2 ⊢ [ g ]ʷ ≈ (d ʷ) (e g))
  (lemma-7-5   : ∀ {u t} → 4 G.G, u === t → 2 ⊢ (d ʷ) u ≈ (d ʷ) t)
  where

  open BF.Complete theorem-4-4 e e-sem d lemma-7-5 lemma-7-4 public
    using (complete)
