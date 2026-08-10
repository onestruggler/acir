{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Product using (_,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Vec hiding ([_])

open import Word.Base hiding (wfoldl)
open import Notations
open import Presentation.GroupLike
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.Semantics.Action (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where


open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open Symplectic-Derived-Gen
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime

-- The action of a single generator on a Pauli, and its extension to
-- circuit words (act = word-act act1).

act1 : ∀ {n} → Gen n → Pauli n → Pauli n
act1 {₁₊ n} (gate₁ (H-gen ₀)) ((a , b) ∷ ps) = ((a , b) ∷ ps)
act1 {₁₊ n} (gate₁ (H-gen ₁)) ((a , b) ∷ ps) = ((- b , a) ∷ ps)
act1 {₁₊ n} (gate₁ (H-gen ₂)) ((a , b) ∷ ps) = ((- a , - b) ∷ ps)
act1 {₁₊ n} (gate₁ (H-gen ₃)) ((a , b) ∷ ps) = ((b , - a) ∷ ps)
act1 {₁₊ n} (gate₁ (S-gen k)) ((a , b) ∷ ps) = ((a , b + a * k) ∷ ps)
act1 {₂₊ n} (gate₂ (CZ-gen k)) ((a , b) ∷ (a' , b') ∷ ps) = (a , b + a' * k) ∷ (a' , b' + a * k) ∷ ps
act1 {₁₊ n} (g ↥) (p ∷ ps) = p ∷ act1 {n} g ps

act : ∀ {n} → Word (Gen n) → Pauli n → Pauli n
act {n} = word-act act1
-- act {n} ε p = p
-- act {n} (w • w₁) p = act w (act w₁ p)
