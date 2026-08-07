
{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Nat.Primality using (Prime)

open import Notations
open import Word.Base

module Examples.Groups.Symplectic.NewCosets (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime using (ML) public
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime using ([_]ᵐˡ) public

