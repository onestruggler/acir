{-# OPTIONS --cubical-compatible --safe #-}




open import Data.Product using (_×_ ; _,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)


open import Word.Base
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Nat.Primality
open import Notations

open import ForStdlib.Data.Fin.Mod
module Examples.Groups.Symplectic.NF1-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime

open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open Lemmas-2Q 2 hiding (lemma-CZ^k-%)
open Symplectic


private
  variable
    n : ℕ

open import Examples.Groups.Symplectic.Cosets p-2 p-prime

⟦_⟧ₕₛ : Cosets1 → Word (Gen (₁₊ n))
⟦ ε ⟧ₕₛ = ε
⟦ HS^ x ⟧ₕₛ = H • S^ x

⟦_⟧'ₕₛ : Cosets1-noε → Word (Gen (₁₊ n))
⟦ HS^ x ⟧'ₕₛ = H • S^ x

⟦_⟧ₛ : SPowers → Word (Gen (₁₊ n))
⟦ x ⟧ₛ = S^ x

⟦_⟧ₘ : ZMultiplier → Word (Gen (₁₊ n))
⟦ x ⟧ₘ = M x

⟦_⟧ₘ₊ : MC → Word (Gen (₁₊ n))
⟦ m , c ⟧ₘ₊ = ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ

⟦_⟧ₘₕₛ : MC → Word (Gen (₁₊ n))
⟦ m , c ⟧ₘₕₛ = ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ

⟦_⟧₁ : NF1 → Word (Gen (₁₊ n))
⟦ s , m , c ⟧₁ =  ⟦ s ⟧ₛ • ⟦ m ⟧ₘ • ⟦ c ⟧ₕₛ
