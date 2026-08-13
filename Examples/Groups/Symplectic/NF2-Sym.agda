{-# OPTIONS --cubical-compatible --safe #-}


open import Data.Product using (_×_ ; _,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)


open import Word.Base as WB hiding (wfoldl)
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Nat.Primality


open import ForStdlib.Data.Fin.Mod

module Examples.Groups.Symplectic.NF2-Sym
 (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where
open PrimeModulus p-2 p-prime


open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime

module LM2 where

  private
    variable
      n : ℕ

  open import Examples.Groups.Symplectic.Cosets p-2 p-prime
  
  ⟦_⟧ₚ : Postfix → Word (Gen (₂₊ n))
  ⟦ s , mc2 , mc1 ⟧ₚ = S^ s • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊
  
  ⟦_⟧₂ : Cosets2 → Word (Gen (₂₊ n))
  ⟦ case-||ₐ k p ⟧₂ = CZ^ k • ⟦ p ⟧ₚ
  ⟦ case-|| (k , _) l p ⟧₂ = CZ^ k • H^ ₃ ↑ • S^ l ↑ • ⟦ p ⟧ₚ
  ⟦ case-Ex-| nf1 mc ⟧₂ = Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊
  ⟦ case-| mc nf1 ⟧₂ = CZ • ⟦ mc ⟧ₘ₊ ↑ • ⟦ nf1 ⟧₁
  ⟦ case-nf1 nf1 ⟧₂ = ⟦ nf1 ⟧₁
  ⟦ case-Ex-nf1 nf1 ⟧₂ = Ex • ⟦ nf1 ⟧₁ ↑
