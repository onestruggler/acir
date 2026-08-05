{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base
import Circuit.Base as CB
open import Notations

module Circuit.CosetNF
  (C : ℕ -> Set)
  (I : ∀ {n} -> C n)
  (Gate : ℕ -> Set)
  (let open CB Gate)
  ([_]ᶜ : ∀ {n} -> C n -> Circuit (₁₊ n))
  where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)


NF : ℕ -> Set
NF ₀ = ⊤
NF (₁₊ n) = NF n × C n

[_] : ∀ {n} -> NF n -> Circuit n
[_] {₀} tt = ε
[_] {₁₊ n} (nf , c) = [ nf ] ↑ • [ c ]ᶜ

inv-nf = [_]

module Normalize 
  (push : ∀ {n} -> C n -> Gen (₁₊ n) -> Circuit n × C n)
  where

  [_]⁻¹ : ∀ {n} -> Circuit n -> NF n
  [_]⁻¹ {₀} cir = tt
  [_]⁻¹ {₁₊ n} cir = [ dir ]⁻¹ , c'
    where
    ph = (push ᵗ) I cir
    dir = ph  .proj₁
    c' = ph  .proj₂

  nf = [_]⁻¹
