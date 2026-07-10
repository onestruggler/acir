{-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=4 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; module ≡-Reasoning ; _≗_)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Function using (id)

open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)
open import Data.Fin using (toℕ)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations

open import Presentation.GroupLike
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Pushing.DHa0 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Ex-Sym2n p-2 p-prime using (lemma-comm-Ex-H-n)
open import Algebra.Properties.Ring (+-*-ring p-2)

------------------------------------------------------------------------
-- The a = 0 rows of the D-box H-push:
--
--   [ (0 , b) ]ᵈ • H  ≈  dir ↑ • [ d' ]ᵈ
--
--   b = 0 : dir = H,  d' = (0 , 0)   (H just hops over the swap Ex)
--   b ≠ 0 : dir = ε,  d' = (b , 0)   ([ (b,0) ]ᵈ = Ex·CZ^(-b)·H already)

dir-of-DHa0 : D -> Word (Gen (₁₊ n))
dir-of-DHa0 (₀ , ₀) = H
dir-of-DHa0 (₀ , ₁₊ _) = ε
dir-of-DHa0 (₁₊ _ , _) = ε   -- unused here; keeps the map total

d-of-DHa0 : D -> D
d-of-DHa0 (₀ , ₀) = ₀ , ₀
d-of-DHa0 (₀ , b@(₁₊ _)) = b , ₀
d-of-DHa0 (a@(₁₊ _) , b) = a , b   -- unused here

aux-DHa0 : let open PB ((₂₊ n) QRel,_===_) in
  ∀ (b : ℤ ₚ) →
  [ (₀ , b) ]ᵈ • H ≈ dir-of-DHa0 (₀ , b) ↑ • [ d-of-DHa0 (₀ , b) ]ᵈ

aux-DHa0 {n} ₀ = begin
  [ (₀ , ₀) ]ᵈ • H     ≈⟨ cleft d00≈Ex ⟩
  Ex • H               ≈⟨ sym lemma-comm-Ex-H-n ⟩
  H ↑ • Ex             ≈⟨ cright (sym d00≈Ex) ⟩
  H ↑ • [ (₀ , ₀) ]ᵈ   ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  cz0≈ε : CZ^ (- ₀) ≈ ε
  cz0≈ε = refl' (Eq.cong CZ^ -0#≈0#)
  d00≈Ex : [ (₀ , ₀) ]ᵈ ≈ Ex
  d00≈Ex = trans (cright cz0≈ε) right-unit

aux-DHa0 {n} (₁₊ b-1) = begin
  [ (₀ , b) ]ᵈ • H                       ≈⟨ assoc ⟩
  Ex • (CZ^ (- b) • H)                   ≈⟨ cright (cright (sym right-unit)) ⟩
  Ex • (CZ^ (- b) • (H • ε))             ≈⟨ cright (cright (cright ε≈S^)) ⟩
  Ex • (CZ^ (- b) • (H • S^ (- ₀ * b⁻¹))) ≈⟨ sym left-unit ⟩
  ε • [ (b , ₀) ]ᵈ                       ∎
  where
  b = ₁₊ b-1
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  pf : - ₀ * b⁻¹ ≡ ₀
  pf = Eq.trans (Eq.cong (_* b⁻¹) -0#≈0#) (*-zeroˡ b⁻¹)
  ε≈S^ : ε ≈ S^ (- ₀ * b⁻¹)
  ε≈S^ = sym (refl' (Eq.cong S^ pf))
