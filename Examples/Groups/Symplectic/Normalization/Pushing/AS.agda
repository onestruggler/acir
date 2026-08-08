{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)

open import Data.Empty using (⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Nat.Primality



module Examples.Groups.Symplectic.Normalization.Pushing.AS (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open LM2


open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
--open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

--open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime



dir-of-AS : A -> Word (Gen (₁₊ n))
dir-of-AS ((₀ , ₀) , nz) = ⊥-elim (nz auto)
dir-of-AS ((₀ , b@(₁₊ _)) , nz) = S^ (b⁻¹ ^2)
  where
  b* : ℤ* ₚ
  b* = (b , λ ())

  b⁻¹ : ℤ* ₚ
  b⁻¹ = b* ⁻¹
dir-of-AS ((₁₊ _ , b) , nz) = ε


a-of-AS : A -> A
a-of-AS ((₀ , ₀) , nz) = ⊥-elim (nz auto)
a-of-AS x@((₀ , b@(₁₊ _)) , nz) = x
a-of-AS ((a@(₁₊ _) , b) , nz) = (a , b + - a) , λ ()


aux-AS : let open PB ((₁₊ n) QRel,_===_) in

  ∀ d ->
  let
  d' = a-of-AS d
  w = dir-of-AS d
  in
  [ d ]ᵃ • S ≈ w • [ d' ]ᵃ


aux-AS {n} x@((a@₀ , b@₀) , nz) = ⊥-elim (nz auto)
aux-AS {n} x@((a@₀ , b@(₁₊ _)) , nz) = claim
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Pattern-Assoc
  open Lemmas-2Q n

  b* : ℤ* ₚ
  b* = (b , λ ())
  nzb : b ≢ ₀
  nzb = λ ()

  b⁻¹ : ℤ* ₚ
  b⁻¹ = b* ⁻¹
  b⁻¹' = b⁻¹ .proj₁

  w = S^ (b⁻¹ ^2)
  x' = x
  claim : [ x ]ᵃ • S ≈ w • [ x' ]ᵃ
  claim = begin
    ([ x ]ᵃ • S) ≈⟨ refl ⟩
    ([ (a , b) , (λ ()) ]ᵃ • S) ≈⟨ (  cleft aux-abox-nzb b nzb) ⟩
    (⟦ (b , nzb) ⁻¹ ⟧ₘ • S) ≈⟨ (  axiom (semi-MS ((b , nzb) ⁻¹))) ⟩
    (S^ (b⁻¹ ^2) • ⟦ (b , nzb) ⁻¹ ⟧ₘ) ≈⟨ sym (cong refl right-unit) ⟩
    S^ (b⁻¹ ^2) • [ x' ]ᵃ ∎


aux-AS {n} d@((a@(₁₊ _) , b) , nz) = claim
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a + ₁ ≡ - (b + - a) * a⁻¹
  aux = Eq.sym ( begin
    - (b + - a) * a⁻¹ ≡⟨ Eq.cong (_* a⁻¹) (Eq.sym (-‿+-comm b (- a))) ⟩
    (- b + - - a) * a⁻¹ ≡⟨ Eq.cong (\ xx -> (- b + xx) * a⁻¹) (-‿involutive a) ⟩
    (- b + a) * a⁻¹ ≡⟨ *-distribʳ-+ a⁻¹ (- b) a ⟩
    - b * a⁻¹ + a * a⁻¹ ≡⟨ Eq.cong (- b * a⁻¹ +_) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = λ ()}}}) ⟩
    - b * a⁻¹ + ₁ ≡⟨ auto ⟩
    -b/a + ₁ ∎
    )
    where
    open ≡-Reasoning

  
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas0 n
  open Pattern-Assoc

  w = S
  d' = ((a , b + - a) , λ ())
  
  claim : [ d ]ᵃ • S ≈ (ε ↑) • [ d' ]ᵃ
  claim = begin
    ([ d ]ᵃ • S) ≈⟨ refl ⟩
    ([ (a , b) , (λ ()) ]ᵃ • S) ≈⟨ (  sym refl) ⟩
    ((ZM ((a , λ ()) ⁻¹) • H • S^ -b/a) • S) ≈⟨ (  by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
    ((ZM ((a , λ ()) ⁻¹) • H) • S^ -b/a • S) ≈⟨ (  cright lemma-S^k+l -b/a ₁) ⟩
    ((ZM ((a , λ ()) ⁻¹) • H) • S^ (-b/a + ₁)) ≈⟨ ( ( assoc)) ⟩
    (ZM ((a , λ ()) ⁻¹) • H • S^ (-b/a + ₁)) ≡⟨ Eq.cong (\ xx -> (ZM ((a , λ ()) ⁻¹) • H • S^ xx)) aux ⟩
    ([ (a , (b + - a)) , (λ ()) ]ᵃ) ≈⟨ refl ⟩
    ([ d' ]ᵃ) ≈⟨ sym left-unit ⟩
    ε • ([ d' ]ᵃ)  ∎


aux-AS↑ : let open PB ((₂₊ n) QRel,_===_) in

  ∀ d -> [ d ]ᵃ • S ↑ ≈ S ↑ • [ d ]ᵃ

aux-AS↑ {n} x@((a@₀ , b@₀) , nz) = ⊥-elim (nz auto)
aux-AS↑ {n} x@((a@₀ , b@(₁₊ _)) , nz) = begin
  [ x ]ᵃ • S ↑ ≈⟨ aux-comm-mc-S↑ n ((b , λ ()) ⁻¹ , ε) ⟩
  S ↑ • [ x ]ᵃ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

aux-AS↑ {n} x@((a@(₁₊ _) , b) , nz) = begin
  [ x ]ᵃ • S ↑ ≈⟨ aux-comm-mc-S↑ n ((a , λ ()) ⁻¹ , HS^ -b/a) ⟩
  S ↑ • [ x ]ᵃ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
