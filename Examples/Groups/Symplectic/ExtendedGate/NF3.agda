{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ ; zero)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_] ; inspect)
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.NF3 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open Lemmas-2Q 2
open Symplectic-Derived-Gen
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF2 p-2 p-prime
open LM2
open Normal-Form1
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime

open ≡-Reasoning
open Eq
open import Algebra.Properties.Ring (+-*-ring p-2)

module LM3 where

  private
    variable
      n : ℕ

  lemma-act-Ex : ∀ p q t ->
    act {₂₊ n} Ex (p ∷ q ∷ t) ≡ (q ∷ p ∷ t)
  lemma-act-Ex p q t = act-Ex (p .proj₁) (p .proj₂) (q .proj₁) (q .proj₂) t



  aux-act-CZ-IZ : ∀ k (t : Pauli n) -> act (CZ^ k) (pI ∷ pZ ∷ t) ≡ (pI ∷ pZ ∷ t)
  aux-act-CZ-IZ k t = begin
    act (CZ^ k) (pI ∷ pZ ∷ t) ≡⟨ auto ⟩
    ((₀ , ₀ + ₀ * k) ∷ (₀ , ₁ + ₀ * k) ∷ t) ≡⟨ auto ⟩
    (pI ∷ pZ ∷ t) ∎

  aux-act-mc-I : ∀ (mc : MC') (t : Pauli n) -> act ⟦ mc ⟧ₘₕₛ (pI ∷ t) ≡ (pI ∷ t)
  aux-act-mc-I mc@(m , c@(HS^ k)) t = begin
    act ⟦ mc ⟧ₘₕₛ (pI ∷ t) ≡⟨ auto ⟩
    act (⟦ m ⟧ₘ • H) ((₀ , ₀) ∷ t) ≡⟨ auto ⟩
    act (⟦ m ⟧ₘ) ((- ₀ , ₀) ∷ t) ≡⟨ cong (\ xx -> act (⟦ m ⟧ₘ) ((xx , ₀) ∷ t)) -0#≈0# ⟩
    act (⟦ m ⟧ₘ) ((₀ , ₀) ∷ t) ≡⟨ lemma-M ₀ ₀ t m ⟩
    ((₀ * x⁻¹ , ₀ * x) ∷ t) ≡⟨ cong₂ (\ xx yy -> ((xx , yy) ∷ t)) (*-zeroˡ (m .proj₁)) (*-zeroˡ (m .proj₁)) ⟩
    (pI ∷ t) ∎
    where
    x = (m .proj₁)
    x⁻¹ = ((m ⁻¹) .proj₁ )

  lemma-act-mc : ∀ (a* : ℤ* ₚ) (b : ℤ ₚ) (t : Pauli n) ->
    let
    a = a* .proj₁
    m = a* ⁻¹
    a⁻¹ = (a* ⁻¹) .proj₁
    k = - b * a⁻¹
    in
    act ⟦ m , HS^ k ⟧ₘₕₛ ((a , b) ∷ t) ≡ (pZ ∷ t)
  lemma-act-mc a* b t = begin
    act ⟦ m , HS^ k ⟧ₘₕₛ ((a , b) ∷ t) ≡⟨ auto ⟩
    act ⟦ m ⟧ₘ ((- (b + a * k) , a) ∷ t) ≡⟨ cong (act ⟦ m ⟧ₘ) (lemma-HS a b t (a* .proj₂)) ⟩
    act ⟦ m ⟧ₘ ((₀ , a) ∷ t) ≡⟨ lemma-M ₀ a t m ⟩
    ((₀ * x⁻¹ , a * x) ∷ t) ≡⟨ cong₂ (\ xx yy -> (xx , yy) ∷ t) auto (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}}) ⟩
    ((₀ , ₁) ∷ t) ∎
    where
    a = a* .proj₁
    a⁻¹ = (a* ⁻¹) .proj₁
    k = - b * a⁻¹
    m = a* ⁻¹
    x = (m .proj₁)
    x⁻¹ = ((m ⁻¹) .proj₁)
    
  lemma-act-mc' : ∀ (a* : ℤ* ₚ) (b : ℤ ₚ) (t : Pauli n) ->
    let
    a = a* .proj₁
    m = -' (a* ⁻¹)
    -a⁻¹ = (-' (a* ⁻¹)) .proj₁
    k = -a⁻¹ * b
    in
    act ⟦ m , HS^ k ⟧ₘₕₛ ((a , b) ∷ t) ≡ ((₀ , - ₁) ∷ t)
  lemma-act-mc' a* b t = begin
    act ⟦ m , HS^ k ⟧ₘₕₛ ((a , b) ∷ t) ≡⟨ auto ⟩
    act ⟦ m ⟧ₘ ((- (b + a * k) , a) ∷ t) ≡⟨ cong (\ xx -> act ⟦ m ⟧ₘ ((xx , a) ∷ t)) aux ⟩
    act ⟦ m ⟧ₘ ((₀ , a) ∷ t) ≡⟨ lemma-M ₀ a t m ⟩
    ((₀ * x⁻¹ , a * x) ∷ t) ≡⟨ cong₂ (\ xx yy -> (xx , yy) ∷ t) auto (trans (sym (-‿distribʳ-* a a⁻¹)) (cong -_ (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}}))) ⟩
    ((₀ , - ₁) ∷ t) ∎
    where
    a = a* .proj₁
    m = -' (a* ⁻¹)
    a⁻¹ = (a* ⁻¹) .proj₁
    -a⁻¹ = (-' (a* ⁻¹)) .proj₁
    k = -a⁻¹ * b
    x = (m .proj₁)
    x⁻¹ = ((m ⁻¹) .proj₁)
    aux : - (b + a * k) ≡ ₀
    aux = begin
      - (b + a * k) ≡⟨ cong -_ (cong (b +_) (sym (*-assoc a -a⁻¹ b))) ⟩
      - (b + (a * -a⁻¹) * b) ≡⟨ cong -_ (cong (b +_) (cong (_* b) (sym (-‿distribʳ-* a a⁻¹)))) ⟩
      - (b + - (a * a⁻¹) * b) ≡⟨ cong (\ xx -> - (b + - xx * b)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = a* .proj₂}}}) ⟩
      - (b + - ₁ * b) ≡⟨ cong (\ xx -> - (b + xx)) (-1*x≈-x b) ⟩
      - (b + - b) ≡⟨ cong -_ (+-inverseʳ b) ⟩
      - ₀ ≡⟨ -0#≈0# ⟩
      ₀ ∎
    

  Theorem-LM3 :

    ∀ (ps qs : Pauli 3) (t : Pauli n) ->
    sform ps qs ≡ ₁ ->
    -----------------------------------------------------
    ∃ \ lm -> act ⟦ lm ⟧₃ (ps ++ t) ≡ pZ ∷ pI ∷ pI ∷ t ×
              act ⟦ lm ⟧₃ (qs ++ t) ≡ pX ∷ pI ∷ pI ∷ t
{-

  Theorem-LM3 ps@(p1@(₀ , ₀) ∷ p2 ∷ p3 ∷ []) qs@(q1@(c1@₀ , d1) ∷ q2 ∷ q3 ∷ []) t eq1 = lm , claim1 , claim2
    where
    ps' = (p2 ∷ p3 ∷ [])
    qs' = (q2 ∷ q3 ∷ [])
    
    eq1' : sform ps' qs' ≡ ₁
    eq1' = begin
      sform ps' qs' ≡⟨ sym (+-identityˡ (sform ps' qs')) ⟩
      ₀ + sform ps' qs' ≡⟨ cong (_+ sform ps' qs') (sym (sform-pI-q=0 q1)) ⟩
      sform1 pI q1 + sform ps' qs' ≡⟨ eq1 ⟩
      ₁ ∎
    
    c2p = Theorem-LM2 ps' qs' t eq1'

    k = - d1
    c2 = (c2p .proj₁)

    lm : Cosets3
    lm = case-Ia (- d1) c2

    claim1 : act ⟦ lm ⟧₃ (ps ++ t) ≡ pZ ∷ pI ∷ pI ∷ t
    claim1 = begin
      act ⟦ lm ⟧₃ (ps ++ t) ≡⟨ auto ⟩
      act (Ex • CZ^ k • ⟦ c2 ⟧₂ ↑) (ps ++ t) ≡⟨ cong (act (Ex • CZ^ k) ) (lemma-act-↑ ⟦ c2 ⟧₂ p1 (ps' ++ t)) ⟩
      act (Ex • CZ^ k) (p1 ∷ act ⟦ c2 ⟧₂ (ps' ++ t)) ≡⟨ cong (\ xx -> act (Ex • CZ^ k) (p1 ∷ xx)) (c2p .proj₂ .proj₁) ⟩
      act (Ex • CZ^ k) (p1 ∷ pZ ∷ pI ∷ t) ≡⟨ auto ⟩
      act (Ex) (p1 ∷ pZ ∷ pI ∷ t) ≡⟨ lemma-act-Ex p1 pZ (pI ∷ t) ⟩
      pZ ∷ pI ∷ pI ∷ t ∎

    claim2 : act ⟦ lm ⟧₃ (qs ++ t) ≡ pX ∷ pI ∷ pI ∷ t
    claim2 = begin
      act ⟦ lm ⟧₃ (qs ++ t) ≡⟨ auto ⟩
      act (Ex • CZ^ k • ⟦ c2 ⟧₂ ↑) (qs ++ t) ≡⟨ cong (act (Ex • CZ^ k) ) (lemma-act-↑ ⟦ c2 ⟧₂ q1 (qs' ++ t)) ⟩
      act (Ex • CZ^ k) (q1 ∷ act ⟦ c2 ⟧₂ (qs' ++ t)) ≡⟨ cong (\ xx -> act (Ex • CZ^ k) (q1 ∷ xx)) (c2p .proj₂ .proj₂) ⟩
      act (Ex • CZ^ k) (q1 ∷ pX ∷ pI ∷ t) ≡⟨ auto ⟩
      act (Ex) ((₀ , d1 + ₁ * k) ∷ (₁ , ₀) ∷ pI ∷ t) ≡⟨ cong (\ xx -> act (Ex) ((₀ , xx) ∷ (₁ , ₀) ∷ pI ∷ t)) (trans (cong (d1 +_) (*-identityˡ k)) (+-inverseʳ d1)) ⟩
      act (Ex) ((₀ , ₀) ∷ (₁ , ₀) ∷ pI ∷ t) ≡⟨ lemma-act-Ex p1 pX (pI ∷ t) ⟩
      pX ∷ pI ∷ pI ∷ t ∎



  Theorem-LM3 ps@(p1@(₀ , ₀) ∷ p2 ∷ p3 ∷ []) qs@(q1@(c1@(₁₊ _) , d1) ∷ q2 ∷ q3 ∷ []) t eq1 = lm , claim1 , claim2
    where
    ps' = (p2 ∷ p3 ∷ [])
    qs' = (q2 ∷ q3 ∷ [])
    
    eq1' : sform ps' qs' ≡ ₁
    eq1' = begin
      sform ps' qs' ≡⟨ sym (+-identityˡ (sform ps' qs')) ⟩
      ₀ + sform ps' qs' ≡⟨ cong (_+ sform ps' qs') (sym (sform-pI-q=0 q1)) ⟩
      sform1 pI q1 + sform ps' qs' ≡⟨ eq1 ⟩
      ₁ ∎
    
    c2p = Theorem-LM2 ps' qs' t eq1'

    k = - d1
    c2 = (c2p .proj₁)

    c1* : ℤ* ₚ
    c1* = (c1 , λ ())
    -'c1*⁻¹ = -' c1* ⁻¹
    -c1⁻¹ = -'c1*⁻¹ .proj₁
    mc : MC'
    mc = (-'c1*⁻¹ , HS^ (-c1⁻¹ * d1))
    lm : Cosets3
    lm = case-Ib mc c2

    claim1 : act ⟦ lm ⟧₃ (ps ++ t) ≡ pZ ∷ pI ∷ pI ∷ t
    claim1 = begin
      act ⟦ lm ⟧₃ (ps ++ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ mc ⟧ₘₕₛ • ⟦ c2 ⟧₂ ↑) (ps ++ t) ≡⟨ cong (act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) ) (lemma-act-↑ ⟦ c2 ⟧₂ p1 (ps' ++ t)) ⟩
      act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) (p1 ∷ act ⟦ c2 ⟧₂ (ps' ++ t)) ≡⟨ cong (\ xx -> act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) (p1 ∷ xx)) (c2p .proj₂ .proj₁) ⟩
      act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) (p1 ∷ pZ ∷ pI ∷ t) ≡⟨ cong (act (Ex • CZ)) (aux-act-mc-I mc (pZ ∷ pI ∷ t)) ⟩
      act (Ex • CZ) (p1 ∷ pZ ∷ pI ∷ t) ≡⟨ auto ⟩
      act (Ex) (p1 ∷ pZ ∷ pI ∷ t) ≡⟨ lemma-act-Ex p1 pZ (pI ∷ t) ⟩
      pZ ∷ pI ∷ pI ∷ t ∎


    claim2 : act ⟦ lm ⟧₃ (qs ++ t) ≡ pX ∷ pI ∷ pI ∷ t
    claim2 = begin
      act ⟦ lm ⟧₃ (qs ++ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ mc ⟧ₘₕₛ • ⟦ c2 ⟧₂ ↑) (qs ++ t) ≡⟨ cong (act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) ) (lemma-act-↑ ⟦ c2 ⟧₂ q1 (qs' ++ t)) ⟩
      act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) (q1 ∷ act ⟦ c2 ⟧₂ (qs' ++ t)) ≡⟨ cong (\ xx -> act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) (q1 ∷ xx)) (c2p .proj₂ .proj₂) ⟩
      act (Ex • CZ • ⟦ mc ⟧ₘₕₛ) (q1 ∷ pX ∷ pI ∷ t) ≡⟨ cong (act (Ex • CZ)) (lemma-act-mc' c1* d1 (pX ∷ pI ∷ t)) ⟩
      act (Ex • CZ) ((₀ , - ₁) ∷ pX ∷ pI ∷ t) ≡⟨ auto ⟩
      act (Ex) ((₀ , - ₁ + ₁ * ₁ ) ∷ pX ∷ pI ∷ t) ≡⟨ cong (\ xx -> act (Ex) ((₀ , xx) ∷ pX ∷ pI ∷ t)) (trans (cong (- ₁ +_) (*-identityˡ ₁)) (+-inverseˡ ₁)) ⟩
      act (Ex) (pI ∷ pX ∷ pI ∷ t) ≡⟨ lemma-act-Ex pI pX (pI ∷ t) ⟩
      pX ∷ pI ∷ pI ∷ t ∎


-}

  Theorem-LM3 ps@(p1@(a1 , b1@(₁₊ _)) ∷ p2@(a2 , b2) ∷ p3 ∷ []) qs@(q1@(c1@(₁₊ _) , d1) ∷ q2 ∷ q3 ∷ []) t eq1 = lm , claim1 , {!!}
    where
    ps' = (p2 ∷ p3 ∷ [])
    qs' = (q2 ∷ q3 ∷ [])


    c1* : ℤ* ₚ
    c1* = (c1 , λ ())
    -'c1*⁻¹ = -' c1* ⁻¹
    -c1⁻¹ = -'c1*⁻¹ .proj₁
    co2 = {!!}
    co2p = {!!}
    k = - a2
    l = - b2
    mcl : MC'
    mcl = (-'c1*⁻¹ , HS^ (-c1⁻¹ * d1))
    lm : Cosets3
    lm = case-IIb mcl co2 (k , l) 


    claim1 : act ⟦ lm ⟧₃ (ps ++ t) ≡ pZ ∷ pI ∷ pI ∷ t
    claim1 = begin
      act ⟦ lm ⟧₃ (ps ++ t) ≡⟨ auto ⟩
      act (Ex • CZ • ⟦ mcl ⟧ₘₕₛ • ⟦ c2-emb co2 ⟧₂ ↑ • CZ^ k • H • CZ^ l) (ps ++ t) ≡⟨ {!!} ⟩
      act (Ex • CZ • ⟦ mcl ⟧ₘₕₛ) (p1 ∷ act ⟦ c2-emb co2 ⟧₂ (ps' ++ t)) ≡⟨ cong (\ xx -> act (Ex • CZ • ⟦ mcl ⟧ₘₕₛ) (p1 ∷ xx)) (co2p .proj₂ .proj₁) ⟩
      act (Ex • CZ • ⟦ mcl ⟧ₘₕₛ) (pI ∷ pZ ∷ pI ∷ t) ≡⟨ cong (act (Ex • CZ)) {!!} ⟩
      act (Ex • CZ) (pI ∷ pZ ∷ pI ∷ t) ≡⟨ auto ⟩
      act (Ex) (pI ∷ pZ ∷ pI ∷ t) ≡⟨ lemma-act-Ex pI pZ (pI ∷ t) ⟩
      pZ ∷ pI ∷ pI ∷ t ∎
