{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)


open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


import Data.Nat.Properties as NP
open import Data.Nat.Primality


module Examples.Groups.Symplectic.Lemmas.Ex-Sym3 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where


open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas-2Q 0
module Lemmas0c where

  private
    variable
      n : ℕ
      
  open Symplectic
  open Lemmas-Sym

  open Symplectic-GroupLike

  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  open Duality

  open import Algebra.Properties.Ring (+-*-ring p-2)
  open PB (₂ QRel,_===_)
  open PP (₂ QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 1


  abstract


    lemma-CZ^-aHCZ^k' : ∀ (a* k* : ℤ* ₚ) →
      let
        k : ℤ ₚ
        k = k* .proj₁
        a : ℤ ₚ
        a = a* .proj₁
        -k : ℤ ₚ
        -k = - k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      in

      CZ^ a • H • CZ^ k ≈ S^ (-k⁻¹ * a) • H • CZ^ k • H ^ 3 • S^ (k⁻¹ * a) • H • S^ (-k * a) ↑

    lemma-CZ^-aHCZ^k' a*@(a@₀ , nza) k*@(k , nzk) with nza auto
    ... | ()
    lemma-CZ^-aHCZ^k' a*@(a@(₁₊ a') , nza) k*@(k , nzk) = begin
      CZ^ a • H • CZ^ k ≈⟨ lemma-CZCZ^aHCZ^k' (toℕ a') k nzk ⟩
      S^ -k⁻¹ ^ j • H • CZ^ k • H ^ 3 • S^ k⁻¹ ^ j • H • (S^ -k ^ j) ↑ ≈⟨ cong (aux-S^-^ a -k⁻¹ nza) (cright (cright (cright cong (aux-S^-^ a k⁻¹ nza) (cright lemma-cong↑ _ _ (aux-S^-^ a -k nza))))) ⟩
      S^ (-k⁻¹ * a) • H • CZ^ k • H ^ 3 • S^ (k⁻¹ * a) • H • S^ (-k * a) ↑ ∎
      where
      j : ℕ
      j = toℕ a
      -k : ℤ ₚ
      -k = - k
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹


    lemma-CZ^-aHCZ^k-selinger : ∀ (a* k* : ℤ* ₚ) →
      let
        k : ℤ ₚ
        k = k* .proj₁
        a : ℤ ₚ
        a = a* .proj₁
        -k : ℤ ₚ
        -k = - k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        a⁻¹ : ℤ ₚ
        a⁻¹ = ((a* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      in

      CZ^ a • H • CZ^ k ≈ S^ (-k⁻¹ * a) • H • CZ^ k • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑

    lemma-CZ^-aHCZ^k-selinger a*@(a , nza) k*@(k , nzk) = begin
      CZ^ a • H • CZ^ k ≈⟨ lemma-CZ^-aHCZ^k' a* k* ⟩
      S^ (-k⁻¹ * a) • H • CZ^ k • H ^ 3 • S^ (k⁻¹ * a) • H • S^ (-k * a) ↑ ≈⟨ (cright cright cright by-passoc (□ ^ 4) (□ ^ 3 • □) auto) ⟩
      S^ (-k⁻¹ * a) • H • CZ^ k • (H ^ 3 • S^ (k⁻¹ * a) • H) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cleft lemma-Euler-Mˡ' (k* ⁻¹ *' a*)) ⟩
      S^ (-k⁻¹ * a) • H • CZ^ k • (M ((k* ⁻¹ *' a*) ⁻¹) • S^ (- (k⁻¹ * a)) • H • S^ (- (((k* ⁻¹ *' a*) ⁻¹) .proj₁))) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cleft cong (aux-MM (((k* ⁻¹ *' a*) ⁻¹) .proj₂) ( (k* *' a* ⁻¹) .proj₂) aux) (cong (refl' (Eq.cong S^ (-‿distribˡ-* k⁻¹ a))) (cright refl' (Eq.cong S^ aux2)))) ⟩
      S^ (-k⁻¹ * a) • H • CZ^ k • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ∎
      where
      j : ℕ
      j = toℕ a
      -k : ℤ ₚ
      -k = - k
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      a⁻¹ : ℤ ₚ
      a⁻¹ = ((a* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹
      aux : ((k* ⁻¹ *' a*) ⁻¹) .proj₁ ≡ (k* *' a* ⁻¹) .proj₁
      aux = Eq.trans (inv-distrib (k* ⁻¹) a*) (Eq.cong (_* a⁻¹) (inv-involutive k*))
      aux2 : - (((k* ⁻¹ *' a*) ⁻¹) .proj₁) ≡ -k * a⁻¹
      aux2 = Eq.trans (Eq.cong -_ (aux )) (-‿distribˡ-* k a⁻¹ )


    lemma-CZ^-aHCZ^k-selinger' : ∀ (a* k* : ℤ* ₚ) →
      let
        k : ℤ ₚ
        k = k* .proj₁
        a : ℤ ₚ
        a = a* .proj₁
        -k : ℤ ₚ
        -k = - k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        a⁻¹ : ℤ ₚ
        a⁻¹ = ((a* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      in

      CZ^ a • H • CZ^ k ≈ M (k* ⁻¹) • S^ (-k * a) • H • CZ • S^ (-k⁻¹ * a⁻¹) • H • S^ (-k * a) • S^ (-k * a) ↑ • M a*

    lemma-CZ^-aHCZ^k-selinger' a*@(a , nza) k*@(k , nzk) = begin
      CZ^ a • H • CZ^ k ≈⟨ lemma-CZ^-aHCZ^k-selinger a* k* ⟩
      S^ (-k⁻¹ * a) • H • CZ^ k • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright sym left-unit) ⟩
      S^ (-k⁻¹ * a) • H • ε • CZ^ k • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright cleft sym (aux-M-mul k*)) ⟩
      S^ (-k⁻¹ * a) • H • (M k* • M (k* ⁻¹)) • CZ^ k • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
      S^ (-k⁻¹ * a) • H • M k* • (M (k* ⁻¹) • CZ^ k) • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cleft lemma-M↓CZ^k k⁻¹ k ((k* ⁻¹) .proj₂)) ⟩
      S^ (-k⁻¹ * a) • H • M k* • (CZ^ (k * k⁻¹) • M (k* ⁻¹)) • (M (k* *' a* ⁻¹) • S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright cright by-passoc (□ ^ 2 • □ ^ 4 • □) (□ • □ ^ 2 • □ ^ 3 • □) auto) ⟩
      S^ (-k⁻¹ * a) • H • M k* • CZ^ (k * k⁻¹) • (M (k* ⁻¹) • M (k* *' a* ⁻¹)) • (S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cong (refl' (Eq.cong CZ^ (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = k* .proj₂}}}))) (cleft axiom (M-mul (k* ⁻¹) (k* *' a* ⁻¹)))) ⟩
      S^ (-k⁻¹ * a) • H • M k* • CZ • M (k* ⁻¹ *' (k* *' a* ⁻¹)) • (S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cright cleft aux-MM ((k* ⁻¹ *' (k* *' a* ⁻¹)) .proj₂) ((a* ⁻¹) .proj₂) aux3) ⟩
      S^ (-k⁻¹ * a) • H • M k* • CZ • M (a* ⁻¹) • (S^ (-k⁻¹ * a) • H • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ ^ 3 • □) (□ • □ ^ 2 • □ • □ ^ 2 • □ ^ 3) auto ⟩
      S^ (-k⁻¹ * a) • (H • M k*) • CZ • (M (a* ⁻¹) • S^ (-k⁻¹ * a)) • H • S^ (-k * a⁻¹) • S^ (-k * a) ↑ ≈⟨ (cright cong (semi-HM k*) (cright (cleft lemma-MS^k a⁻¹ (-k⁻¹ * a) ((a* ⁻¹) .proj₂)))) ⟩
      S^ (-k⁻¹ * a) • (M (k* ⁻¹) • H) • CZ • (S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • M (a* ⁻¹)) • H • S^ (-k * a⁻¹) • S^ (-k * a) ↑ ≈⟨ by-passoc (□ • □ ^ 2 • □ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
      (S^ (-k⁻¹ * a) • M (k* ⁻¹)) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • (M (a* ⁻¹) • H) • S^ (-k * a⁻¹) • S^ (-k * a) ↑ ≈⟨ cong (sym (lemma-MS^k' k⁻¹ (-k⁻¹ * a) ((k* ⁻¹) .proj₂))) (cright cright cright cleft sym (semi-HM a*)) ⟩
      (M (k* ⁻¹) • S^ (-k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹))) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • (H • M a*) • S^ (-k * a⁻¹) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cright by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
      (M (k* ⁻¹) • S^ (-k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹))) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • H • (M a* • S^ (-k * a⁻¹)) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cright cright cleft lemma-MS^k a (-k * a⁻¹) nza) ⟩
      (M (k* ⁻¹) • S^ (-k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹))) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • H • (S^ (-k * a⁻¹ * (a * a)) • M a*) • S^ (-k * a) ↑ ≈⟨ (cright cright cright cright (cright assoc)) ⟩
      (M (k* ⁻¹) • S^ (-k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹))) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • H • S^ (-k * a⁻¹ * (a * a)) • M a* • S^ (-k * a) ↑ ≈⟨ (cright cright cright cright cright cright aux-comm-m-S^ (a , nza) (fromℕ< _)) ⟩
      (M (k* ⁻¹) • S^ (-k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹))) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • H • S^ (-k * a⁻¹ * (a * a)) • S^ (-k * a) ↑ • M a* ≈⟨ assoc ⟩
      M (k* ⁻¹) • S^ (-k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹)) • H • CZ • S^ (-k⁻¹ * a * (a⁻¹ * a⁻¹)) • H • S^ (-k * a⁻¹ * (a * a)) • S^ (-k * a) ↑ • M a* ≈⟨ (cright cong (refl' (Eq.cong S^ aux5)) (cright cright cong (refl' (Eq.cong S^ aux6)) (cright cleft refl' (Eq.cong S^ aux7)))) ⟩
      M (k* ⁻¹) • S^ (-k * a) • H • CZ • S^ (-k⁻¹ * a⁻¹) • H • S^ (-k * a) • S^ (-k * a) ↑ • M a* ∎
      where
      j : ℕ
      j = toℕ a
      -k : ℤ ₚ
      -k = - k
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      k⁻¹⁻¹ : ℤ ₚ
      k⁻¹⁻¹ = ((k* ⁻¹ ⁻¹) .proj₁)
      a⁻¹ : ℤ ₚ
      a⁻¹ = ((a* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹
      aux : ((k* ⁻¹ *' a*) ⁻¹) .proj₁ ≡ (k* *' a* ⁻¹) .proj₁
      aux = Eq.trans (inv-distrib (k* ⁻¹) a*) (Eq.cong (_* a⁻¹) (inv-involutive k*))
      aux2 : - (((k* ⁻¹ *' a*) ⁻¹) .proj₁) ≡ -k * a⁻¹
      aux2 = Eq.trans (Eq.cong -_ (aux )) (-‿distribˡ-* k a⁻¹ )
      aux3 : (k* ⁻¹ *' (k* *' a* ⁻¹)) .proj₁ ≡ (a* ⁻¹) .proj₁
      aux3 = Eq.trans (Eq.sym (*-assoc k⁻¹ k a⁻¹)) (Eq.trans (Eq.cong (_* a⁻¹) (lemma-⁻¹ˡ k {{nztoℕ {y = k} {neq0 = k* .proj₂}}})) (*-identityˡ a⁻¹))
      aux4 : k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹) ≡ k * a
      aux4 = Eq.trans (Eq.cong (_* (k⁻¹⁻¹ * k⁻¹⁻¹)) (*-comm k⁻¹ a) ) (Eq.trans (*-assoc a k⁻¹ (k⁻¹⁻¹ * k⁻¹⁻¹)) (Eq.trans (Eq.cong (a *_) (Eq.sym (*-assoc k⁻¹ k⁻¹⁻¹  k⁻¹⁻¹))) (Eq.trans (Eq.cong (\ xx → a * (xx * k⁻¹⁻¹)) (lemma-⁻¹ʳ k⁻¹ {{nztoℕ {y = k⁻¹} {neq0 = (k* ⁻¹) .proj₂}}})) (Eq.trans (Eq.cong (\ xx → a * xx) (*-identityˡ k⁻¹⁻¹)) (Eq.trans (Eq.cong (\ xx → a * xx) (inv-involutive k*)) (*-comm a k)))))) 
      aux5 : -k⁻¹ * a * (k⁻¹⁻¹ * k⁻¹⁻¹) ≡ -k * a
      aux5 = Eq.trans (Eq.cong (_* (k⁻¹⁻¹ * k⁻¹⁻¹)) (Eq.sym (-‿distribˡ-* k⁻¹ a))) (Eq.trans (Eq.sym (-‿distribˡ-* (k⁻¹ * a) (k⁻¹⁻¹ * k⁻¹⁻¹))) (Eq.trans (Eq.cong -_ aux4) (-‿distribˡ-* k a)))

      aux6 : -k⁻¹ * a * (a⁻¹ * a⁻¹) ≡ -k⁻¹ * a⁻¹
      aux6 = Eq.trans (*-assoc -k⁻¹ a (a⁻¹ * a⁻¹)) (Eq.trans (Eq.cong (-k⁻¹ *_) (Eq.sym (*-assoc a a⁻¹ a⁻¹))) (Eq.trans (Eq.cong (\ xx → -k⁻¹ * (xx * a⁻¹)) (lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = (a*) .proj₂}}})) (Eq.cong (-k⁻¹ *_) (*-identityˡ a⁻¹))))


      aux7 : -k * a⁻¹ * (a * a) ≡ -k * a
      aux7 = Eq.trans (*-assoc -k a⁻¹ (a * a)) (Eq.trans (Eq.cong (-k *_) (Eq.sym (*-assoc a⁻¹ a a))) (Eq.trans (Eq.cong (\ xx → -k * (xx * a)) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = (a*) .proj₂}}})) (Eq.cong (-k *_) (*-identityˡ a))))
      

    lemma-CXCZ^k : ∀ (k* : ℤ* ₚ) →
      let
        k : ℤ ₚ
        k = k* .proj₁
        -k : ℤ ₚ
        -k = - k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      in

      -- checked for 7 and 11 in Haskell
      CX • CZ^ k ≈ S^ k • CX • S^ -k • S^ -k ↑ 

    lemma-CXCZ^k k*@(k , nzk) = begin
      CX • CZ^ k ≈⟨ trans assoc (cong refl assoc) ⟩
      H ^ 3 • CZ • H • CZ^ k ≈⟨ (cright lemma-CZ^-aHCZ^k-selinger' (a , (λ ())) k*) ⟩
      H ^ 3 • M (k* ⁻¹) • S^ (-k * a) • H • CZ • S^ (-k⁻¹ * a⁻¹) • H • S^ (-k * a) • S^ (-k * a) ↑ • M a* ≈⟨ (cright cright cong (refl' (Eq.cong S^ (*-identityʳ -k))) (cright cright cong (refl' (Eq.cong S^ (Eq.trans (Eq.cong (-k⁻¹ *_) aux₁⁻¹') (*-identityʳ -k⁻¹)))) (cright cong (refl' (Eq.cong S^ (*-identityʳ -k))) (cong (lemma-cong↑ _ _ (PB1.refl' (Eq.cong S^ (*-identityʳ -k)))) (sym lemma-M1))))) ⟩
      H ^ 3 • M (k* ⁻¹) • S^ -k • H • CZ • S^ -k⁻¹ • H • S^ -k • S^ -k ↑ • ε ≈⟨ (cright cright cright cright cright cright cright cright right-unit) ⟩
      H ^ 3 • M (k* ⁻¹) • S^ -k • H • CZ • S^ -k⁻¹ • H • S^ -k • S^ -k ↑ ≈⟨ (cright cright cright cright sym assoc) ⟩
      H ^ 3 • M (k* ⁻¹) • S^ -k • H • (CZ • S^ -k⁻¹) • H • S^ -k • S^ -k ↑ ≈⟨ (cright cright cright cright cleft comm⇒pow-comm 1 (toℕ -k⁻¹) (axiom comm-CZ-S↓)) ⟩
      H ^ 3 • M (k* ⁻¹) • S^ -k • H • (S^ -k⁻¹ • CZ) • H • S^ -k • S^ -k ↑ ≈⟨ by-passoc (□ • □ • □ • □ • □ ^ 2 • □) (□ • □ ^ 4 • □ ^ 2) auto ⟩
      H ^ 3 • (M (k* ⁻¹) • S^ -k • H • S^ -k⁻¹) • CZ • H • S^ -k • S^ -k ↑ ≈⟨ (cright cleft sym (lemma-Euler-Mˡ' k*)) ⟩
      H ^ 3 • (H ^ 3 • S^ k • H) • CZ • H • S^ -k • S^ -k ↑ ≈⟨ by-passoc (□ • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
      (H ^ 3 • H ^ 3) • (S^ k • H) • CZ • H • S^ -k • S^ -k ↑ ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
      HH • (S^ k • H) • CZ • H • S^ -k • S^ -k ↑ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (HH • S^ k) • H • CZ • H • S^ -k • S^ -k ↑ ≈⟨ (cleft comm⇒pow-comm 1 (toℕ k) (trans assoc (axiom comm-HHS))) ⟩
      (S^ k • HH) • H • CZ • H • S^ -k • S^ -k ↑ ≈⟨ by-passoc (□ ^ 3 • □ ^ 5) (□ • (□ ^ 3 • □ ^ 2) • □ ^ 2) auto ⟩
      S^ k • (H ^ 3 • CZ • H) • S^ -k • S^ -k ↑ ≈⟨ refl ⟩
      S^ k • CX • S^ -k • S^ -k ↑  ∎
      where
      a* : ℤ* ₚ
      a* = (₁ , λ ())
      a : ℤ ₚ
      a = ₁
      a⁻¹ : ℤ ₚ
      a⁻¹ = (a* ⁻¹) .proj₁
      -k : ℤ ₚ
      -k = - k
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹
      module PB1 = PB (1 QRel,_===_)
      open Sym0-Rewriting 1
      

    lemma-semi-CXCZ^k : ∀ (k* : ℤ* ₚ) →
      let
        k : ℤ ₚ
        k = k* .proj₁
        -k : ℤ ₚ
        -k = - k
        -2k : ℤ ₚ
        -2k = -k + -k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      in

      -- checked for 7 and 11, 17 in Haskell
      CX • CZ^ k ≈ S^ -2k ↑ • CZ^ k • CX

    lemma-semi-CXCZ^k k* = begin
      CX • CZ^ k ≈⟨ lemma-CXCZ^k k* ⟩
      S^ k • CX • S^ -k • S^ -k ↑ ≈⟨ (cright sym assoc) ⟩
      S^ k • (CX • S^ -k) • S^ -k ↑ ≈⟨ (cright cleft sym (lemma-CXS^k -k)) ⟩
      S^ k • (S^ -k • S^ -k ↑ • CZ^ (- -k) • CX) • S^ -k ↑ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (S^ k • S^ -k) • (S^ -k ↑ • CZ^ (- -k) • CX) • S^ -k ↑ ≈⟨ cong (lemma-S^k-k k) (cleft cright cleft refl' (Eq.cong CZ^ (-‿involutive k))) ⟩
      ε • (S^ -k ↑ • CZ^ k • CX) • S^ -k ↑ ≈⟨ left-unit ⟩
      (S^ -k ↑ • CZ^ k • CX) • S^ -k ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (S^ -k ↑ • CZ^ k) • CX • S^ -k ↑ ≈⟨ (cright aux-comm-CX^a-S^k↑ ₁ -k) ⟩
      (S^ -k ↑ • CZ^ k) • S^ -k ↑ • CX ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
      S^ -k ↑ • (CZ^ k • S^ -k ↑) • CX ≈⟨ (cright cleft aux-comm-CZ^a-S^b↑ (k* .proj₁) (fromℕ< _)) ⟩
      S^ -k ↑ • (S^ -k ↑ • CZ^ k) • CX ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (S^ -k ↑ • S^ -k ↑) • CZ^ k • CX ≈⟨ (cleft lemma-cong↑ _ _ (L0.lemma-S^k+l -k -k)) ⟩
      S^ -2k ↑ • CZ^ k • CX ∎
      where
        module L0 = Lemmas0 0
        k : ℤ ₚ
        k = k* .proj₁
        -k : ℤ ₚ
        -k = - k
        -2k : ℤ ₚ
        -2k = -k + -k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      

    lemma-semi-CXCZ : S ↑ ^ 2 • CX • CZ ≈ CZ • CX
    lemma-semi-CXCZ = begin
      S ↑ ^ 2 • CX • CZ ≈⟨ (cright by-assoc auto) ⟩
      S ↑ ^ 2 • H ↓ ^ 3 • (CZ • H ↓ • CZ) ≈⟨ (cright cright axiom selinger-c11) ⟩
      S ↑ ^ 2 • H ↓ ^ 3 • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑) ≈⟨ (cright cright by-passoc (□ ^ 7) (  □ ^ 3 • □ ^ 4) auto) ⟩
      S ↑ ^ 2 • H ↓ ^ 3 • (S⁻¹ ↓ • H ↓ • S⁻¹ ↓) • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ (cright cright cleft lemma-S⁻¹HS⁻¹) ⟩
      S ↑ ^ 2 • H ↓ ^ 3 • (H⁻¹ • S • H) • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ by-passoc (□ • □ • □ ^ 3 • □ ^ 4) (□ ^ 5 • □ ^ 4) auto ⟩
      (S ↑ ^ 2 • H ↓ ^ 3 • H⁻¹ • S • H) • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
      (S ↑ ^ 2 • S • H ^ 3) • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑ ≈⟨ by-passoc (□ ^ 3 • □ ^ 4) (□ • □ • (□ ^ 3 • □) • □) auto ⟩
      S ↑ ^ 2 • S • ((H ^ 3 • CZ • H) • S⁻¹) • S⁻¹ ↑ ≈⟨ (cright cright cleft sym (lemma-CXS^k-ℕ p-1)) ⟩
      S ↑ ^ 2 • S • (S ^ k • (S ^ k) ↑ • CZ ^ -k • H^ ₃ • CZ • H) • S⁻¹ ↑ ≈⟨ (cright by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ ^ 4 ) auto) ⟩
      S ↑ ^ 2 • (S • S ^ k) • (S ^ k) ↑ • CZ ^ -k • (CX • S⁻¹ ↑) ≈⟨ (cright cleft axiom order-S) ⟩
      S ↑ ^ 2 • ε • (S ^ k) ↑ • CZ ^ -k • (CX • S⁻¹ ↑) ≈⟨ (cright left-unit) ⟩
      S ↑ ^ 2 • (S ^ k) ↑ • CZ ^ -k • (CX • S⁻¹ ↑) ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
      S ↑ • (S ↑ • (S ^ k) ↑) • CZ ^ -k • (CX • S⁻¹ ↑) ≈⟨ (cright cleft axiom (cong↑ order-S)) ⟩
      S ↑ • ε • CZ ^ -k • (CX • S⁻¹ ↑) ≈⟨ (cright left-unit) ⟩
      S ↑ • CZ ^ -k • (CX • S⁻¹ ↑) ≈⟨ (cright cright aux-comm-CX-S^k↑-ℕ p-1) ⟩
      S ↑ • CZ ^ -k • (S⁻¹ ↑ • CX) ≈⟨ (cright sym assoc) ⟩
      S ↑ • (CZ ^ -k • S⁻¹ ↑) • CX ≈⟨ (cright cleft aux-comm-CZ^a-S^b↑' -k p-1) ⟩
      S ↑ • (S⁻¹ ↑ • CZ ^ -k ) • CX ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (S ↑ • S⁻¹ ↑) • CZ ^ -k • CX ≈⟨ (cleft axiom (cong↑ order-S)) ⟩
      ε • CZ ^ -k • CX ≈⟨ left-unit ⟩
      CZ ^ -k • CX ≈⟨ (cleft aux00) ⟩
      CZ • CX ∎
      where
      open Sym0-Rewriting 1
      k : ℕ
      k = p-1
      -k : ℕ
      -k = p-1 Nat.* k

      aux00 : CZ ^ -k ≈ CZ
      aux00 = begin
        CZ ^ -k ≈⟨ sym (^^ CZ p-1 p-1) ⟩
        (CZ ^ p-1) ^ p-1 ≈⟨ aux-CZ⁻¹⁻¹ ⟩
        CZ ∎


    lemma-semi-CXCZ^k-ℕ' : ∀ (k : ℕ) → let 2k = k Nat.* 2 in

      S ↑ ^ 2k • CX • CZ ^ k ≈ CZ ^ k • CX

    lemma-semi-CXCZ^k-ℕ' k@0 = begin
      S ↑ ^ 2k • CX • CZ ^ k ≈⟨ trans left-unit (trans right-unit (sym left-unit)) ⟩
      CZ ^ k • CX ∎
      where
      2k : ℕ
      2k = k Nat.* 2
    lemma-semi-CXCZ^k-ℕ' k@1 = begin
      S ↑ ^ 2 • CX • CZ ≈⟨ lemma-semi-CXCZ ⟩
      CZ • CX ∎
      where
      2k : ℕ
      2k = k Nat.* 2

    lemma-semi-CXCZ^k-ℕ' k@(₂₊ k-2) = begin
      S ↑ ^ 2k • CX • CZ ^ k ≈⟨ refl ⟩
      (S ↑ ^ 2k) • CX • CZ ^ k ≈⟨ cong (sym aux) (cright refl) ⟩
      (S ↑ ^ 2[k-1] • S ↑ ^ 2) • CX • CZ • CZ ^ (₁₊ k-2) ≈⟨ by-passoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 3 • □) auto ⟩
      S ↑ ^ 2[k-1] • (S ↑ ^ 2 • CX • CZ) • CZ ^ (₁₊ k-2) ≈⟨ (cright cleft lemma-semi-CXCZ) ⟩
      S ↑ ^ 2[k-1] • (CZ • CX) • CZ ^ (₁₊ k-2) ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (S ↑ ^ 2[k-1] • CZ) • CX • CZ ^ (₁₊ k-2) ≈⟨ (cleft comm⇒pow-comm 2[k-1] 1 (sym (axiom comm-CZ-S↑))) ⟩
      (CZ • S ↑ ^ 2[k-1]) • CX • CZ ^ (₁₊ k-2) ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 4) auto ⟩
      CZ • S ↑ ^ 2[k-1] • CX • CZ ^ (₁₊ k-2) ≈⟨ (cright lemma-semi-CXCZ^k-ℕ' (₁₊ k-2)) ⟩
      CZ • CZ ^ (₁₊ k-2) • CX ≈⟨ sym assoc ⟩
      CZ ^ k • CX ∎
      where
      2k : ℕ
      2k = k Nat.* 2
      2[k-1] : ℕ
      2[k-1] = (₁₊ k-2) Nat.* 2
      k-1 : ℕ
      k-1 = (₁₊ k-2)
      aux : S ↑ ^ 2[k-1] • S ↑ ^ 2 ≈ S ↑ ^ 2k
      aux = begin
        S ↑ ^ 2[k-1] • S ↑ ^ 2 ≈⟨ comm⇒pow-comm 2[k-1] 2 refl ⟩
        S ↑ ^ 2 • S ↑ ^ 2[k-1] ≈⟨ (cright sym (^^ (S ↑) k-1 2)) ⟩
        S ↑ ^ 2 • (S ↑ ^ k-1) ^ 2 ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
        S ↑ • (S ↑ • S ↑ ^ k-1) • S ↑ ^ k-1 ≈⟨ refl ⟩
        S ↑ • (S ↑ ^ k) • S ↑ ^ k-1 ≈⟨ (cright comm⇒pow-comm k k-1 refl) ⟩
        S ↑ • S ↑ ^ k-1 • (S ↑ ^ k) ≈⟨ sym assoc ⟩
        (S ↑ • S ↑ ^ k-1) • (S ↑ ^ k) ≈⟨ refl ⟩
        S ↑ ^ k • S ↑ ^ k ≈⟨ sym (^-+ (S ↑) k k) ⟩
        S ↑ ^ (k Nat.+ k) ≈⟨ refl' (Eq.cong ((S ↑) ^_) (Eq.sym (Eq.trans (NP.*-comm k 2) (Eq.sym aux0)))) ⟩
        S ↑ ^ 2k ∎
        where
        open import Data.Nat.Solver as NS
        aux0 : (k Nat.+ k) ≡ 2 Nat.* k
        aux0 = Eq.sym (Eq.trans (NP.*-distribʳ-+ k 1 1) (Eq.cong₂ Nat._+_ (NP.*-identityˡ k) (NP.*-identityˡ k)))


    lemma-CZ^-aHCZ^k'-dual : ∀ (a* k* : ℤ* ₚ) →
      let
        k : ℤ ₚ
        k = k* .proj₁
        a : ℤ ₚ
        a = a* .proj₁
        -k : ℤ ₚ
        -k = - k
        k⁻¹ : ℤ ₚ
        k⁻¹ = ((k* ⁻¹) .proj₁)
        -k⁻¹ : ℤ ₚ
        -k⁻¹ = - k⁻¹
      in

      CZ^ a • H ↑ • CZ^ k ≈ S^ (-k⁻¹ * a) ↑ • H ↑ • CZ^ k • H ↑ ^ 3 • S^ (k⁻¹ * a) ↑ • H ↑ • S^ (-k * a)
      
    lemma-CZ^-aHCZ^k'-dual a*@(a , nza) k*@(k , nzk) = by-duality' (lemma-CZ^-aHCZ^k' a* k*) aux1 aux2
      where
      j : ℕ
      j = toℕ a
      -k : ℤ ₚ
      -k = - k
      k⁻¹ : ℤ ₚ
      k⁻¹ = ((k* ⁻¹) .proj₁)
      -k⁻¹ : ℤ ₚ
      -k⁻¹ = - k⁻¹

      aux1 : dual (CZ^ a) • H ↑ • dual (CZ^ k) ≈ (CZ^ a • H ↑ • CZ^ k)
      aux1 = begin
        dual (CZ^ a) • H ↑ • dual (CZ^ k) ≈⟨ cong (refl' (aux-dual-CZ^k (toℕ a))) (cright refl' (aux-dual-CZ^k (toℕ k))) ⟩
        (CZ^ a • H ↑ • CZ^ k) ∎


      aux2 : dual (S^ (-k⁻¹ * a) • H • CZ^ k • H ^ 3 • S^ (k⁻¹ * a) • H • S^ (-k * a) ↑) ≈ S^ (-k⁻¹ * a) ↑ • H ↑ • CZ^ k • H ↑ ^ 3 • S^ (k⁻¹ * a) ↑ • H ↑ • S^ (-k * a)
      aux2 = begin
        dual (S^ (-k⁻¹ * a) • H • CZ^ k • H ^ 3 • S^ (k⁻¹ * a) • H • S^ (-k * a) ↑) ≈⟨ cong (refl' (aux-dual-S^k (toℕ (-k⁻¹ * a)))) (cright cong (refl' (aux-dual-CZ^k (toℕ k))) (cright cong (refl' (aux-dual-S^k (toℕ (k⁻¹ * a)))) (cright refl' (aux-dual-S^k↑ (toℕ (-k * a)))))) ⟩
        S^ (-k⁻¹ * a) ↑ • H ↑ • CZ^ k • H ↑ ^ 3 • S^ (k⁻¹ * a) ↑ • H ↑ • S^ (-k * a) ∎

