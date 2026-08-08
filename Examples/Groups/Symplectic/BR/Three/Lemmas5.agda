{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)


open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP



open import Data.Fin using (toℕ)
open import Presentation.GroupLike
open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.Three.Lemmas5 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic

open import Algebra.Properties.Ring (+-*-ring p-2)


open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
--open Lemmas-2Q 2

--open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime hiding (module L0)

open Lemmas-Sym

--open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime renaming (module Completeness to CP2) using ()
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime as L4 hiding (lemma-Ex-M-n)
open import Examples.Groups.Symplectic.BR.Calculations p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.Lemmas p-2 p-prime hiding (sa)
open import Examples.Groups.Symplectic.BR.Three.Lemmas p-2 p-prime
open import Examples.Groups.Symplectic.BR.Three.Lemmas3 p-2 p-prime
open import Examples.Groups.Symplectic.BR.Three.Lemmas4 p-2 p-prime

open PB (3 QRel,_===_)
open PP (3 QRel,_===_)
-- module B2 = PB (2 QRel,_===_)
-- module P2 = PP (2 QRel,_===_)
-- module B1 = PB (1 QRel,_===_)
-- module P1 = PP (1 QRel,_===_)

open Pattern-Assoc
open Lemmas0 1
--module L02 = Lemmas0 2
open Lemmas-2Q 1
module L2Q1 = Lemmas-2Q 1
--module Sym01 = Sym0-Rewriting 1
open Symplectic-GroupLike
open Basis-Change _ (3 QRel,_===_) grouplike



lemma-CZ02^k-CZ^l↑-CZ : ∀ (k*@(k , nzk) l*@(l , nzl) : ℤ* ₚ) ->
  let
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  in
  CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ ≈ H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑
  
lemma-CZ02^k-CZ^l↑-CZ k*@(k , nzk) l*@(l , nzl) = bbc (M (k* ⁻¹) • M (l* ⁻¹) ↑) ε claim
  where
  k⁻¹ = (k* ⁻¹) .proj₁
  l⁻¹ = (l* ⁻¹) .proj₁
  aux2 : l * k * (l⁻¹ * l⁻¹) ≡ k * l⁻¹
  aux2 = begin
    l * k * (l⁻¹ * l⁻¹) ≡⟨ Eq.cong (_* (l⁻¹ * l⁻¹)) (*-comm l k) ⟩
    k * l * (l⁻¹ * l⁻¹) ≡⟨ aux-lkkk l* k* ⟩
    k * l⁻¹ ∎
    where
    open ≡-Reasoning

  open SR word-setoid
  claim : (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ) • ε ≈ (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑) • ε
  claim = begin
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ) • ε ≈⟨ cong refl right-unit ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (CZ02^ (- k) • H • CZ^ (- l) ↑ • H ↑ • CZ) ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    M (k* ⁻¹) • (M (l* ⁻¹) ↑ • CZ02^ (- k)) • H • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ cright cleft aux-comm-m-CZ02^k (l* ⁻¹) (- k) ⟩
    M (k* ⁻¹) • (CZ02^ (- k) • M (l* ⁻¹) ↑) • H • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (M (k* ⁻¹) • CZ02^ (- k)) • (M (l* ⁻¹) ↑ • H) • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ cong (lemma-M↓CZ02^k k⁻¹ (- k) ((k* ⁻¹) .proj₂)) (cleft sym (lemma-comm-H-w↑ ( M (l* ⁻¹)))) ⟩
    (CZ02^ (- k * k⁻¹) • M (k* ⁻¹)) • (H • M (l* ⁻¹) ↑) • CZ^ (- l) ↑ • H ↑ • CZ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
    CZ02^ (- k * k⁻¹) • (M (k* ⁻¹) • H) • (M (l* ⁻¹) ↑ • CZ^ (- l) ↑) • H ↑ • CZ ≈⟨ cright cong (sym (L02.semi-HM k*)) (cleft lemma-cong↑ _ _ (L2Q0.lemma-M↓CZ^k l⁻¹ (- l) ((l* ⁻¹) .proj₂))) ⟩
    CZ02^ (- k * k⁻¹) • (H • M k*) • (CZ^ (- l * l⁻¹) ↑ • M (l* ⁻¹) ↑) • H ↑ • CZ ≈⟨ cong (refl' (Eq.cong CZ02^ (Eq.trans (Eq.sym (-‿distribˡ-* k k⁻¹)) (Eq.cong -_ (lemma-⁻¹ʳ k {{nztoℕ {y = k} {neq0 = nzk}}}))))) (cright cleft cleft refl' (Eq.cong (\ xx -> CZ^ xx ↑) ((Eq.trans (Eq.sym (-‿distribˡ-* l l⁻¹)) (Eq.cong -_ (lemma-⁻¹ʳ l {{nztoℕ {y = l} {neq0 = nzl}}})))))) ⟩
    CZ02^ (- ₁) • (H • M k*) • (CZ^ (- ₁) ↑ • M (l* ⁻¹) ↑) • H ↑ • CZ ≈⟨ cright sa (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ ^ 2 • □) auto ⟩
    CZ02^ (- ₁) • H • (M k* • CZ^ (- ₁) ↑) • (M (l* ⁻¹) ↑ • H ↑) • CZ ≈⟨ cright cright cong (aux-comm-m-w↑ k* (CZ^ (- ₁))) (cleft lemma-cong↑ _ _ (B2.sym (semi-HM l*))) ⟩
    CZ02^ (- ₁) • H • (CZ^ (- ₁) ↑ • M k*) • (H ↑ • M l* ↑) • CZ ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • (M k* • H ↑) • M l* ↑ • CZ ≈⟨ cright cright cright cong (aux-comm-m-w↑ k* H) (axiom (semi-M↑CZ l*)) ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • (H ↑ • M k*) • CZ^ l • M l* ↑ ≈⟨ cright cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • (M k* • CZ^ l) • M l* ↑ ≈⟨ cright cright cright cright (cleft lemma-M↓CZ^k k l nzk) ⟩
    CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • (CZ^ (l * k) • M k*) • M l* ↑ ≈⟨ sa (□ • □ • □ • □ • □ ^ 2 • □) (□ ^ 5 • □ ^ 2) auto ⟩

    
    (CZ02^ (- ₁) • H • CZ^ (- ₁) ↑ • H ↑ • CZ^ (l * k)) • M k* • M l* ↑ ≈⟨ cleft lemma-CZ02⁻¹-CZ⁻¹↑-CZ^k (l * k) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁) • S^ (l * k) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑ • S^ (l * k) ↑)) • M k* • M l* ↑ ≈⟨ sa (□ ^ 9 • □ ^ 2) (□ ^ 6 • (□ ^ 3 • □) • □) auto ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁) • S^ (l * k)) • ((S^ (- (l * k)) ↑ • CX^ (- ₁) ↑ • S^ (l * k) ↑) • M k*) • M l* ↑ ≈⟨ cright cleft sym (aux-comm-m-w↑ k* (S^ (- (l * k)) • CX^ (- ₁) • S^ (l * k))) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁) • S^ (l * k)) • (M k* • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑ • S^ (l * k) ↑)) • M l* ↑ ≈⟨ sa ((□ ^ 6 • (□ ^ 4) • □)) (□ ^ 5 • □ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁)) • (S^ (l * k) • M k*) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑) • S^ (l * k) ↑ • M l* ↑ ≈⟨ cright cong (L02.lemma-S^kM k (l * k) nzk) (cright lemma-cong↑ _ _ (lemma-S^kM l (l * k) nzl)) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁)) • (M k* • S^ (l * k * (k⁻¹ * k⁻¹))) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑) • M l* ↑ • S^ (l * k * (l⁻¹ * l⁻¹)) ↑ ≈⟨ cright cong (cright refl' (Eq.cong S^ (aux-lkkk k* l*))) (cright cright refl' (Eq.cong (\ xx -> S^ xx ↑) aux2)) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k)) • CX02^ (- ₁)) • (M k* • S^ (l * k⁻¹)) • (S^ (- (l * k)) ↑ • CX^ (- ₁) ↑) • M l* ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 5 • □ ^ 2 • □ ^ 2 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □ • □ • □ ^ 2 • □) auto ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k))) • (CX02^ (- ₁) • M k*) • S^ (l * k⁻¹) • S^ (- (l * k)) ↑ • (CX^ (- ₁) ↑ • M l* ↑) • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (aux-CX02^kM↓ k* (- ₁)) (cright cright cleft lemma-cong↑ _ _ (aux-CX^kM↓ (- ₁) l*)) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k))) • (M k* • CX02^ (- ₁ * k)) • S^ (l * k⁻¹) • S^ (- (l * k)) ↑ • (M l* ↑ • CX^ (- ₁ * l) ↑) • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (cright refl' (Eq.cong CX02^ (-1*x≈-x k))) (cright cright cleft cright refl' (Eq.cong (\ xx -> CX^ xx ↑) (-1*x≈-x l))) ⟩
    (H • H ↑ • CZ^ (l * k) • S^ (- (l * k))) • (M k* • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (l * k)) ↑ • (M l* ↑ • CX^ (- l) ↑) • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 4 • □ ^ 2 • □ • □ • □ ^ 2 • □) (□ ^ 3 • □ ^ 2 • □ • □ • □ ^ 2 • □ ^ 2) auto ⟩
    (H • H ↑ • CZ^ (l * k)) • (S^ (- (l * k)) • M k*) • CX02^ (- k) • S^ (l * k⁻¹) • (S^ (- (l * k)) ↑ • M l* ↑) • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (L02.lemma-S^kM k (- (l * k)) nzk) (cright cright cleft lemma-cong↑ _ _ (lemma-S^kM l (- (l * k)) nzl)) ⟩
    (H • H ↑ • CZ^ (l * k)) • (M k* • S^ (- (l * k) * (k⁻¹ * k⁻¹))) • CX02^ (- k) • S^ (l * k⁻¹) • (M l* ↑ • S^ (- (l * k) * (l⁻¹ * l⁻¹)) ↑) • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (cright refl' (Eq.cong S^ (Eq.trans (Eq.sym (-‿distribˡ-* (l * k) (k⁻¹ * k⁻¹))) (Eq.cong -_ (aux-lkkk k* l*))))) (cright cright cleft cright refl' (Eq.cong (\ xx -> S^ xx ↑) (Eq.trans (Eq.sym (-‿distribˡ-* (l * k) (l⁻¹ * l⁻¹))) (Eq.cong -_ aux2)))) ⟩
    (H • H ↑ • CZ^ (l * k)) • (M k* • S^ (- (l * k⁻¹))) • CX02^ (- k) • S^ (l * k⁻¹) • (M l* ↑ • S^ (- (k * l⁻¹)) ↑) • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa ((□ ^ 3 • □ ^ 2 • □ • □ • □ ^ 2 • □ ^ 2)) (□ ^ 2 • □ ^ 2 • □ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H ↑) • (CZ^ (l * k) • M k*) • S^ (- (l * k⁻¹)) • CX02^ (- k) • (S^ (l * k⁻¹) • M l* ↑) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (sym (L2Q1.lemma-M↓CZ^k k l nzk)) (cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ (l * k⁻¹)) (M l*)) ⟩
    (H • H ↑) • (M k* • CZ^ l) • S^ (- (l * k⁻¹)) • CX02^ (- k) • (M l* ↑ • S^ (l * k⁻¹)) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cright sa (□ • □ ^ 2 • □ ^ 3) (□ ^ 2 • □ ^ 4) auto ⟩
    (H • H ↑) • (M k* • CZ^ l) • S^ (- (l * k⁻¹)) • (CX02^ (- k) • M l* ↑) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cright cleft sym (aux-comm-m-CX02^k l* (- k)) ⟩
    (H • H ↑) • (M k* • CZ^ l) • S^ (- (l * k⁻¹)) • (M l* ↑ • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ • □ ^ 2 • □) (□ • □ ^ 2 • □ • □ • □ ^ 2 • □) auto ⟩
    H • (H ↑ • M k*) • CZ^ l • S^ (- (l * k⁻¹)) • (M l* ↑ • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cong (sym (aux-comm-m-w↑ k* H)) refl ⟩
    H • (M k* • H ↑) • CZ^ l • S^ (- (l * k⁻¹)) • (M l* ↑ • CX02^ (- k)) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ • □ ^ 2 • □ • □ • □ ^ 2 • □) (□ ^ 2 • □ • □ • □ ^ 2 • □ • □) auto ⟩
    (H • M k*) • H ↑ • CZ^ l • (S^ (- (l * k⁻¹)) • M l* ↑) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cong (L02.semi-HM k*) (cright cright cleft lemma-comm-Sᵏ-w↑ (toℕ (- (l * k⁻¹))) (M l*)) ⟩
    (M (k* ⁻¹) • H) • H ↑ • CZ^ l • (M l* ↑ • S^ (- (l * k⁻¹))) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright sa (□ • □ ^ 2 • □ ) (□ ^ 2 • □ ^ 2) auto ⟩
    (M (k* ⁻¹) • H) • H ↑ • (CZ^ l • M l* ↑) • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cleft sym (axiom (semi-M↑CZ l*)) ⟩
    (M (k* ⁻¹) • H) • H ↑ • (M l* ↑ • CZ) • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (M (k* ⁻¹) • H) • (H ↑ • M l* ↑) • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cleft lemma-cong↑ _ _ (semi-HM l*) ⟩
    (M (k* ⁻¹) • H) • (M (l* ⁻¹) ↑ • H ↑) • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    M (k* ⁻¹) • (H • M (l* ⁻¹) ↑) • H ↑ • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cleft lemma-comm-H-w↑ ( M (l* ⁻¹)) ⟩
    M (k* ⁻¹) • (M (l* ⁻¹) ↑ • H) • H ↑ • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sa (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • H • H ↑ • CZ • S^ (- (l * k⁻¹)) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- (k * l⁻¹)) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ cright cright cright cright cong (refl' (Eq.cong S^ (-‿distribˡ-* l k⁻¹))) (cright cright cleft refl' (Eq.cong (\ xx -> S^ xx ↑) (-‿distribˡ-* k l⁻¹))) ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑ ≈⟨ sym (cong refl right-unit) ⟩
    (M (k* ⁻¹) • M (l* ⁻¹) ↑) • (H • H ↑ • CZ • S^ (- l * k⁻¹) • CX02^ (- k) • S^ (l * k⁻¹) • S^ (- k * l⁻¹) ↑ • CX^ (- l) ↑ • S^ (k * l⁻¹) ↑) • ε ∎

