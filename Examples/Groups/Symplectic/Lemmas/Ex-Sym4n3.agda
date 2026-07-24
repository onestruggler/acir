{-# OPTIONS --cubical-compatible --safe #-}
--{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Ex-Sym4n3 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ)  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime

open Symplectic
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n p-2 p-prime as Sym4n
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n2 p-2 p-prime as Sym4n2
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime as Sym2n hiding (lemma-XCS^k')

open import Examples.Groups.Symplectic.Lemmas.Ex-Rewriting p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0
open import Examples.Groups.Symplectic.Lemmas.Lemma-Postfix p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Duality p-2 p-prime hiding (module L0)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open LM2
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()


open Symplectic
open Lemmas-Sym
open Symplectic-GroupLike

open import Data.Nat.DivMod
open import Data.Fin.Properties
open Duality

open import Algebra.Properties.Ring (+-*-ring p-2)
open PB ((₃₊ n) QRel,_===_)
open PP ((₃₊ n) QRel,_===_)
open SR word-setoid
module P1 = PP ((₂₊ n) QRel,_===_)
open Pattern-Assoc
open Lemmas0 (₂₊ n)
open Commuting-Symplectic (₁₊ n)
open Sym0-Rewriting (₂₊ n)
open Basis-Change _ ((₃₊ n) QRel,_===_) grouplike
import Examples.Groups.Symplectic.Lemmas.Duality p-2 p-prime as ND
open Rewriting-Powers (₂₊ n)
open Rewriting-Swap (₂₊ n)
open import Examples.Groups.Symplectic.Lemmas.XEX-Rewriting p-2 p-prime
open Rewriting-EX (₂₊ n)
open Homo (₃₊ n)

lemma-comm-CZ↑-CZ02⁻¹ : 
  CZ ↑ • CZ02⁻¹ ≈ CZ02⁻¹ • CZ ↑
lemma-comm-CZ↑-CZ02⁻¹ = begin
  CZ ↑ • CZ02⁻¹ ≈⟨ (cright aux-CZ02⁻¹) ⟩
  CZ ↑ • CZ02 ^ p-1 ≈⟨ comm⇒pow-comm 1 p-1 lemma-comm-CZ↑-CZ02 ⟩
  CZ02 ^ p-1 • CZ ↑ ≈⟨ (cleft sym aux-CZ02⁻¹) ⟩
  CZ02⁻¹ • CZ ↑ ∎


lemma-XC-CZ : 
  XC • CZ ↑ ≈ CZ ↑ • CZ02⁻¹ • XC
lemma-XC-CZ = bbc (Ex • Ex ↑ • Ex) (Ex • Ex ↑ • Ex) aux
  where
  aux : (Ex • Ex ↑ • Ex) • (XC • CZ ↑) • Ex • Ex ↑ • Ex ≈ (Ex • Ex ↑ • Ex) • (CZ ↑ • CZ02⁻¹ • XC) • Ex • Ex ↑ • Ex
  aux = begin
    (Ex • Ex ↑ • Ex) • (XC • CZ ↑) • Ex • Ex ↑ • Ex ≈⟨ by-ex {w = (EX.Ex • EX.Ex EX.↑ • EX.Ex) • (EX.XC • EX.CZ EX.↑) • EX.Ex • EX.Ex EX.↑ • EX.Ex} {v = EX.CX EX.↑ • EX.CZ} (rewrite-EX 100 auto)  ⟩
    CX ↑ • CZ ≈⟨ lemma-CX↑-CZ ⟩
    CZ • CZ02⁻¹ • CX ↑ ≈⟨ by-passoc (□ • □ ^ 3 • □) (□ ^ 2 • □ • □ ^ 2) auto ⟩
    (CZ • Ex) • (CZ⁻¹) ↑ • Ex • CX ↑ ≈⟨ cright cleft sym (trans (sym assoc) (trans (cleft lemma-cong↑ _ _ lemma-order-Ex-n) left-unit)) ⟩
    (CZ • Ex) • (Ex • Ex • CZ⁻¹) ↑ • Ex • CX ↑ ≈⟨ sym (cright cleft cright lemma-cong↑ _ _ (P1.comm⇒pow-comm p-1 1 lemma-comm-Ex-CZ-n)) ⟩
    (CZ • Ex) • (Ex • CZ⁻¹ • Ex) ↑ • Ex • CX ↑ ≈⟨ by-passoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ ^ 3 • □ • □ ^ 3) auto ⟩
    (CZ • Ex • Ex ↑) • CZ⁻¹ ↑ • Ex ↑ • Ex • CX ↑ ≈⟨  cong (rewrite-powers 100 auto) (cright rewrite-powers 100 auto) ⟩
    (CZ • Ex • Ex ↑ • Ex • Ex) • CZ⁻¹ ↑ • Ex • Ex • Ex ↑ • Ex • CX ↑ ≈⟨  by-passoc (□ ^ 5 • □ • □ ^ 5) (□ ^ 4 • □ ^ 3 • □ ^ 4) auto ⟩
    (CZ • Ex • Ex ↑ • Ex) • CZ02⁻¹ • Ex • Ex ↑ • Ex • CX ↑ ≈⟨ cright cright by-ex {w = EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.CX EX.↑} {v = EX.XC • EX.Ex • EX.Ex EX.↑ • EX.Ex} (rewrite-EX 100 auto) ⟩
    (CZ • Ex • Ex ↑ • Ex) • CZ02⁻¹ • XC • Ex • Ex ↑ • Ex ≈⟨ cleft by-ex {w = EX.CZ • EX.Ex • EX.Ex EX.↑ • EX.Ex} {v = EX.Ex • EX.Ex EX.↑ • EX.Ex • EX.CZ EX.↑} (rewrite-EX 100 auto) ⟩
    
    (Ex • Ex ↑ • Ex • CZ ↑) • CZ02⁻¹ • XC • Ex • Ex ↑ • Ex ≈⟨ by-passoc (□ ^ 4 • □ ^ 5) (□ ^ 3 • □ ^ 3 • □ ^ 3) auto ⟩
    (Ex • Ex ↑ • Ex) • (CZ ↑ • CZ02⁻¹ • XC) • Ex • Ex ↑ • Ex ∎

lemma-XC-CZ^k : ∀ k ->
  XC • CZ ↑ ^ k ≈ CZ ↑ ^ k • CZ02⁻ᵏ k • XC
lemma-XC-CZ^k k@0 = rewrite-powers 100 auto
lemma-XC-CZ^k k@1 = lemma-XC-CZ
lemma-XC-CZ^k k@(₁₊ k'@(₁₊ k'')) = begin
  (XC) • CZ ↑ ^ ₂₊ k'' ≈⟨ sym assoc ⟩
  (XC • CZ ↑) • CZ ↑ ^ k' ≈⟨ (cleft lemma-XC-CZ) ⟩
  (CZ ↑ • CZ02⁻¹ • XC) • CZ ↑ ^ k' ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (CZ ↑ • CZ02⁻¹) • XC • CZ ↑ ^ k' ≈⟨ (cright lemma-XC-CZ^k k' ) ⟩
  (CZ ↑ • CZ02⁻¹) • CZ ↑ ^ k' • CZ02⁻ᵏ k' • XC ≈⟨ by-passoc (□ ^ 2 • □ ^ 3) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  CZ ↑ • (CZ02⁻¹ • CZ ↑ ^ k') • CZ02⁻ᵏ k' • XC ≈⟨ (cright cleft comm⇒pow-comm 1 k' (sym lemma-comm-CZ↑-CZ02⁻¹)) ⟩
  CZ ↑ • (CZ ↑ ^ k' • CZ02⁻¹) • CZ02⁻ᵏ k' • XC ≈⟨ by-passoc (□ • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
  (CZ ↑ • CZ ↑ ^ k') • (CZ02⁻¹ • CZ02⁻ᵏ k') • XC ≈⟨ (cright cleft aux-CZ02⁻ᵏ k') ⟩
  (CZ ↑ • CZ ↑ ^ k') • (CZ02⁻ᵏ (₁₊ k')) • XC ≈⟨ refl ⟩
  CZ ↑ ^ ₂₊ k'' • CZ02⁻ᵏ (₂₊ k'') • (XC) ∎
  where
  open Rewriting-Powers (₂₊ n)
  open Commuting-Symplectic (₁₊ n)
  open Sym0-Rewriting (₂₊ n)
  open Rewriting-Swap (₁₊ n)
  open Basis-Change _ ((₃₊ n) QRel,_===_) grouplike


aux-XC^p : XC⁻¹ • XC ≈ ε
aux-XC^p = begin
  XC⁻¹ • XC ≈⟨ refl ⟩
  (H ↑ ^ 3 • CZ^ (- ₁) • H ↑) • H ↑ ^ 3 • CZ • H ↑ ≈⟨ by-passoc (□ ^ 3 • □ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ ^ 3 • CZ^ (- ₁)) • H ↑ ^ 4 • CZ • H ↑ ≈⟨ cright trans (cong (axiom (cong↑ order-H)) refl) left-unit ⟩
  (H ↑ ^ 3 • CZ^ (- ₁)) • CZ • H ↑ ≈⟨ sym (trans (by-assoc auto) assoc) ⟩
  H ↑ ^ 3 • (CZ^ (- ₁) • CZ) • H ↑ ≈⟨ cright cleft lemma-CZ^k+l (- ₁) ₁ ⟩
  H ↑ ^ 3 • CZ^ (- ₁ + ₁) • H ↑ ≈⟨ cright cleft refl' (Eq.cong CZ^ (+-inverseˡ ₁)) ⟩
  H ↑ ^ 3 • ε • H ↑ ≈⟨ rewrite-powers 100 auto ⟩
  ε ∎
  where
  open Lemmas-2Q (₁₊ n)

aux-XC^p' : XC • XC⁻¹ ≈ ε
aux-XC^p' = begin
  XC • XC⁻¹ ≈⟨ refl ⟩
  (H ↑ ^ 3 • CZ • H ↑) • H ↑ ^ 3 • CZ^ (- ₁) • H ↑ ≈⟨ by-passoc (□ ^ 3 • □ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 4 • □ ^ 2) auto ⟩
  (H ↑ ^ 3 • CZ) • H ↑ ^ 4 • CZ^ (- ₁) • H ↑ ≈⟨ cright trans (cong (axiom (cong↑ order-H)) refl) left-unit ⟩
  (H ↑ ^ 3 • CZ) • CZ^ (- ₁) • H ↑ ≈⟨ sym (trans (by-assoc auto) assoc) ⟩
  H ↑ ^ 3 • (CZ • CZ^ (- ₁)) • H ↑ ≈⟨ cright cleft lemma-CZ^k+l ₁ (- ₁) ⟩
  H ↑ ^ 3 • CZ^ (₁ + - ₁) • H ↑ ≈⟨ cright cleft refl' (Eq.cong CZ^ (+-inverseʳ ₁)) ⟩
  H ↑ ^ 3 • ε • H ↑ ≈⟨ rewrite-powers 100 auto ⟩
  ε ∎
  where
  open Lemmas-2Q (₁₊ n)


aux-inv-CZ02k : ∀ k -> CZ02k k • CZ02⁻ᵏ k ≈ ε
aux-inv-CZ02k k = begin
  CZ02k k • CZ02⁻ᵏ k ≈⟨ refl ⟩
  (Ex • CZ ↑ ^ k • Ex) • (Ex • CZ⁻¹ ↑ ^ k • Ex) ≈⟨ by-passoc (□ ^ 3 • □ ^ 3) ((□ ^ 2) ^ 3) auto ⟩
  (Ex • CZ ↑ ^ k) • Ex ^ 2 • (CZ⁻¹ ↑ ^ k • Ex) ≈⟨ cright trans (cleft lemma-order-Ex-n) left-unit ⟩
  (Ex • CZ ↑ ^ k) • (CZ⁻¹ ↑ ^ k • Ex) ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ ↑ ^ k • CZ⁻¹ ↑ ^ k) • Ex ≈⟨ cright cleft cright refl' (lemma-^-↑ CZ⁻¹ k) ⟩
  Ex • (CZ ↑ ^ k • (CZ⁻¹ ^ k) ↑) • Ex ≈⟨ cright cleft cleft refl' (lemma-^-↑ CZ k) ⟩
  Ex • ((CZ ^ k) ↑ • (CZ⁻¹ ^ k) ↑) • Ex ≈⟨ sym (cright cleft lemma-cong↑ _ _ (P1.^-• _ _ k (P1.comm⇒pow-comm 1 p-1 PB.refl))) ⟩
  Ex • ((CZ • CZ⁻¹) ^ k) ↑ • Ex ≈⟨ cright cleft lemma-cong↑ _ _ (P1.^-cong _ _ k (PB.axiom order-CZ)) ⟩
  Ex • (ε ^ k) ↑ • Ex ≈⟨ cright cleft lemma-cong↑ _ _ (P1.ε^k=ε k) ⟩
  Ex • ε • Ex ≈⟨ cright left-unit ⟩
  Ex • Ex ≈⟨ lemma-order-Ex-n ⟩
  ε ∎

comm-CX-CZ↑ : CX • CZ ↑ ≈ CZ ↑ • CX
comm-CX-CZ↑ = general-comm auto

comm-CX-CZ⁻¹↑ : CX • CZ⁻¹ ↑ ≈ CZ⁻¹ ↑ • CX
comm-CX-CZ⁻¹↑ = begin
  CX • CZ⁻¹ ↑ ≈⟨ cright sym (refl' (lemma-^-↑ CZ p-1)) ⟩
  CX • CZ ↑ ^ p-1 ≈⟨ comm⇒pow-comm 1 p-1 comm-CX-CZ↑ ⟩
  CZ ↑ ^ p-1 • CX ≈⟨ cleft refl' (lemma-^-↑ CZ p-1) ⟩
  CZ⁻¹ ↑ • CX ∎

aux-comm-XC-CZ02⁻ᵏ : ∀ k -> XC • CZ02⁻ᵏ k ≈ CZ02⁻ᵏ k • XC
aux-comm-XC-CZ02⁻ᵏ k = begin
  XC • Ex • CZ⁻¹ ↑ ^ k • Ex ≈⟨ sym assoc ⟩
  (XC • Ex) • CZ⁻¹ ↑ ^ k • Ex ≈⟨ cleft rewrite-swap 100 auto ⟩
  (Ex • CX) • CZ⁻¹ ↑ ^ k • Ex ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CX • CZ⁻¹ ↑ ^ k) • Ex ≈⟨ cright cleft comm⇒pow-comm 1 k comm-CX-CZ⁻¹↑ ⟩
  Ex • (CZ⁻¹ ↑ ^ k • CX) • Ex ≈⟨ cright assoc ⟩
  Ex • CZ⁻¹ ↑ ^ k • CX • Ex ≈⟨ cright cright rewrite-swap 100 auto ⟩
  Ex • CZ⁻¹ ↑ ^ k • Ex • XC ≈⟨ cright sym assoc ⟩
  Ex • (CZ⁻¹ ↑ ^ k • Ex) • XC ≈⟨ by-passoc (□ • □ ^ 2 • □ ) (□ ^ 3 • □) auto ⟩
  CZ02⁻ᵏ k • XC ∎

lemma-XC⁻¹-CZ^k : ∀ k ->
  XC⁻¹ • CZ ↑ ^ k ≈ CZ ↑ ^ k • CZ02k k • XC⁻¹
lemma-XC⁻¹-CZ^k k = bbc XC XC aux
  where
  open Rewriting-Powers (₂₊ n)
  open Commuting-Symplectic (₁₊ n)
  open Sym0-Rewriting (₂₊ n)
  open Rewriting-Swap (₁₊ n)
  open Lemmas-2Q (₁₊ n)

  aux0 : ε • ((CZ ↑) ^ k • XC) • CZ02⁻ᵏ k ≈ ε • (XC • (CZ ↑) ^ k • CZ02k k) • CZ02⁻ᵏ k
  aux0 = begin
    ε • ((CZ ↑) ^ k • XC) • CZ02⁻ᵏ k ≈⟨ left-unit ⟩
    ((CZ ↑) ^ k • XC) • CZ02⁻ᵏ k ≈⟨ assoc ⟩
    (CZ ↑) ^ k • XC • CZ02⁻ᵏ k ≈⟨ cright aux-comm-XC-CZ02⁻ᵏ k ⟩
    (CZ ↑) ^ k • CZ02⁻ᵏ k • XC ≈⟨ sym (lemma-XC-CZ^k k) ⟩
    (XC • (CZ ↑) ^ k) ≈⟨ sym right-unit ⟩
    (XC • (CZ ↑) ^ k) • ε ≈⟨ cright sym (aux-inv-CZ02k k) ⟩
    (XC • (CZ ↑) ^ k) • CZ02k k • CZ02⁻ᵏ k ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    (XC • (CZ ↑) ^ k • CZ02k k) • CZ02⁻ᵏ k ≈⟨ sym left-unit ⟩
    ε • (XC • (CZ ↑) ^ k • CZ02k k) • CZ02⁻ᵏ k ∎
    
  aux : XC • (XC⁻¹ • (CZ ↑) ^ k) • XC ≈ XC • ((CZ ↑) ^ k • CZ02k k • XC⁻¹) • XC
  aux = begin
    XC • (XC⁻¹ • (CZ ↑) ^ k) • XC ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (XC • XC⁻¹) • (CZ ↑) ^ k • XC ≈⟨ trans (cleft aux-XC^p') left-unit ⟩
    (CZ ↑) ^ k • XC ≈⟨ bbc ε (CZ02⁻ᵏ k) aux0 ⟩
    XC • ((CZ ↑) ^ k • CZ02k k) ≈⟨ cright sym (trans (cright aux-XC^p) right-unit) ⟩
    XC • ((CZ ↑) ^ k • CZ02k k) • XC⁻¹ • XC ≈⟨ cright by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
    XC • ((CZ ↑) ^ k • CZ02k k • XC⁻¹) • XC ∎

lemma-comm-CZ02-H↑ : ∀ k -> CZ02k k • H ↑ ≈ H ↑ • CZ02k k
lemma-comm-CZ02-H↑ k = begin
  CZ02k k • H ↑ ≈⟨ trans assoc (cong refl assoc) ⟩
  Ex • CZ ↑ ^ k • Ex • H ↑ ≈⟨ cright cright lemma-Ex-H↑-n ⟩
  Ex • CZ ↑ ^ k • H • Ex ≈⟨ sym (cong refl assoc) ⟩
  Ex • (CZ ↑ ^ k • H) • Ex ≈⟨ cright cleft comm⇒pow-comm k 1 (sym (lemma-comm-H-w↑ CZ)) ⟩
  Ex • (H • CZ ↑ ^ k) • Ex ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • H) • CZ ↑ ^ k • Ex ≈⟨ cleft rewrite-swap 100 auto ⟩
  (H ↑ • Ex) • CZ ↑ ^ k • Ex ≈⟨ assoc ⟩
  H ↑ • CZ02k k ∎


lemma-CZ02-d : ∀ d k -> CZ02k k • [ d ]ᵈ ≈ [ d ]ᵈ • CZ ↑ ^ k

lemma-CZ02-d d@(₀ , b) k =  begin
  CZ02k k • [ d ]ᵈ ≈⟨ trans (by-assoc auto) assoc ⟩
  (Ex • CZ ↑ ^ k) • Ex • Ex • CZ^ (- b) ≈⟨  cright sym assoc ⟩
  (Ex • CZ ↑ ^ k) • (Ex • Ex) • CZ^ (- b) ≈⟨  cright cleft rewrite-swap 100 auto ⟩
  (Ex • CZ ↑ ^ k) • ε • CZ^ (- b) ≈⟨  cong refl left-unit ⟩
  (Ex • CZ ↑ ^ k) • CZ^ (- b) ≈⟨ assoc ⟩
  Ex • CZ ↑ ^ k • CZ^ (- b) ≈⟨ cright comm⇒pow-comm k (toℕ (- b)) (axiom selinger-c12) ⟩
  Ex • CZ^ (- b) • CZ ↑ ^ k ≈⟨ sym assoc ⟩
  [ d ]ᵈ • CZ ↑ ^ k ∎

lemma-CZ02-d d@(a@(₁₊ _) , b) k = begin
  CZ02k k • [ d ]ᵈ ≈⟨ trans (by-assoc auto) assoc ⟩
  (Ex • CZ ↑ ^ k) • Ex • Ex • CZ^ (- a) • H • S^ -b/a ≈⟨ sym (cong refl assoc) ⟩
  (Ex • CZ ↑ ^ k) • (Ex • Ex) • CZ^ (- a) • H • S^ -b/a ≈⟨  cright cleft rewrite-swap 100 auto ⟩
  (Ex • CZ ↑ ^ k) • ε • CZ^ (- a) • H • S^ -b/a ≈⟨  cong refl left-unit ⟩
  (Ex • CZ ↑ ^ k) • CZ^ (- a) • H • S^ -b/a ≈⟨  by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ ↑ ^ k • CZ^ (- a)) • H • S^ -b/a ≈⟨  cright cleft comm⇒pow-comm k (toℕ (- a)) (axiom selinger-c12) ⟩
  Ex • (CZ^ (- a) • CZ ↑ ^ k) • H • S^ -b/a ≈⟨  sym (by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (Ex • CZ^ (- a)) • CZ ↑ ^ k • H • S^ -b/a ≈⟨  cright cleft refl' (lemma-^-↑ CZ k) ⟩
  (Ex • CZ^ (- a)) • (CZ ^ k) ↑ • H • S^ -b/a ≈⟨  sym (cright comm-hs-w↑ -b/a (CZ ^ k)) ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • (CZ ^ k) ↑ ≈⟨  by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (Ex • CZ^ (- a) • (H • S^ -b/a)) • (CZ ^ k) ↑ ≈⟨  cright sym (refl' (lemma-^-↑ CZ k)) ⟩
  [ d ]ᵈ • CZ ↑ ^ k ∎
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

{-
lemma-CZ02-d : ∀ d k -> CZ02k k • [ d ]ᵈ ≈ [ d ]ᵈ • CZ ↑ ^ k
lemma-CZ02-d d@(₀ , ₀) k = begin
  CZ02k k • [ d ]ᵈ ≈⟨ trans (by-assoc auto) assoc ⟩
  (Ex • CZ ↑ ^ k) • Ex • [ d ]ᵈ ≈⟨ cright rewrite-swap 100 auto ⟩
  (Ex • CZ ↑ ^ k) • ε ≈⟨ right-unit ⟩
  [ d ]ᵈ • CZ ↑ ^ k ∎

lemma-CZ02-d d@(₀ , ₁₊ _) k = begin
  CZ02k k • [ d ]ᵈ ≈⟨ trans (by-assoc auto) assoc ⟩
  (Ex • CZ ↑ ^ k) • Ex • Ex • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  cright sym assoc ⟩
  (Ex • CZ ↑ ^ k) • (Ex • Ex) • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  cright cleft rewrite-swap 100 auto ⟩
  (Ex • CZ ↑ ^ k) • ε • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  cong refl left-unit ⟩
  (Ex • CZ ↑ ^ k) • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ ↑ ^ k • CZ^ (- ₁)) • [ d , (λ ()) ]ᵃ ≈⟨  cright cleft comm⇒pow-comm k (toℕ (- ₁)) (axiom selinger-c12) ⟩
  Ex • (CZ^ (- ₁) • CZ ↑ ^ k) • [ d , (λ ()) ]ᵃ ≈⟨  sym (by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (Ex • CZ^ (- ₁)) • CZ ↑ ^ k • [ d , (λ ()) ]ᵃ ≈⟨  cright cleft refl' (lemma-^-↑ CZ k) ⟩
  (Ex • CZ^ (- ₁)) • (CZ ^ k) ↑ • [ d , (λ ()) ]ᵃ ≈⟨  sym (cright comm-abox-w↑ (d , (λ ())) (CZ ^ k)) ⟩
  (Ex • CZ^ (- ₁)) • [ d , (λ ()) ]ᵃ • (CZ ^ k) ↑ ≈⟨  by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (Ex • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ) • (CZ ^ k) ↑ ≈⟨  cright sym (refl' (lemma-^-↑ CZ k)) ⟩
  [ d ]ᵈ • CZ ↑ ^ k ∎

lemma-CZ02-d d@(₁₊ _ , _) k = begin
  CZ02k k • [ d ]ᵈ ≈⟨ trans (by-assoc auto) assoc ⟩
  (Ex • CZ ↑ ^ k) • Ex • Ex • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  cright sym assoc ⟩
  (Ex • CZ ↑ ^ k) • (Ex • Ex) • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  cright cleft rewrite-swap 100 auto ⟩
  (Ex • CZ ↑ ^ k) • ε • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  cong refl left-unit ⟩
  (Ex • CZ ↑ ^ k) • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ ≈⟨  by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  Ex • (CZ ↑ ^ k • CZ^ (- ₁)) • [ d , (λ ()) ]ᵃ ≈⟨  cright cleft comm⇒pow-comm k (toℕ (- ₁)) (axiom selinger-c12) ⟩
  Ex • (CZ^ (- ₁) • CZ ↑ ^ k) • [ d , (λ ()) ]ᵃ ≈⟨  sym (by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto) ⟩
  (Ex • CZ^ (- ₁)) • CZ ↑ ^ k • [ d , (λ ()) ]ᵃ ≈⟨  cright cleft refl' (lemma-^-↑ CZ k) ⟩
  (Ex • CZ^ (- ₁)) • (CZ ^ k) ↑ • [ d , (λ ()) ]ᵃ ≈⟨  sym (cright comm-abox-w↑ (d , (λ ())) (CZ ^ k)) ⟩
  (Ex • CZ^ (- ₁)) • [ d , (λ ()) ]ᵃ • (CZ ^ k) ↑ ≈⟨  by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 3 • □) auto ⟩
  (Ex • CZ^ (- ₁) • [ d , (λ ()) ]ᵃ) • (CZ ^ k) ↑ ≈⟨  cright sym (refl' (lemma-^-↑ CZ k)) ⟩
  [ d ]ᵈ • CZ ↑ ^ k ∎

-}
