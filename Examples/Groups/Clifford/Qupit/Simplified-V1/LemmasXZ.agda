{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; setoid ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)
open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
open import Agda.Builtin.Nat using ()
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])


open import Data.Maybe
open import Data.Sum using ([_,_])
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.Tactic.Rewriting

open import Presentation.Construct.Base hiding (_*_)

import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open Bézout
open import Data.Empty
open import Algebra.Properties.Group
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module Examples.Groups.Clifford.Qupit.Simplified-V1.LemmasXZ
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

module Symplectic-Simplified where

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
-- Same hiding list as Part1: only Symplectic's generator layer is taken
-- (see Part1 for the full note).
open Symplectic hiding
  ( _QRel,_===_ ; M ; M₁ ; module Base
  ; order-S ; order-H ; order-SH
  ; semi-M↑CZ ; semi-M↓CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑
  ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15
  ; comm-H ; comm-S ; comm-CZ ; comm-HHS
  ; M-mul ; semi-MS
  ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ) public

1/2 = ((₂ , λ ()) ⁻¹) .proj₁

-1/2 = - ((₂ , λ ()) ⁻¹) .proj₁

open import Examples.Groups.Clifford.Qupit.Simplified-V1.Syntactics p-3 p-prime g* g-gen using (module Clifford-Relations ; module Lemmas-Clifford)
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Lemmas p-3 p-prime g* g-gen using (module Lemmas1 ; module Clifford-GroupLike)
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Tactics p-3 p-prime g* g-gen using (module Sim-Rewriting)

module Lemmas1b (n : ℕ) where

  open Clifford-Relations
  open Lemmas-Clifford
  open Lemmas1 n

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Clifford-GroupLike
  open import Data.Nat.DivMod
  open import Data.Fin.Properties

  aux-S⁻¹⁻¹ : 
    S⁻¹ ^ p-1 ≈ S
  aux-S⁻¹⁻¹ = •-cancelʳ {h = S⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : S⁻¹ ^ p-1 • S⁻¹ ≈ S • S⁻¹
    aux00 = begin
      S⁻¹ ^ p-1 • S⁻¹ ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
      S⁻¹ • S⁻¹ ^ p-1 ≈⟨ refl ⟩
      S⁻¹ ^ p ≈⟨ ^^ S p-1 p ⟩
      S ^ (p-1 Nat.* p) ≡⟨ Eq.cong (S ^_) (NP.*-comm p-1 p) ⟩
      S ^ (p Nat.* p-1) ≈⟨ sym (^^ S p p-1) ⟩
      (S ^ p) ^ p-1 ≈⟨ ^-cong (S ^ p) ε p-1 (axiom order-S) ⟩
      ε ^ p-1 ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ∎

  aux-Z⁻¹⁻¹ : 
    Z⁻¹ ^ p-1 ≈ Z
  aux-Z⁻¹⁻¹ = •-cancelʳ {h = Z⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : Z⁻¹ ^ p-1 • Z⁻¹ ≈ Z • Z⁻¹
    aux00 = begin
      Z⁻¹ ^ p-1 • Z⁻¹ ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
      Z⁻¹ • Z⁻¹ ^ p-1 ≈⟨ refl ⟩
      Z⁻¹ ^ p ≈⟨ ^^ Z p-1 p ⟩
      Z ^ (p-1 Nat.* p) ≡⟨ Eq.cong (Z ^_) (NP.*-comm p-1 p) ⟩
      Z ^ (p Nat.* p-1) ≈⟨ sym (^^ Z p p-1) ⟩
      (Z ^ p) ^ p-1 ≈⟨ ^-cong (Z ^ p) ε p-1 (lemma-order-Z) ⟩
      ε ^ p-1 ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (lemma-order-Z) ⟩
      Z • Z⁻¹ ∎

  aux-X⁻¹⁻¹ : 
    X⁻¹ ^ p-1 ≈ X
  aux-X⁻¹⁻¹ = •-cancelʳ {h = X⁻¹} aux00
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas ((₁₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹′)
    aux00 : X⁻¹ ^ p-1 • X⁻¹ ≈ X • X⁻¹
    aux00 = begin
      X⁻¹ ^ p-1 • X⁻¹ ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
      X⁻¹ • X⁻¹ ^ p-1 ≈⟨ refl ⟩
      X⁻¹ ^ p ≈⟨ ^^ X p-1 p ⟩
      X ^ (p-1 Nat.* p) ≡⟨ Eq.cong (X ^_) (NP.*-comm p-1 p) ⟩
      X ^ (p Nat.* p-1) ≈⟨ sym (^^ X p p-1) ⟩
      (X ^ p) ^ p-1 ≈⟨ ^-cong (X ^ p) ε p-1 (lemma-order-X) ⟩
      ε ^ p-1 ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε ≈⟨ sym (lemma-order-X) ⟩
      X • X⁻¹ ∎

  conj-H-X : H • X ≈ Z • H
  conj-H-X = begin
    H • X ≈⟨ by-assoc auto ⟩
    Z • H ∎

  conj-H-X^k : ∀ k -> H • X ^ k ≈ Z ^ k • H
  conj-H-X^k k@0 = by-assoc auto
  conj-H-X^k k@1 = conj-H-X
  conj-H-X^k k@(₁₊ k'@(₁₊ k'')) = begin
    H • X ^ k ≈⟨ sym assoc ⟩
    (H • X) • X ^ k' ≈⟨ (cleft conj-H-X) ⟩
    (Z • H) • X ^ k' ≈⟨ assoc ⟩
    Z • H • X ^ k' ≈⟨ (cright conj-H-X^k k') ⟩
    Z • Z ^ k' • H ≈⟨ sym assoc ⟩
    Z ^ k • H ∎


  lemma-HH-Z : HH • Z ≈ Z^ (- ₁) • HH
  lemma-HH-Z = begin
    HH • H • H • S • H • H • S⁻¹ ≈⟨ by-passoc (□ ^ 2 • □ ^ 6) (□ • □ • □ ^ 5 • □) auto ⟩
    H • H • (H • H • S • H • H) • S⁻¹ ≈⟨ (cright cright sym (comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH 1))) ⟩
    H • H • S⁻¹ • (H • H • S • H • H) ≈⟨ by-passoc (□ ^ 8) (□ ^ 6 • □ ^ 2) auto ⟩
    (H • H • S⁻¹ • H • H • S) • H • H ≈⟨ (cleft (cright cright cong (refl' (Eq.cong (S ^_) (Eq.sym lemma-toℕ-1ₚ))) (cright cright sym aux-S⁻¹⁻¹))) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ p-1) • HH ≈⟨ (cleft cright cright cright cright cright refl' (Eq.cong (S⁻¹ ^_) (Eq.sym lemma-toℕ-1ₚ))) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ (toℕ (- 1ₚ))) • HH ≈⟨ (cleft sym (lemma-Z^k-ℕ (toℕ (- 1ₚ)))) ⟩
    Z^ (- ₁) • HH ∎


  lemma-HH-X : HH • X ≈ X^ (- ₁) • HH
  lemma-HH-X = bbc H ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : H • (HH • X) • ε ≈ H • (X^ (- ₁) • HH) • ε
    claim = begin
      H • (HH • X) • ε ≈⟨ cong refl right-unit ⟩
      H • (HH • X) ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      HH • H • X ≈⟨ (cright conj-H-X) ⟩
      HH • Z • H ≈⟨ sym assoc ⟩
      (HH • Z) • H ≈⟨ (cleft lemma-HH-Z) ⟩
      (Z^ (- ₁) • HH) • H ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (Z^ (- ₁) • H) • HH ≈⟨ (cleft sym (conj-H-X^k (toℕ (- ₁)))) ⟩
      (H • X^ (- ₁)) • HH ≈⟨ assoc ⟩
      H • (X^ (- ₁) • HH) ≈⟨ sym (cong refl right-unit) ⟩
      H • (X^ (- ₁) • HH) • ε ∎

  conj-H-Z : H • Z ≈ X^ (- ₁) • H
  conj-H-Z = bbc (H ^ 3) H claim 
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : H ^ 3 • (H • Z) • H ≈ H ^ 3 • (X^ (- ₁) • H) • H
    claim = begin
      H ^ 3 • (H • Z) • H ≈⟨ by-assoc auto ⟩
      (H ^ 4) • Z • H ≈⟨ trans (cleft lemma-order-H) left-unit ⟩
      Z • H ≈⟨ sym conj-H-X ⟩
      H • X ≈⟨ cleft (sym (trans (cright lemma-order-H) right-unit)) ⟩
      H ^ 5 • X ≈⟨ by-passoc (□ ^ 5 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
      H ^ 3 • HH • X ≈⟨ (cright lemma-HH-X) ⟩
      H ^ 3 • X^ (- ₁) • H • H ≈⟨ by-passoc (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
      H ^ 3 • (X^ (- ₁) • H) • H ∎


  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹
  lemma-SHSH = bbc ε (S • H) claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    
    claim : ε • (S • H • S • H) • S • H ≈ ε • (H ^ 3 • S⁻¹) • S • H
    claim = begin
      ε • (S • H • S • H) • S • H ≈⟨ left-unit ⟩
      (S • H • S • H) • S • H ≈⟨ by-passoc (□ ^ 4 • □ ^ 2) ((□ ^ 2) ^ 3) auto ⟩
      (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
      ε ≈⟨ sym inverseˡ ⟩
      (H ^ 3 • S⁻¹) • S • H ≈⟨ sym left-unit ⟩
      ε • (H ^ 3 • S⁻¹) • S • H ∎


  lemma-HSHSH : H • S • H • S • H ≈ S⁻¹
  lemma-HSHSH = bbc S ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    
    claim : S • (H • S • H • S • H) • ε ≈ S • S⁻¹ • ε
    claim = begin
      S • (H • S • H • S • H) • ε ≈⟨ by-assoc auto ⟩
      (S • H) ^ 3 ≈⟨ axiom order-SH ⟩
      ε ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ≈⟨ sym (cong refl right-unit) ⟩
      S • S⁻¹ • ε ∎

  lemma-HSH : H • S • H ≈ S⁻¹ • H ^ 3 • S⁻¹
  lemma-HSH = bbc S ε claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    open Group-Lemmas _ (grouplike {₁₊ n}) renaming (_⁻¹ to _⁻¹ʷ)
    claim : S • (H • S • H) • ε ≈ S • (S⁻¹ • H ^ 3 • S⁻¹) • ε
    claim = begin
      S • (H • S • H) • ε ≈⟨ cong refl right-unit ⟩
      S • (H • S • H) ≈⟨ lemma-SHSH ⟩
      H ^ 3 • S⁻¹ ≈⟨ sym left-unit ⟩
      ε • H ^ 3 • S⁻¹ ≈⟨ (cleft sym (axiom order-S)) ⟩
      (S • S⁻¹) • H ^ 3 • S⁻¹ ≈⟨ assoc ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) ≈⟨ sym (cong refl right-unit) ⟩
      S • (S⁻¹ • H ^ 3 • S⁻¹) • ε ∎
  
  lemma-SX : S • X ≈ X • Z • S
  lemma-SX = begin
    S • H • S • H • H • S⁻¹ • H ≈⟨ by-passoc (□ ^ 7) (□ ^ 4 • □ ^ 3) auto ⟩
    (S • H • S • H) • H • S⁻¹ • H ≈⟨ (cleft lemma-SHSH) ⟩
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H ≈⟨ (cright cleft rewrite-sim 100  auto) ⟩
    (H ^ 3 • S⁻¹) • H ^ 5 • S⁻¹ • H ≈⟨ sym (by-passoc (□ ^ 5 • □ • □ ^ 3 • □ ^ 2) ((□ ^ 3 • □ )• □ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ (cleft (cright sym left-unit)) ⟩
    (H • ε • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ (cleft cright cleft sym (axiom order-S)) ⟩
    (H • (S • S⁻¹) • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H) ≈⟨ by-passoc ((□ • □ ^ 2 • □ ^ 4) • □ ^ 4) (□ ^ 2 • □ ^ 6 • □ ^ 3) auto ⟩
    (H • S) • (S⁻¹ • H • H • S⁻¹ • H • H) • H ^ 3 • S⁻¹ • H ≈⟨ (cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH p-1)) ⟩
    (H • S) • ((H • H • S⁻¹ • H • H) • S⁻¹) • H ^ 3 • S⁻¹ • H ≈⟨ by-passoc (□ ^ 2 • (□ ^ 5 • □) • □ ^ 3) (□ ^ 6 • □ • □ ^ 3 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • H • (S⁻¹ • H ^ 3 • S⁻¹) • H ≈⟨ (cright cright cleft sym lemma-HSH) ⟩
    (H • S • H • H • S⁻¹ • H) • H • (H • S • H) • H ≈⟨ by-passoc (□ ^ 6 • □ • □ ^ 3 • □) (□ ^ 6 • □ ^ 5) auto ⟩

    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) ≈⟨ (cright sym right-unit) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • ε ≈⟨ (cright cright sym (axiom order-S)) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S • S⁻¹ ≈⟨ (cright cright comm⇒pow-comm 1 p-1 refl) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S⁻¹ • S ≈⟨ (cright by-passoc (□ ^ 5 • □ ^ 2) (□ ^ 6 • □) auto) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • S ∎
    where
    open Sim-Rewriting n

  conj-S-X : S • X ≈ (X • Z) • S
  conj-S-X = begin
    S • X ≈⟨ lemma-SX ⟩
    X • Z • S ≈⟨ sym assoc ⟩
    (X • Z) • S ∎

  conj-S-X^k : ∀ k -> S • X ^ k ≈ (X • Z) ^ k • S
  conj-S-X^k k = lemma-Induction conj-S-X k

  conj-S^l-X : ∀ l -> S ^ l • X ≈ X • Z ^ l • S ^ l
  conj-S^l-X l = begin
    S ^ l • X ≈⟨ lemma-Inductionˡ lemma-SX l ⟩
    X • (Z • S) ^ l ≈⟨ (cright ^-• Z S l lemma-comm-Z-S) ⟩
    X • Z ^ l • S ^ l ∎  

  conj-S^l-X' : ∀ l -> S ^ l • X ≈ (X • Z ^ l) • S ^ l
  conj-S^l-X' l = begin
    S ^ l • X ≈⟨ conj-S^l-X l ⟩
    X • Z ^ l • S ^ l ≈⟨ sym assoc ⟩
    (X • Z ^ l) • S ^ l ∎

  aux-X⁻¹ : X⁻¹ ≈ H • S⁻¹ • H • H • S • H
  aux-X⁻¹ = begin
    X⁻¹ ≈⟨ lemma-X^k-ℕ p-1 ⟩
    H • S⁻¹ • H • H • S⁻¹ ^ p-1 • H ≈⟨ (cright cright cright cright cleft aux-S⁻¹⁻¹) ⟩
    H • S⁻¹ • H • H • S • H ∎
    where
    open Sim-Rewriting n

  aux-Z⁻¹ : Z⁻¹ ≈ H • H • S ^ p-1 • H • H • S
  aux-Z⁻¹ = begin
    Z⁻¹ ≈⟨ lemma-Z^k-ℕ p-1 ⟩
    H • H • S ^ p-1 • H • H • S⁻¹ ^ p-1 ≈⟨ (cright cright cright cright cright aux-S⁻¹⁻¹) ⟩
    H • H • S ^ p-1 • H • H • S ∎
    where
    open Sim-Rewriting n
