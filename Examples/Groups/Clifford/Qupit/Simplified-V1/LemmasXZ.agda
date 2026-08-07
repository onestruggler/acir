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

  -- --------------------------------------------------------------------
  -- Moving Pauli powers rightward past S
  --
  -- Groundwork for deriving order-SH from M-power alone, following
  -- Proposition 4.8: the plan is (R • H) ^ 3 ≈ (S • H) ^ 3, where
  -- R = S • Z^½.  Since M ₁ = (R • H) ^ 3 definitionally and lemma-M1
  -- gives M ₁ ≈ ε out of M-power, that would yield (S • H) ^ 3 ≈ ε
  -- without appealing to order-SH.  These are the right-moving
  -- companions of conj-S-X^k / conj-S^l-X, which move S past a Pauli.
  --
  -- NOTE: everything here is independent of order-SH.  lemma-SHSH and
  -- lemma-HSHSH above are NOT usable for that derivation — both are
  -- proved from `axiom order-SH` and so are downstream of it.

  -- Z-powers commute with S outright.
  comm-Z^k-S : ∀ k -> Z ^ k • S ≈ S • Z ^ k
  comm-Z^k-S k = lemma-Inductionˡ lemma-comm-Z-S k

  -- Z • Z⁻¹ is Z ^ p on the nose, since p = ₂₊ p-2.
  lemma-Z-Z⁻¹ : Z • Z⁻¹ ≈ ε
  lemma-Z-Z⁻¹ = lemma-order-Z

  -- Moving a single X rightward past S costs a Z⁻¹.
  lemma-XS : X • S ≈ S • X • Z⁻¹
  lemma-XS = sym (begin
    S • X • Z⁻¹         ≈⟨ sym assoc ⟩
    (S • X) • Z⁻¹       ≈⟨ (cleft conj-S-X) ⟩
    ((X • Z) • S) • Z⁻¹ ≈⟨ assoc ⟩
    (X • Z) • S • Z⁻¹   ≈⟨ (cright sym (comm-Z^k-S p-1)) ⟩
    (X • Z) • Z⁻¹ • S   ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    X • (Z • Z⁻¹) • S   ≈⟨ (cright cleft lemma-Z-Z⁻¹) ⟩
    X • ε • S           ≈⟨ (cright left-unit) ⟩
    X • S ∎)

  -- …and so an X-power costs a Z⁻¹-power.
  conj-X^k-S : ∀ k -> X ^ k • S ≈ S • (X • Z⁻¹) ^ k
  conj-X^k-S k = lemma-Inductionˡ lemma-XS k

  -- X^(-1) spelled as a Z-power exponent is X⁻¹: toℕ (- ₁) is p-1.
  aux-X^-₁ : X^ (- ₁) ≈ X⁻¹
  aux-X^-₁ = refl' (Eq.cong (X ^_)
               (Eq.trans (Eq.cong toℕ (Eq.sym p-1=-1ₚ)) lemma-toℕ-ₚ₋₁))

  aux-X-X⁻¹ : X • X⁻¹ ≈ ε
  aux-X-X⁻¹ = lemma-order-X

  aux-Z⁻¹-Z : Z⁻¹ • Z ≈ ε
  aux-Z⁻¹-Z = begin
    Z⁻¹ • Z ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
    Z • Z⁻¹ ≈⟨ lemma-Z-Z⁻¹ ⟩
    ε ∎

  -- Conjugation by H sends X to Z and Z to X⁻¹, so it sends X to Z⁻¹ the
  -- other way round.  This is the companion of conj-H-X / conj-H-Z that
  -- moves the Pauli rightward through H.
  lemma-XH : X • H ≈ H • Z⁻¹
  lemma-XH = bbc ε Z claim
    where
    open Basis-Change _ ((₁₊ n) QRel,_===_) grouplike
    claim : ε • (X • H) • Z ≈ ε • (H • Z⁻¹) • Z
    claim = begin
      ε • (X • H) • Z   ≈⟨ left-unit ⟩
      (X • H) • Z       ≈⟨ assoc ⟩
      X • (H • Z)       ≈⟨ (cright conj-H-Z) ⟩
      X • (X^ (- ₁) • H) ≈⟨ (cright cleft aux-X^-₁) ⟩
      X • (X⁻¹ • H)     ≈⟨ sym assoc ⟩
      (X • X⁻¹) • H     ≈⟨ (cleft aux-X-X⁻¹) ⟩
      ε • H             ≈⟨ left-unit ⟩
      H                 ≈⟨ sym right-unit ⟩
      H • ε             ≈⟨ (cright sym aux-Z⁻¹-Z) ⟩
      H • Z⁻¹ • Z       ≈⟨ sym assoc ⟩
      (H • Z⁻¹) • Z     ≈⟨ sym left-unit ⟩
      ε • (H • Z⁻¹) • Z ∎

  conj-X^k-H : ∀ k -> X ^ k • H ≈ H • Z⁻¹ ^ k
  conj-X^k-H k = lemma-Inductionˡ lemma-XH k

  -- X commutes with Z-powers, hence with Z⁻¹.
  comm-X-Z^k : ∀ k -> X • Z ^ k ≈ Z ^ k • X
  comm-X-Z^k k = lemma-Induction (axiom comm-X-Z) k

  split-XZ⁻¹^k : ∀ k -> (X • Z⁻¹) ^ k ≈ X ^ k • Z⁻¹ ^ k
  split-XZ⁻¹^k k = ^-• X Z⁻¹ k (comm-X-Z^k p-1)

  aux-Z⁻¹^k-Z^k : ∀ k -> Z⁻¹ ^ k • Z ^ k ≈ ε
  aux-Z⁻¹^k-Z^k k = begin
    Z⁻¹ ^ k • Z ^ k ≈⟨ sym (^-• Z⁻¹ Z k (comm⇒pow-comm p-1 1 refl)) ⟩
    (Z⁻¹ • Z) ^ k   ≈⟨ ^-cong (Z⁻¹ • Z) ε k aux-Z⁻¹-Z ⟩
    ε ^ k           ≈⟨ ε^k=ε k ⟩
    ε ∎

  -- --------------------------------------------------------------------
  -- (R • H) ^ 3 ≈ (S • H) ^ 3, the bridge that makes order-SH derivable.
  --
  -- R = S • Z^½, so each R contributes a Pauli.  Moved one at a time,
  -- each cancels against the NEXT Z^½ (Proposition 4.8):
  --
  --   S P H S P H S P H          P = Z^a, Q = X^a, a = toℕ ½
  --   S H Q S P H S P H          P•H = H•Q
  --   S H S (X•Z⁻¹)^a P H S P H  Q•S = S•(X•Z⁻¹)^a
  --   S H S X^a H S P H          (X^a•Z⁻¹^a)•Z^a = X^a
  --   S H S H Z⁻¹^a S P H        X^a•H = H•Z⁻¹^a
  --   S H S H S Z⁻¹^a P H        Z⁻¹^a•S = S•Z⁻¹^a
  --   S H S H S H                Z⁻¹^a•Z^a = ε
  --
  -- R is unfolded in its own `refl` step: a by-passoc pattern cannot
  -- span the R boundary, since unfolding changes the atom count 6 -> 9.

  -- The ℕ exponent carried by R's Pauli.
  a½ : ℕ
  a½ = toℕ 1/2

  lemma-RH⁶ : (R • H) ^ 3 ≈ S • Z ^ a½ • H • S • Z ^ a½ • H • S • Z ^ a½ • H
  lemma-RH⁶ = begin
    (R • H) ^ 3
      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □))
                   (□ • □ • □ • □ • □ • □) auto ⟩
    R • H • R • H • R • H
      ≈⟨ refl ⟩
    (S • Z ^ a½) • H • (S • Z ^ a½) • H • (S • Z ^ a½) • H
      ≈⟨ by-passoc (□ ^ 2 • □ • □ ^ 2 • □ • □ ^ 2 • □)
                   (□ • □ • □ • □ • □ • □ • □ • □ • □) auto ⟩
    S • Z ^ a½ • H • S • Z ^ a½ • H • S • Z ^ a½ • H ∎

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
