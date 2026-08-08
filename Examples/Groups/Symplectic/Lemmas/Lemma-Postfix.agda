{-# OPTIONS --cubical-compatible --safe #-}


import Relation.Binary.Reasoning.Setoid as SR



open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Fin using (toℕ)
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Lemma-Postfix (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open Lemmas-2Q 2
open Symplectic
open Lemmas-Sym
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm p-2 p-prime 0
open Lemmas0a
open Lemmas0b
open Lemmas0 1

open LM2
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()

open PB (2 QRel,_===_)
open PP (2 QRel,_===_)
module PB1 = PB (1 QRel,_===_)
module PP1 = PP (1 QRel,_===_)

open SR word-setoid
open Pattern-Assoc
open Duality


SingleQGen : Gen 2 -> Set
SingleQGen (H-gen) = ⊤
SingleQGen (S-gen) = ⊤
SingleQGen (H-gen ↥) = ⊤
SingleQGen (S-gen ↥) = ⊤
SingleQGen (CZ-gen) = ⊥
SingleQGen (EX-gen) = ⊥



Lemma-Postfix-SingleQ :

  ∀ (pf : Postfix) (g : Gen 2) -> (SingleQGen g) ->
  ---------------------------------------------------------
  ∃ \ cz -> ∃ \ s -> ∃ \ pf' -> ⟦ pf ⟧ₚ • [ g ]ʷ ≈ CZ^ cz • S^ s ↑ • ⟦ pf' ⟧ₚ

Lemma-Postfix-SingleQ pf@(k , mc1 , mc0) H-gen sg = cz , s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-H {1} mc0
  k0 = t0 .proj₁
  mc0' = t0 .proj₂ .proj₁
  cz : ℤ ₚ
  cz = - k0
  s : ℤ ₚ
  s = k0
  k' = k + k0
  pf' = k' , mc1 , mc0'
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ≈ CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ≈⟨ (cright t0 .proj₂ .proj₂) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S^ k0 • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S^ k0) • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ k0) ⟦ mc1 ⟧ₘ₊)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-CXS^k k0)) ⟩
    S^ k • (S^ k0 • S^ k0 ↑ • CZ^ (- k0) • H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ ^ 4) auto ⟩
    (S^ k • S^ k0) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-S^k+l k k0) ⟩
    (S^ (k + k0)) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ (k + k0) • S^ k0 ↑) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ (k + k0)) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ (k + k0)) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    S^ k0 ↑ • S^ (k + k0) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright sym assoc) ⟩
    S^ k0 ↑ • (S^ (k + k0) • CZ^ (- k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft comm⇒pow-comm (toℕ (k + k0)) (toℕ (- k0)) (sym (axiom comm-CZ-S↓))) ⟩
    S^ k0 ↑ • (CZ^ (- k0) • S^ (k + k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k0 ↑ • CZ^ (- k0)) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft sym (aux (- k0) k0)) ⟩
    (CZ^ (- k0) • S^ k0 ↑) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ ∎
    where
    aux : ∀ a b -> CZ^ a • S^ b ↑ ≈ S^ b ↑ • CZ^ a
    aux a b = begin
      CZ^ a • S^ b ↑ ≈⟨ (cright sym (refl' (aux-↑ S (toℕ b)))) ⟩
      CZ^ a • S ↑ ^ toℕ b ≈⟨ comm⇒pow-comm (toℕ a) (toℕ b) (axiom comm-CZ-S↑) ⟩
      S ↑ ^ toℕ b • CZ^ a ≈⟨ (cleft refl' (aux-↑ S (toℕ b))) ⟩
      S^ b ↑ • CZ^ a ∎

Lemma-Postfix-SingleQ pf@(k , mc1 , mc0) S-gen sg = cz , s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-S {1} mc0
  k0 = t0 .proj₁
  mc0' = t0 .proj₂ .proj₁
  cz : ℤ ₚ
  cz = - k0
  s : ℤ ₚ
  s = k0
  k' = k + k0
  pf' = k' , mc1 , mc0'
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • S ≈ CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • S ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • S ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • S ≈⟨ (cright t0 .proj₂ .proj₂) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S^ k0 • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S^ k0) • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ k0) ⟦ mc1 ⟧ₘ₊)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-CXS^k k0)) ⟩
    S^ k • (S^ k0 • S^ k0 ↑ • CZ^ (- k0) • H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ ^ 4) auto ⟩
    (S^ k • S^ k0) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-S^k+l k k0) ⟩
    (S^ (k + k0)) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ (k + k0) • S^ k0 ↑) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ (k + k0)) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ (k + k0)) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    S^ k0 ↑ • S^ (k + k0) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright sym assoc) ⟩
    S^ k0 ↑ • (S^ (k + k0) • CZ^ (- k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft comm⇒pow-comm (toℕ (k + k0)) (toℕ (- k0)) (sym (axiom comm-CZ-S↓))) ⟩
    S^ k0 ↑ • (CZ^ (- k0) • S^ (k + k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k0 ↑ • CZ^ (- k0)) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft sym (aux (- k0) k0)) ⟩
    (CZ^ (- k0) • S^ k0 ↑) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ ∎
    where
    aux : ∀ a b -> CZ^ a • S^ b ↑ ≈ S^ b ↑ • CZ^ a
    aux a b = begin
      CZ^ a • S^ b ↑ ≈⟨ (cright sym (refl' (aux-↑ S (toℕ b)))) ⟩
      CZ^ a • S ↑ ^ toℕ b ≈⟨ comm⇒pow-comm (toℕ a) (toℕ b) (axiom comm-CZ-S↑) ⟩
      S ↑ ^ toℕ b • CZ^ a ≈⟨ (cleft refl' (aux-↑ S (toℕ b))) ⟩
      S^ b ↑ • CZ^ a ∎

Lemma-Postfix-SingleQ pf@(k , mc1 , mc0) (H-gen ↥) sg = cz , s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-H {0} mc1
  k0 = t0 .proj₁
  mc1' = t0 .proj₂ .proj₁
  cz : ℤ ₚ
  cz = ₀
  s : ℤ ₚ
  s = k0
  pf' = k , mc1' , mc0
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ↑ ≈ CZ^ cz • S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ↑ ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ↑ ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ↑ ≈⟨ (cright aux-comm-mc-H↑ mc0) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • H ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • H ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft lemma-cong↑ _ _ (t0 .proj₂ .proj₂)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 ↑ • ⟦ mc1' ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0 ↑) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft aux-comm-CX-S^k↑ k0) ⟩
    S^ k • (S^ k0 ↑ • (H^ ₃ • CZ • H)) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k • S^ k0 ↑) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ k) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ • □) (□ • □ ^ 3) auto ⟩
    S^ k0 ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ≈⟨ sym left-unit ⟩
    CZ^ cz • S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ∎

Lemma-Postfix-SingleQ pf@(k , mc1 , mc0) (S-gen ↥) sg = cz , s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-S {0} mc1
  k0 = t0 .proj₁
  mc1' = t0 .proj₂ .proj₁
  cz : ℤ ₚ
  cz = ₀
  s : ℤ ₚ
  s = k0
  pf' = k , mc1' , mc0
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • S ↑ ≈ CZ^ cz • S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • S ↑ ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • S ↑ ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • S ↑ ≈⟨ (cright aux-comm-mc-S↑ mc0) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft lemma-cong↑ _ _ (t0 .proj₂ .proj₂)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 ↑ • ⟦ mc1' ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0 ↑) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft aux-comm-CX-S^k↑ k0) ⟩
    S^ k • (S^ k0 ↑ • (H^ ₃ • CZ • H)) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k • S^ k0 ↑) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ k) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ • □) (□ • □ ^ 3) auto ⟩
    S^ k0 ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ≈⟨ sym left-unit ⟩
    CZ^ cz • S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ∎

Lemma-Postfix-SingleQ pf CZ-gen ()



Lemma-Postfix-SingleQ-S↑ :

  ∀ (pf : Postfix) ->
  ---------------------------------------------------------------
  ∃ \ s -> ∃ \ pf' -> ⟦ pf ⟧ₚ • S ↑ ≈ S^ s ↑ • ⟦ pf' ⟧ₚ

Lemma-Postfix-SingleQ-S↑ pf@(k , mc1 , mc0) = s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-S {0} mc1
  k0 = t0 .proj₁
  mc1' = t0 .proj₂ .proj₁
  s : ℤ ₚ
  s = k0
  pf' = k , mc1' , mc0
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • S ↑ ≈ S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • S ↑ ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • S ↑ ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • S ↑ ≈⟨ (cright aux-comm-mc-S↑ mc0) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft lemma-cong↑ _ _ (t0 .proj₂ .proj₂)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 ↑ • ⟦ mc1' ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0 ↑) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft aux-comm-CX-S^k↑ k0) ⟩
    S^ k • (S^ k0 ↑ • (H^ ₃ • CZ • H)) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k • S^ k0 ↑) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ k) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ • □) (□ • □ ^ 3) auto ⟩
    S^ k0 ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ≈⟨ refl ⟩
    S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ∎



Lemma-Postfix-SingleQ-H↑ :

  ∀ (pf : Postfix) ->
  ---------------------------------------------------------------
  ∃ \ s -> ∃ \ pf' -> ⟦ pf ⟧ₚ • H ↑ ≈ S^ s ↑ • ⟦ pf' ⟧ₚ

Lemma-Postfix-SingleQ-H↑ pf@(k , mc1 , mc0) = s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-H {0} mc1
  k0 = t0 .proj₁
  mc1' = t0 .proj₂ .proj₁
  s : ℤ ₚ
  s = k0
  pf' = k , mc1' , mc0
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ↑ ≈ S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ↑ ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ↑ ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ↑ ≈⟨ (cright aux-comm-mc-H↑ mc0) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • H ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • H ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft lemma-cong↑ _ _ (t0 .proj₂ .proj₂)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 ↑ • ⟦ mc1' ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0 ↑) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cright cleft aux-comm-CX-S^k↑ k0) ⟩
    S^ k • (S^ k0 ↑ • (H^ ₃ • CZ • H)) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k • S^ k0 ↑) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ k) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ k) • (H^ ₃ • CZ • H) • ⟦ mc1' ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ • □) (□ • □ ^ 3) auto ⟩
    S^ k0 ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ≈⟨ refl ⟩
    S^ s ↑ • ⟦ k , mc1' , mc0 ⟧ₚ ∎


Lemma-Postfix-SingleQ-H :

  ∀ (pf : Postfix) ->
  ---------------------------------------------------------
  ∃ \ cz -> ∃ \ s -> ∃ \ pf' -> ⟦ pf ⟧ₚ • H ≈ CZ^ cz • S^ s ↑ • ⟦ pf' ⟧ₚ

Lemma-Postfix-SingleQ-H pf@(k , mc1 , mc0) = cz , s , pf' , claim
  where
  t0 = CP1.Lemma-single-qupit-completeness-mc-H {1} mc0
  k0 = t0 .proj₁
  mc0' = t0 .proj₂ .proj₁
  cz : ℤ ₚ
  cz = - k0
  s : ℤ ₚ
  s = k0
  k' = k + k0
  pf' = k' , mc1 , mc0'
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ≈ CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ≈⟨ (cright t0 .proj₂ .proj₂) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S^ k0 • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S^ k0) • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ k0) ⟦ mc1 ⟧ₘ₊)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-CXS^k k0)) ⟩
    S^ k • (S^ k0 • S^ k0 ↑ • CZ^ (- k0) • H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ ^ 4) auto ⟩
    (S^ k • S^ k0) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-S^k+l k k0) ⟩
    (S^ (k + k0)) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ (k + k0) • S^ k0 ↑) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ (k + k0)) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ (k + k0)) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    S^ k0 ↑ • S^ (k + k0) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright sym assoc) ⟩
    S^ k0 ↑ • (S^ (k + k0) • CZ^ (- k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft comm⇒pow-comm (toℕ (k + k0)) (toℕ (- k0)) (sym (axiom comm-CZ-S↓))) ⟩
    S^ k0 ↑ • (CZ^ (- k0) • S^ (k + k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k0 ↑ • CZ^ (- k0)) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft sym (aux (- k0) k0)) ⟩
    (CZ^ (- k0) • S^ k0 ↑) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ ∎
    where
    aux : ∀ a b -> CZ^ a • S^ b ↑ ≈ S^ b ↑ • CZ^ a
    aux a b = begin
      CZ^ a • S^ b ↑ ≈⟨ (cright sym (refl' (aux-↑ S (toℕ b)))) ⟩
      CZ^ a • S ↑ ^ toℕ b ≈⟨ comm⇒pow-comm (toℕ a) (toℕ b) (axiom comm-CZ-S↑) ⟩
      S ↑ ^ toℕ b • CZ^ a ≈⟨ (cleft refl' (aux-↑ S (toℕ b))) ⟩
      S^ b ↑ • CZ^ a ∎


Lemma-Postfix-SingleQ-S-ε :

  ∀ k pmc1 m -> let pf = (k , pmc1 , (m , ε)) in let cz = - m ^2 in
  ---------------------------------------------------------
  let s = m ^2 in let k' = k + s in ⟦ pf ⟧ₚ • S ≈ CZ^ cz • S^ s ↑ • ⟦ (k' , pmc1 , (m , ε)) ⟧ₚ

Lemma-Postfix-SingleQ-S-ε k mc1 m  = claim
  where
  cz : ℤ ₚ
  cz = - m ^2
  k0 = m ^2
  s : ℤ ₚ
  s = k0
  k' = k + k0
  mc0 = (m , ε)
  mc0' = (m , ε)
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • S ≈ CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • S ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • S ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • S ≈⟨ cright CP1.Lemma-single-qupit-completeness-mc-S-ε m ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S^ k0 • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S^ k0) • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ k0) ⟦ mc1 ⟧ₘ₊)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ k0 • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ k0) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-CXS^k k0)) ⟩
    S^ k • (S^ k0 • S^ k0 ↑ • CZ^ (- k0) • H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ ^ 4) auto ⟩
    (S^ k • S^ k0) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-S^k+l k k0) ⟩
    (S^ (k + k0)) • S^ k0 ↑ • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ (k + k0) • S^ k0 ↑) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ (k + k0)) (S^ k0)) ⟩
    (S^ k0 ↑ • S^ (k + k0)) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    S^ k0 ↑ • S^ (k + k0) • CZ^ (- k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright sym assoc) ⟩
    S^ k0 ↑ • (S^ (k + k0) • CZ^ (- k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft comm⇒pow-comm (toℕ (k + k0)) (toℕ (- k0)) (sym (axiom comm-CZ-S↓))) ⟩
    S^ k0 ↑ • (CZ^ (- k0) • S^ (k + k0)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ k0 ↑ • CZ^ (- k0)) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft sym (aux (- k0) k0)) ⟩
    (CZ^ (- k0) • S^ k0 ↑) • S^ (k + k0) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ ∎
    where
    aux : ∀ a b -> CZ^ a • S^ b ↑ ≈ S^ b ↑ • CZ^ a
    aux a b = begin
      CZ^ a • S^ b ↑ ≈⟨ (cright sym (refl' (aux-↑ S (toℕ b)))) ⟩
      CZ^ a • S ↑ ^ toℕ b ≈⟨ comm⇒pow-comm (toℕ a) (toℕ b) (axiom comm-CZ-S↑) ⟩
      S ↑ ^ toℕ b • CZ^ a ≈⟨ (cleft refl' (aux-↑ S (toℕ b))) ⟩
      S^ b ↑ • CZ^ a ∎


Lemma-Postfix-SingleQ-S-HS :

  ∀ k pmc1 m cc -> let pf = (k , pmc1 , (m , HS^ cc)) in 
  ---------------------------------------------------------
  ⟦ pf ⟧ₚ • S ≈ ⟦ (k , pmc1 , (m , HS^ (1ₚ + cc))) ⟧ₚ

Lemma-Postfix-SingleQ-S-HS k mc1 m cc  = claim
  where

  mc0 = (m , HS^ cc)
  mc0' = (m , HS^ (1ₚ + cc))
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • S ≈ ⟦ k , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • S ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • S ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • S ≈⟨ cright CP1.Lemma-single-qupit-completeness-mc-S-HS m cc ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
    ⟦ k , mc1 , mc0' ⟧ₚ ∎




Lemma-Postfix-SingleQ-H-ε :

  ∀ k pmc1 m -> let pf = (k , pmc1 , (m , ε)) in 
  ---------------------------------------------------------
  ⟦ pf ⟧ₚ • H ≈ ⟦ (k , pmc1 , (m , HS^ ₀)) ⟧ₚ

Lemma-Postfix-SingleQ-H-ε k mc1 m  = claim
  where

  mc0 = (m , ε)
  mc0' = (m , HS^ ₀)
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ≈ ⟦ k , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ≈⟨ cright CP1.Lemma-single-qupit-completeness-mc-H-ε m ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
    ⟦ k , mc1 , mc0' ⟧ₚ ∎

Lemma-Postfix-SingleQ-H-HS⁰ :

  ∀ k pmc1 m -> let pf = (k , pmc1 , (m , HS^ ₀)) in let mc' = (m *' -'₁ , ε) in 
  ---------------------------------------------------------
  ⟦ pf ⟧ₚ • H ≈ ⟦ (k , pmc1 , mc') ⟧ₚ

Lemma-Postfix-SingleQ-H-HS⁰ k mc1 m  = claim
  where

  mc0 = (m , HS^ ₀)
  mc0' = (m *' -'₁ , ε)
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ≈ ⟦ k , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ≈⟨ cright CP1.Lemma-single-qupit-completeness-mc-H-HS⁰ m ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
    ⟦ k , mc1 , mc0' ⟧ₚ ∎



Lemma-Postfix-SingleQ-H-HS :

  ∀ k mc1 m kk* -> let pf = (k , mc1 , (m , HS^ (kk* .proj₁))) in 
  ---------------------------------------------------------
  let k* = (-' (kk* ⁻¹) *' (m *' m)) in
  let sk = k* .proj₁ in
  let -m/kk* = ((m *' kk* ⁻¹) *' -'₁) in
  let -1/kk = - (kk* ⁻¹) .proj₁ in
  let mc' = (-m/kk* , HS^ -1/kk) in
  ---------------------------------------------------------
  let cz = - sk in let s = sk in  let pf' = (k + s , mc1 , mc') in ⟦ pf ⟧ₚ • H ≈ CZ^ cz • S^ s ↑ • ⟦ pf' ⟧ₚ

Lemma-Postfix-SingleQ-H-HS k mc1 m kk* = claim
  where
  k* = (-' (kk* ⁻¹) *' (m *' m))
  sk = k* .proj₁
  -m/kk* = ((m *' kk* ⁻¹) *' -'₁)
  -1/kk = - (kk* ⁻¹) .proj₁
  mc' = (-m/kk* , HS^ -1/kk)

  mc0' = mc'
  cz : ℤ ₚ
  cz = - sk
  s : ℤ ₚ
  s = sk
  k0 = s
  k' = k + s
  mc0 = (m , HS^ (kk* .proj₁))
  pf' = k' , mc1 , mc0'
  claim : ⟦ k , mc1 , mc0 ⟧ₚ • H ≈ CZ^ cz • S^ s ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ
  claim = begin
    ⟦ k , mc1 , mc0 ⟧ₚ • H ≈⟨ refl ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0 ⟧ₘ₊) • H ≈⟨ by-passoc (□ ^ 4 • □) (□ ^ 3 • □ ^ 2) auto ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0 ⟧ₘ₊ • H ≈⟨ (cright CP1.Lemma-single-qupit-completeness-mc-H-HS m kk*) ⟩
    (S^ k • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑) • S^ sk • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (⟦ mc1 ⟧ₘ₊ ↑ • S^ sk) • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-comm-Sᵏ-w↑ (toℕ sk) ⟦ mc1 ⟧ₘ₊)) ⟩
    (S^ k • (H^ ₃ • CZ • H)) • (S^ sk • ⟦ mc1 ⟧ₘ₊ ↑) • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
    S^ k • ((H^ ₃ • CZ • H) • S^ sk) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft sym (lemma-CXS^k sk)) ⟩
    S^ k • (S^ sk • S^ sk ↑ • CZ^ (- sk) • H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ ^ 4) auto ⟩
    (S^ k • S^ sk) • S^ sk ↑ • CZ^ (- sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-S^k+l k sk) ⟩
    (S^ (k + sk)) • S^ sk ↑ • CZ^ (- sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ sym assoc ⟩
    (S^ (k + sk) • S^ sk ↑) • CZ^ (- sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft lemma-comm-Sᵏ-w↑ (toℕ (k + sk)) (S^ sk)) ⟩
    (S^ sk ↑ • S^ (k + sk)) • CZ^ (- sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    S^ sk ↑ • S^ (k + sk) • CZ^ (- sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright sym assoc) ⟩
    S^ sk ↑ • (S^ (k + sk) • CZ^ (- sk)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cright cleft comm⇒pow-comm (toℕ (k + sk)) (toℕ (- sk)) (sym (axiom comm-CZ-S↓))) ⟩
    S^ sk ↑ • (CZ^ (- sk) • S^ (k + sk)) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ • □) auto ⟩
    (S^ sk ↑ • CZ^ (- sk)) • S^ (k + sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ (cleft sym (aux (- sk) sk)) ⟩
    (CZ^ (- sk) • S^ sk ↑) • S^ (k + sk) • (H^ ₃ • CZ • H) • ⟦ mc1 ⟧ₘ₊ ↑ • ⟦ mc0' ⟧ₘ₊ ≈⟨ assoc ⟩
    CZ^ cz • S^ sk ↑ • ⟦ k' , mc1 , mc0' ⟧ₚ ∎
    where
    aux : ∀ a b -> CZ^ a • S^ b ↑ ≈ S^ b ↑ • CZ^ a
    aux a b = begin
      CZ^ a • S^ b ↑ ≈⟨ (cright sym (refl' (aux-↑ S (toℕ b)))) ⟩
      CZ^ a • S ↑ ^ toℕ b ≈⟨ comm⇒pow-comm (toℕ a) (toℕ b) (axiom comm-CZ-S↑) ⟩
      S ↑ ^ toℕ b • CZ^ a ≈⟨ (cleft refl' (aux-↑ S (toℕ b))) ⟩
      S^ b ↑ • CZ^ a ∎
