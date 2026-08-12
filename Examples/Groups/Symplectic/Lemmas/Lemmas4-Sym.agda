{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)

open import Data.Empty using (⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Data.Fin using (toℕ)
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    




open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open LM2


--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality



aux-comm-shs-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in
  ∀ a b -> SHS a b • CZ ↑ ≈ CZ ↑ • SHS a b
aux-comm-shs-CZ↑ {n} x x⁻¹ = begin
  SHS x x⁻¹ • CZ ↑ ≈⟨ (cleft refl) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x • H) • CZ ↑ ≈⟨ by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H • CZ ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • CZ ↑ • H ≈⟨ by-passoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S^ x • CZ ↑) • H ≈⟨ (cright cleft comm⇒pow-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H • S^ x⁻¹ • H) • (CZ ↑ • S^ x) • H ≈⟨ by-passoc ((□ ^ 4 • □ ^ 2 • □)) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹) • (H • CZ ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹) • (CZ ↑ • H) • S^ x • H ≈⟨ by-passoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ x • H) • (S^ x⁻¹ • CZ ↑) • H • S^ x • H ≈⟨ (cright cleft comm⇒pow-comm (toℕ x⁻¹) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H) • (CZ ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ by-passoc ((□ ^ 2 • □ ^ 2 • □ ^ 3)) ((□ • □ ^ 2 • □ ^ 4)) auto ⟩
  S^ x • (H • CZ ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  S^ x • (CZ ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-passoc ((□ • □ ^ 2 • □ ^ 4)) ((□ ^ 2 • □ ^ 5)) auto ⟩
  (S^ x • CZ ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft comm⇒pow-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  (CZ ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
  CZ ↑ • SHS x x⁻¹ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

aux-comm-m-CZ↑ : let open PB ((₃₊ n) QRel,_===_) in ∀ m -> ⟦ m ⟧ₘ • CZ ↑ ≈ CZ ↑ • ⟦ m ⟧ₘ
aux-comm-m-CZ↑ m = aux-comm-shs-CZ↑ (m .proj₁) ((m ⁻¹) .proj₁)

aux-comm-shs-CZ^ : let open PB ((₃₊ n) QRel,_===_) in
  ∀ a b k -> SHS a b • CZ^ k ↑ ≈ CZ^ k ↑ • SHS a b
aux-comm-shs-CZ^ {n} a b k = begin
  SHS a b • CZ^ k ↑ ≈⟨ cright sym (refl' (aux-↑ CZ (toℕ k))) ⟩
  SHS a b • CZ ↑ ^ toℕ k ≈⟨ comm⇒pow-comm 1 (toℕ k) (aux-comm-shs-CZ↑ a b) ⟩
  CZ ↑ ^ toℕ k • SHS a b ≈⟨ cleft refl' (aux-↑ CZ (toℕ k)) ⟩
  CZ^ k ↑ • SHS a b ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

aux-comm-m-CZ^ : let open PB ((₃₊ n) QRel,_===_) in ∀ m k -> ⟦ m ⟧ₘ • CZ^ k ↑ ≈ CZ^ k ↑ • ⟦ m ⟧ₘ
aux-comm-m-CZ^ m = aux-comm-shs-CZ^ (m .proj₁) ((m ⁻¹) .proj₁)

aux-comm-shs-g↥↑ : let open PB ((₃₊ n) QRel,_===_) in
  ∀ a b g -> SHS a b • [ g ↥ ]ʷ ↑ ≈ [ g ↥ ]ʷ ↑ • SHS a b
aux-comm-shs-g↥↑ {n} x x⁻¹ g = begin
  SHS x x⁻¹ • [ g ↥ ]ʷ ↑ ≈⟨ (cleft refl) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x • H) • [ g ↥ ]ʷ ↑ ≈⟨ by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • H • [ g ↥ ]ʷ ↑ ≈⟨ (cright sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹ • H • S^ x) • [ g ↥ ]ʷ ↑ • H ≈⟨ by-passoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
  (S^ x • H • S^ x⁻¹ • H) • (S^ x • [ g ↥ ]ʷ ↑) • H ≈⟨ (cright cleft comm⇒pow-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H • S^ x⁻¹ • H) • ([ g ↥ ]ʷ ↑ • S^ x) • H ≈⟨ by-passoc ((□ ^ 4 • □ ^ 2 • □)) (□ ^ 3 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ x • H • S^ x⁻¹) • (H • [ g ↥ ]ʷ ↑) • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  (S^ x • H • S^ x⁻¹) • ([ g ↥ ]ʷ ↑ • H) • S^ x • H ≈⟨ by-passoc (□ ^ 3 • □ ^ 2 • □ ^ 2) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
  (S^ x • H) • (S^ x⁻¹ • [ g ↥ ]ʷ ↑) • H • S^ x • H ≈⟨ (cright cleft comm⇒pow-comm (toℕ x⁻¹) 1 (sym (axiom comm-S))) ⟩
  (S^ x • H) • ([ g ↥ ]ʷ ↑ • S^ x⁻¹) • H • S^ x • H ≈⟨ by-passoc ((□ ^ 2 • □ ^ 2 • □ ^ 3)) ((□ • □ ^ 2 • □ ^ 4)) auto ⟩
  S^ x • (H • [ g ↥ ]ʷ ↑) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cright cleft sym (axiom comm-H)) ⟩
  S^ x • ([ g ↥ ]ʷ ↑ • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-passoc ((□ • □ ^ 2 • □ ^ 4)) ((□ ^ 2 • □ ^ 5)) auto ⟩
  (S^ x • [ g ↥ ]ʷ ↑) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft comm⇒pow-comm (toℕ x) 1 (sym (axiom comm-S))) ⟩
  ([ g ↥ ]ʷ ↑ • S^ x) • H • S^ x⁻¹ • H • S^ x • H ≈⟨ assoc ⟩
  [ g ↥ ]ʷ ↑ • SHS x x⁻¹ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

aux-comm-m-g↥↑ : let open PB ((₃₊ n) QRel,_===_) in ∀ m g -> ⟦ m ⟧ₘ • [ g ↥ ]ʷ ↑ ≈ [ g ↥ ]ʷ ↑ • ⟦ m ⟧ₘ
aux-comm-m-g↥↑ m = aux-comm-shs-g↥↑ (m .proj₁) ((m ⁻¹) .proj₁)


aux-comm-shs-w↑ : let open PB ((₁₊ n) QRel,_===_) in
  ∀ a b w -> SHS a b • w ↑ ≈ w ↑ • SHS a b
aux-comm-shs-w↑ {₁₊ n} a b [ H-gen ]ʷ = aux-comm-shs-H↑ n a b
aux-comm-shs-w↑ {₁₊ n} a b [ S-gen ]ʷ = aux-comm-shs-S↑ n a b
aux-comm-shs-w↑ {₂₊ n} a b [ CZ-gen ]ʷ = aux-comm-shs-CZ↑ a b
aux-comm-shs-w↑ {₂₊ n} a b [ x ↥ ]ʷ = aux-comm-shs-g↥↑ a b x
aux-comm-shs-w↑ {₀} a b [ gate₀ () ]ʷ
aux-comm-shs-w↑ {₁} a b [ gate₀ () ↥ ]ʷ
aux-comm-shs-w↑ {n} a b ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
aux-comm-shs-w↑ {n} a b (w • v) = begin
  SHS a b • w ↑ • v ↑ ≈⟨ sym assoc ⟩
  (SHS a b • w ↑) • v ↑ ≈⟨ (cleft aux-comm-shs-w↑ a b w) ⟩
  (w ↑ • SHS a b) • v ↑ ≈⟨ assoc ⟩
  w ↑ • SHS a b • v ↑ ≈⟨ (cright aux-comm-shs-w↑ a b v) ⟩
  w ↑ • v ↑ • SHS a b ≈⟨ sym assoc ⟩
  (w ↑ • v ↑) • SHS a b ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

aux-comm-m-w↑ : let open PB ((₁₊ n) QRel,_===_) in ∀ m w -> ⟦ m ⟧ₘ • w ↑ ≈ w ↑ • ⟦ m ⟧ₘ
aux-comm-m-w↑ m = aux-comm-shs-w↑ (m .proj₁) ((m ⁻¹) .proj₁)

-- The XM instance: the same shape with the two exponents swapped.
comm-XM-w↑ : let open PB ((₁₊ n) QRel,_===_) in
  ∀ x w -> XM x • w ↑ ≈ w ↑ • XM x
comm-XM-w↑ x = aux-comm-shs-w↑ ((x ⁻¹) .proj₁) (x .proj₁)


-- Commuting past a shifted circuit is closed under concatenation, so a
-- box can be handled letter by letter instead of by one long
-- re-association.
comm-•-w↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ {u v : Word (Gen (₂₊ n))} (w : Word (Gen (₁₊ n))) →
  u • w ↑ ≈ w ↑ • u → v • w ↑ ≈ w ↑ • v →
  (u • v) • w ↑ ≈ w ↑ • (u • v)
comm-•-w↑ {n} {u} {v} w pu pv = begin
  (u • v) • w ↑ ≈⟨ assoc ⟩
  u • v • w ↑   ≈⟨ (cright pv) ⟩
  u • w ↑ • v   ≈⟨ sym assoc ⟩
  (u • w ↑) • v ≈⟨ (cleft pu) ⟩
  (w ↑ • u) • v ≈⟨ assoc ⟩
  w ↑ • u • v ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

comm-abox-w↑ : let open PB ((₁₊ n) QRel,_===_) in
  ∀ a (w : Word (Gen n)) -> [ a ]ᵃ • w ↑ ≈ w ↑ • [ a ]ᵃ
-- At width 0 there are no generators to commute with, so the induction
-- on w closes without looking at the box at all.
comm-abox-w↑ {₀} d [ gate₀ () ]ʷ
comm-abox-w↑ {₀} d ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-abox-w↑ {₀} d (w • v) = begin
  [ d ]ᵃ • w ↑ • v ↑ ≈⟨ sym assoc ⟩
  ([ d ]ᵃ • w ↑) • v ↑ ≈⟨ (cleft comm-abox-w↑ d w) ⟩
  (w ↑ • [ d ]ᵃ) • v ↑ ≈⟨ assoc ⟩
  w ↑ • [ d ]ᵃ • v ↑ ≈⟨ (cright comm-abox-w↑ d v) ⟩
  w ↑ • v ↑ • [ d ]ᵃ ≈⟨ sym assoc ⟩
  (w ↑ • v ↑) • [ d ]ᵃ ∎
  where
  open PB ((1) QRel,_===_)
  open PP ((1) QRel,_===_)
  open SR word-setoid
comm-abox-w↑ {₁₊ n} ((₀ , ₀) , neqI) w = ⊥-elim (neqI auto)
comm-abox-w↑ {₁₊ n} ((₀ , b@(₁₊ _)) , neqI) w = comm-XM-w↑ (b , λ ()) w
comm-abox-w↑ {₁₊ n} ((a@(₁₊ _) , b) , neqI) w =
  comm-•-w↑ w (comm-XM-w↑ (a , λ ()) w)
  (comm-•-w↑ w (lemma-comm-H-w↑ w) (lemma-comm-Sᵏ-w↑ (toℕ -b/a) w))
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹





comm-hs-w↑ : let open PB ((₁₊ n) QRel,_===_) in
  ∀ k (w : Word (Gen n)) -> (H • S^ k) • w ↑ ≈ w ↑ • H • S^ k
comm-hs-w↑ {₀} k [ gate₀ () ]ʷ
comm-hs-w↑ {0} k ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-hs-w↑ {0} k (w • v) = begin
  (H • S^ k) • w ↑ • v ↑ ≈⟨ sym assoc ⟩
  ((H • S^ k) • w ↑) • v ↑ ≈⟨ (cleft comm-hs-w↑ k w) ⟩
  (w ↑ • (H • S^ k)) • v ↑ ≈⟨ assoc ⟩
  w ↑ • (H • S^ k) • v ↑ ≈⟨ (cright comm-hs-w↑ k v) ⟩
  w ↑ • v ↑ • (H • S^ k) ≈⟨ sym assoc ⟩
  (w ↑ • v ↑) • (H • S^ k) ∎
  where
  open PB ((1) QRel,_===_)  
  open PP ((1) QRel,_===_)
  open SR word-setoid
comm-hs-w↑ {n@(₁₊ _)} k w = begin
  (H • S^ k) • w ↑ ≈⟨ assoc ⟩
  H • S^ k • w ↑ ≈⟨ (cright lemma-comm-Sᵏ-w↑ (toℕ k) w) ⟩
  H • w ↑ • S^ k ≈⟨ ( sym assoc) ⟩
  (H • w ↑) • S^ k ≈⟨ ( cleft lemma-comm-H-w↑ w) ⟩
  (w ↑ • H) • S^ k ≈⟨ assoc ⟩
  w ↑ • H • S^ k ∎
  where
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

comm-Ex-CZ^k-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k (w : Word (Gen n)) -> (Ex • CZ^ k) • w ↑ ↑ ≈ w ↑ ↑ • Ex • CZ^ k

comm-Ex-CZ^k-w↑↑ {₀} k [ gate₀ () ]ʷ
comm-Ex-CZ^k-w↑↑ {0} l ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-Ex-CZ^k-w↑↑ {0} k (w • v) = begin
  (Ex • CZ^ k) • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ((Ex • CZ^ k) • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-Ex-CZ^k-w↑↑ k w) ⟩
  (w ↑ ↑ • (Ex • CZ^ k)) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • (Ex • CZ^ k) • v ↑ ↑ ≈⟨ (cright comm-Ex-CZ^k-w↑↑ k v) ⟩
  w ↑ ↑ • v ↑ ↑ • (Ex • CZ^ k) ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • (Ex • CZ^ k) ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid


comm-Ex-CZ^k-w↑↑ {₁₊ n} k w = begin
  (Ex • CZ^ k) • w ↑ ↑ ≈⟨ assoc ⟩
  Ex • CZ^ k • w ↑ ↑ ≈⟨ cright comm⇒pow-comm (toℕ k) 1 (lemma-comm-CZ-w↑↑ w) ⟩
  Ex • w ↑ ↑ • CZ^ k ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • CZ^ k ≈⟨ cleft lemma-comm-Ex-w↑↑ w ⟩
  (w ↑ ↑ • Ex) • CZ^ k ≈⟨ assoc ⟩
  w ↑ ↑ • Ex • CZ^ k ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)
  

lemma-comm-CX^k-w↑↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  CX'^ k • w ↑ ↑ ≈ w ↑ ↑ • CX'^ k

lemma-comm-CX^k-w↑↑ {n} k w = begin
  CX'^ k • w ↑ ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  H ^ 3 • CZ^ k • H • w ↑ ↑ ≈⟨ (cright cright lemma-comm-H-w↑ (w ↑)) ⟩
  H ^ 3 • CZ^ k • w ↑ ↑ • H ≈⟨ cright sym assoc ⟩
  H ^ 3 • (CZ^ k • w ↑ ↑) • H ≈⟨ (cright cleft comm⇒pow-comm (toℕ k) 1 (lemma-comm-CZ-w↑↑ w)) ⟩
  H ^ 3 • (w ↑ ↑ • CZ^ k) • H ≈⟨ trans (by-assoc auto) assoc ⟩
  (H ^ 3 • w ↑ ↑) • CZ^ k • H ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 3 (w ↑)) ⟩
  (w ↑ ↑ • H ^ 3) • CZ^ k • H ≈⟨ assoc ⟩
  w ↑ ↑ • CX'^ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas3
  open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)




comm-dbox-w↑↑' : let open PB ((₂₊ n) QRel,_===_) in
  ∀ a b (w : Word (Gen n)) -> [ a , b ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ a , b ]ᵈ
comm-dbox-w↑↑' {₀} a b [ gate₀ () ]ʷ
comm-dbox-w↑↑' {0} a b ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-dbox-w↑↑' {0} a b' (w • v) = let b = (a , b') in begin
  [ b ]ᵈ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ([ b ]ᵈ • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-dbox-w↑↑' a b' w) ⟩
  (w ↑ ↑ • [ b ]ᵈ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵈ • v ↑ ↑ ≈⟨ (cright comm-dbox-w↑↑' a b' v) ⟩
  w ↑ ↑ • v ↑ ↑ • [ b ]ᵈ ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • [ b ]ᵈ ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid
comm-dbox-w↑↑' {₁₊ n} a@₀ b' w = let b = (₀ , b') in  begin
  [ ₀ , b' ]ᵈ • w ↑ ↑ ≈⟨ assoc ⟩
  Ex • CZ^ (- b') • w ↑ ↑ ≈⟨ cright comm⇒pow-comm (toℕ (- b')) 1 (lemma-comm-CZ-w↑↑ w) ⟩
  Ex • w ↑ ↑ • CZ^ (- b') ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • CZ^ (- b') ≈⟨ cleft lemma-comm-Ex-w↑↑ w ⟩
  (w ↑ ↑ • Ex) • CZ^ (- b') ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)
  
comm-dbox-w↑↑' {₁₊ n} a@(₁₊ _) b w = let d = (a , b) in  begin
  [ a , b ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- a) • H • S^ -b/a) • w ↑ ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CZ^ (- a)) • (H • S^ -b/a) • w ↑ ↑ ≈⟨ (cright (comm-hs-w↑ -b/a (w ↑))) ⟩
  (Ex • CZ^ (- a)) • w ↑ ↑ • (H • S^ -b/a) ≈⟨ sym assoc ⟩
  ((Ex • CZ^ (- a)) • w ↑ ↑) • (H • S^ -b/a) ≈⟨ (cleft comm-Ex-CZ^k-w↑↑ (- a) w) ⟩
  (w ↑ ↑ • (Ex • CZ^ (- a))) • (H • S^ -b/a) ≈⟨ by-passoc (□ ^ 3 • □ ^ 2 ) (□ • □ ^ 4) auto ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


comm-dbox-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ b (w : Word (Gen n)) -> [ b ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ b ]ᵈ
comm-dbox-w↑↑ {n} d@(a , b) w = comm-dbox-w↑↑' a b w



comm-bbox-w↑↑' : let open PB ((₂₊ n) QRel,_===_) in
  ∀ a b (w : Word (Gen n)) -> [ a , b ]ᵇ • w ↑ ↑ ≈ w ↑ ↑ • [ a , b ]ᵇ
comm-bbox-w↑↑' {₀} a b [ gate₀ () ]ʷ
comm-bbox-w↑↑' {0} a b ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-bbox-w↑↑' {0} a b' (w • v) = let b = (a , b') in begin
  [ b ]ᵇ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ([ b ]ᵇ • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-bbox-w↑↑' a b' w) ⟩
  (w ↑ ↑ • [ b ]ᵇ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵇ • v ↑ ↑ ≈⟨ (cright comm-bbox-w↑↑' a b' v) ⟩
  w ↑ ↑ • v ↑ ↑ • [ b ]ᵇ ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • [ b ]ᵇ ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid
comm-bbox-w↑↑' {₁₊ n} a@₀ b' w = let b = (₀ , b') in  begin
  [ ₀ , b' ]ᵇ • w ↑ ↑ ≈⟨ assoc ⟩
  Ex • CX'^ (b') • w ↑ ↑ ≈⟨ cright lemma-comm-CX^k-w↑↑ b' w ⟩
  Ex • w ↑ ↑ • CX'^ (b') ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • CX'^ (b') ≈⟨ cleft lemma-comm-Ex-w↑↑ w ⟩
  (w ↑ ↑ • Ex) • CX'^ (b') ≈⟨ assoc ⟩
  w ↑ ↑ • [ b ]ᵇ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime hiding (lemma-comm-Ex-w↑↑)


comm-bbox-w↑↑' {₁₊ n} a@(₁₊ _) b w = let d = (a , b) in  begin
  [ a , b ]ᵇ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CX'^ (a) • (H • S^ -b/a) ↑) • w ↑ ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • CX'^ (a)) • (H • S^ -b/a) ↑ • w ↑ ↑ ≈⟨ (cright (lemma-cong↑ _ _ (comm-hs-w↑ -b/a (w )))) ⟩
  (Ex • CX'^ (a)) • w ↑ ↑ • (H • S^ -b/a) ↑ ≈⟨ sym assoc ⟩
  ((Ex • CX'^ (a)) • w ↑ ↑) • (H • S^ -b/a) ↑ ≈⟨ (cleft assoc) ⟩
  (Ex • CX'^ (a) • w ↑ ↑) • (H • S^ -b/a) ↑ ≈⟨ (cleft (cright lemma-comm-CX^k-w↑↑ a w)) ⟩
  (Ex • w ↑ ↑ • CX'^ (a)) • (H • S^ -b/a) ↑ ≈⟨ ( by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  (Ex • w ↑ ↑) • CX'^ a • (H • S^ -b/a) ↑ ≈⟨ (cleft lemma-comm-Ex-w↑↑ w) ⟩
  (w ↑ ↑ • Ex) • CX'^ a • (H • S^ -b/a) ↑ ≈⟨ ( by-passoc (□ ^ 2 • □ ^ 2) (□ ^ 4) auto) ⟩ 
  w ↑ ↑ • Ex • CX'^ a • (H • S^ -b/a) ↑ ≈⟨ refl ⟩
  w ↑ ↑ • [ d ]ᵇ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


comm-bbox-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ b (w : Word (Gen n)) -> [ b ]ᵇ • w ↑ ↑ ≈ w ↑ ↑ • [ b ]ᵇ
comm-bbox-w↑↑ {n} d@(a , b) w = comm-bbox-w↑↑' a b w


{-

comm-dbox-w↑↑' : let open PB ((₂₊ n) QRel,_===_) in
  ∀ a d (w : Word (Gen n)) -> [ a , d ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ a , d ]ᵈ
comm-dbox-w↑↑' {0} a d ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
comm-dbox-w↑↑' {0} a d' (w • v) = let d = (a , d') in begin
  [ d ]ᵈ • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • w ↑ ↑) • v ↑ ↑ ≈⟨ (cleft comm-dbox-w↑↑' a d' w) ⟩
  (w ↑ ↑ • [ d ]ᵈ) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • [ d ]ᵈ • v ↑ ↑ ≈⟨ (cright comm-dbox-w↑↑' a d' v) ⟩
  w ↑ ↑ • v ↑ ↑ • [ d ]ᵈ ≈⟨ sym assoc ⟩
  (w ↑ ↑ • v ↑ ↑) • [ d ]ᵈ ∎
  where
  open PB ((2) QRel,_===_)  
  open PP ((2) QRel,_===_)
  open SR word-setoid
comm-dbox-w↑↑' {₁₊ n} a@₀ d'@₀ w = let d = (₀ , d') in  begin
  [ ₀ , d' ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex ) • w ↑ ↑ ≈⟨  lemma-comm-Ex-w↑↑ w ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
comm-dbox-w↑↑' {₁₊ n} a@₀ d'@(₁₊ _) w = let d = (₀ , d') in  begin
  [ ₀ , d' ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ) • w ↑ ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ • w ↑ ↑ ≈⟨ (cright cright comm-abox-w↑ ((₀ , d') , (λ ())) (w ↑)) ⟩
  Ex • CZ^ (- ₁) • w ↑ ↑ • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ (cright sym assoc) ⟩
  Ex • (CZ^ (- ₁) • w ↑ ↑) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ (((cright cleft  comm⇒pow-comm (toℕ m1) 1 ( lemma-comm-CZ-w↑ w)))) ⟩
  Ex • (w ↑ ↑ • CZ^ (- ₁)) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • w ↑ ↑) • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨ ( cleft lemma-comm-Ex-w↑↑ w) ⟩
  (w ↑ ↑ • Ex) • CZ^ (- ₁) • [ (₀ , d') , (λ ()) ]ᵃ ≈⟨  assoc ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁

comm-dbox-w↑↑' {₁₊ n} a@(₁₊ _) d' w = let d = (a , d') in  begin
  [ a , d' ]ᵈ • w ↑ ↑ ≈⟨ refl ⟩
  (Ex • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ) • w ↑ ↑ ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  Ex • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ • w ↑ ↑ ≈⟨ (cright cright comm-abox-w↑ ((a , d') , (λ ())) (w ↑)) ⟩
  Ex • CZ^ (- ₁) • w ↑ ↑ • [ (a , d') , (λ ()) ]ᵃ ≈⟨ (cright sym assoc) ⟩
  Ex • (CZ^ (- ₁) • w ↑ ↑) • [ (a , d') , (λ ()) ]ᵃ ≈⟨ (((cright cleft  comm⇒pow-comm (toℕ m1) 1 ( lemma-comm-CZ-w↑ w)))) ⟩
  Ex • (w ↑ ↑ • CZ^ (- ₁)) • [ (a , d') , (λ ()) ]ᵃ ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
  (Ex • w ↑ ↑) • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ ≈⟨ ( cleft lemma-comm-Ex-w↑↑ w) ⟩
  (w ↑ ↑ • Ex) • CZ^ (- ₁) • [ (a , d') , (λ ()) ]ᵃ ≈⟨  assoc ⟩
  w ↑ ↑ • [ d ]ᵈ ∎
  where
  open PB ((₃₊ n) QRel,_===_)  
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas3
  open Pattern-Assoc
  m1 : ℤ ₚ
  m1 = - ₁


comm-dbox-w↑↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ d (w : Word (Gen n)) -> [ d ]ᵈ • w ↑ ↑ ≈ w ↑ ↑ • [ d ]ᵈ
comm-dbox-w↑↑ {n} d@(a , b) w = comm-dbox-w↑↑' a b w

-}

-- XM ₁ and ZM ₁ are the same word, since ₁ ⁻¹ is ₁; so XM ₁ collapses
-- for the same reason ZM ₁ does.
lemma-XM1 : let open PB ((₁₊ n) QRel,_===_) in XM {n} (₁ , λ ()) ≈ ε
lemma-XM1 {n} = begin
  XM (₁ , λ ())
    ≡⟨ Eq.cong (\ z -> S^ z • H • S^ ₁ • H • S^ z • H) inv-₁ ⟩
  S^ ₁ • H • S^ ₁ • H • S^ ₁ • H
    ≡⟨ Eq.cong (\ z -> S^ ₁ • H • S^ z • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
  ⟦ (₁ , λ ()) ⟧ₘ ≈⟨ sym lemma-M1 ⟩
  ε ∎
  where
  open Lemmas0 n
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

lemma-A10 : let open PB ((₁₊ n) QRel,_===_) in
  [ (₁ , ₀) , (λ ()) ]ᵃ ≈ H
lemma-A10 {n} = begin
  [ (₁ , ₀) , (λ ()) ]ᵃ ≈⟨ refl ⟩
  XM (₁ , λ ()) • H • S^ -b/a
    ≡⟨ Eq.cong (\ xx -> XM (₁ , λ ()) • H • S^ xx) aux ⟩
  XM (₁ , λ ()) • H • S^ ₀ ≈⟨ cong refl right-unit ⟩
  XM (₁ , λ ()) • H ≈⟨ (cleft lemma-XM1) ⟩
  ε • H ≈⟨ left-unit ⟩
  H ∎
  where
  open Lemmas0 n
  a = ₁
  b = ₀
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a ≡ ₀
  aux = Eq.trans (Eq.cong₂ _*_ (-0#≈0#) inv-₁) auto
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

aux-a≠0⇒ab≠0 : ∀ (a b : ℤ ₚ) (nz : a ≢ ₀) -> _≢_ {A = ℤ ₚ × ℤ ₚ} (a , b) (₀ , ₀)
aux-a≠0⇒ab≠0 a b nz eq0 = ⊥-elim (nz (Eq.cong proj₁ eq0))


lemma-Aa0 : let open PB ((₁₊ n) QRel,_===_) in
  ∀ (a*@(a , nz) : ℤ* ₚ) -> [ (a , ₀) , aux-a≠0⇒ab≠0 a ₀ nz ]ᵃ ≈ ZM (a* ⁻¹) • H
lemma-Aa0 {n} a*@(₀ , nz) = ⊥-elim (nz auto)
lemma-Aa0 {n} a*@(a@(₁₊ _) , nz) = begin
  [ (a , ₀) , aux-a≠0⇒ab≠0 a ₀ nz ]ᵃ ≈⟨ refl ⟩
  XM a* • H • S^ -b/a ≡⟨ Eq.cong (\ xx -> XM a* • H • S^ xx) aux ⟩
  XM a* • H • S^ ₀ ≈⟨ cong refl right-unit ⟩
  XM a* • H ≡⟨ Eq.cong (_• H) (XM≡ZM⁻¹ a*) ⟩
  ⟦ a* ⁻¹ ⟧ₘ • H ∎
  where
  open Lemmas0 n
  b = ₀
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  aux : -b/a ≡ ₀
  aux = Eq.trans (Eq.cong₂ _*_ (-0#≈0#) auto) auto
  open PB ((₁₊ n) QRel,_===_)  
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid


lemma-Ex-M-n : let open PB ((₂₊ n) QRel,_===_) in
  ∀ m -> Ex • ZM m ≈ ZM m ↑ • Ex
lemma-Ex-M-n {n} m@x' = by-emb' (lemma-Ex-M m) aux aux2
  where
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open import Examples.Groups.Symplectic.Lemmas.Embeding-2n p-2 p-prime n

  aux : f* (Ex • ZM m) ≈ Ex • ZM m
  aux = cong refl (lemma-f*-M m)
  aux2 : f* (ZM m ↑ • Ex) ≈ ZM m ↑ • Ex
  aux2 = cong (lemma-f*-M↑ m) refl

