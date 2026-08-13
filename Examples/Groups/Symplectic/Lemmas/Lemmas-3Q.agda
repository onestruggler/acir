{-# OPTIONS --cubical-compatible --safe #-}

import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)


open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Nat.Primality
open import Data.Nat.DivMod
open import Data.Fin.Properties


module Examples.Groups.Symplectic.Lemmas.Lemmas-3Q (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

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


open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4n2 p-2 p-prime as Sym4n

open Lemmas-Sym
open Duality

open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime


rm-mc2 : Cosets2 →  Cosets2
rm-mc2 (case-||ₐ x x₁@(s , mc↑ , mc)) = case-||ₐ x (s , mc↑ , (₁* , ε))
rm-mc2 (case-|| x x₁ x₂@(s , mc↑ , mc)) = case-|| x x₁ (s , mc↑ , (₁* , ε))
rm-mc2 (case-| x x₁@(s , mc)) = case-| x ((s , ₁* , ε))
rm-mc2 (case-nf1 x@(s , mc)) = case-nf1 (s , ₁* , ε)
rm-mc2 x@(case-Ex-nf1 nf1) = x
rm-mc2 x@(case-Ex-| mc nf1) = x

mc-of2 : Cosets2 → MC
mc-of2 (case-||ₐ x x₁@(s , mc↑ , mc)) = mc
mc-of2 (case-|| x x₁ x₂@(s , mc↑ , mc)) = mc
mc-of2 (case-| x x₁@(s , mc)) = mc
mc-of2 (case-nf1 x@(s , mc)) = mc
mc-of2 (case-Ex-nf1 nf1) = ₁* , ε
mc-of2 (case-Ex-| mc nf1) = ₁* , ε

aux-mc-of2 : let open PB ((₂₊ n) QRel,_===_) in ∀ c2 → ⟦ c2 ⟧₂ ≈ ⟦ rm-mc2 c2 ⟧₂ • ⟦ mc-of2 c2 ⟧ₘ₊
aux-mc-of2 {n} (case-||ₐ x x₁@(s , mc↑ , mc)) = begin
  ⟦ case-||ₐ x (s , mc↑ , mc) ⟧₂ ≈⟨ by-passoc (□ ^ 5) (□ ^ 4 • □) auto ⟩
  (CZ^ x  • S^ s  • CX • ⟦ mc↑ ⟧ₘ₊ ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft cright cright cright right-unit) ⟩
  (CZ^ x  • S^ s  • CX • ⟦ mc↑ ⟧ₘ₊ ↑ • ε) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft cright cright cright cright aux-mc1ε) ⟩
  (CZ^ x  • S^ s  • CX • ⟦ mc↑ ⟧ₘ₊ ↑ • ⟦ ₁* , ε ⟧ₘ₊) • ⟦ mc ⟧ₘ₊ ≈⟨ refl ⟩
  ⟦ case-||ₐ x (s , mc↑ , ₁* , ε) ⟧₂ • ⟦ mc ⟧ₘ₊ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc

aux-mc-of2 {n} (case-|| x@(k , nz) l x₂@(s , mc↑ , mc)) =  begin
  ⟦ case-|| x l (s , mc↑ , mc) ⟧₂ ≈⟨ by-passoc (□ ^ 7) (□ ^ 6 • □) auto ⟩
  (CZ^ k  • H ↑ ^ 3 • S^ l ↑ • S^ s  • CX • ⟦ mc↑ ⟧ₘ₊ ↑) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft cright cright cright cright cright right-unit) ⟩
  (CZ^ k  • H ↑ ^ 3 • S^ l ↑  • S^ s  • CX • ⟦ mc↑ ⟧ₘ₊ ↑ • ε) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft cright cright cright cright cright cright aux-mc1ε) ⟩
  (CZ^ k  • H ↑ ^ 3 • S^ l ↑  • S^ s  • CX • ⟦ mc↑ ⟧ₘ₊ ↑ • ⟦ ₁* , ε ⟧ₘ₊) • ⟦ mc ⟧ₘ₊ ≈⟨ refl ⟩
  ⟦ case-|| x l (s , mc↑ , ₁* , ε) ⟧₂ • ⟦ mc ⟧ₘ₊ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
aux-mc-of2 {n} (case-| mc↑ x₁@(s , mc)) = begin
  ⟦ case-| mc↑ (s , mc) ⟧₂ ≈⟨ by-passoc (□ ^ 4) (□ ^ 3 • □) auto ⟩
  (CZ • ⟦ mc↑ ⟧ₘ₊ ↑ • S^ s) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft cright  cright right-unit) ⟩
  (CZ • ⟦ mc↑ ⟧ₘ₊ ↑ • S^ s • ε) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft cright cright cright aux-mc1ε) ⟩
  (CZ • ⟦ mc↑ ⟧ₘ₊ ↑ • S^ s • ⟦ ₁* , ε ⟧ₘ₊) • ⟦ mc ⟧ₘ₊ ≈⟨ refl ⟩
  ⟦ case-| mc↑ (s , ₁* , ε) ⟧₂ • ⟦ mc ⟧ₘ₊ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  
aux-mc-of2 {n} (case-nf1 x@(s , mc)) =  begin
  ⟦ case-nf1 (s , mc) ⟧₂ ≈⟨ refl ⟩
  (S^ s) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft   right-unit) ⟩
  (S^ s • ε) • ⟦ mc ⟧ₘ₊ ≈⟨ sym (cleft   cright aux-mc1ε) ⟩
  (S^ s • ⟦ ₁* , ε ⟧ₘ₊) • ⟦ mc ⟧ₘ₊ ≈⟨ refl ⟩
  ⟦ case-nf1 (s , ₁* , ε) ⟧₂ • ⟦ mc ⟧ₘ₊ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  
aux-mc-of2 {n} (case-Ex-nf1 nf1) = begin
  ⟦ case-Ex-nf1 nf1 ⟧₂ ≈⟨ sym right-unit ⟩
  ⟦ case-Ex-nf1 nf1 ⟧₂ • ε ≈⟨ (cright sym aux-mc1ε) ⟩
  ⟦ case-Ex-nf1 nf1 ⟧₂ • ⟦ ₁* , ε ⟧ₘ₊ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

aux-mc-of2 {n} (case-Ex-| nf1 mc) = begin
  ⟦ case-Ex-| nf1 mc ⟧₂ ≈⟨ sym right-unit ⟩
  ⟦ case-Ex-| nf1 mc ⟧₂ • ε ≈⟨ (cright sym aux-mc1ε) ⟩
  ⟦ case-Ex-| nf1 mc ⟧₂ • ⟦ ₁* , ε ⟧ₘ₊ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

aux-dd : let open PB ((₂₊ n) QRel,_===_) in ∀ d → [ d ]ᵈ ≈ [ d ]ᵈ'
aux-dd {n} d@(a@₀ , b) = begin
  Ex • CZ^ (- b) ≈⟨ ( comm⇒pow-comm 1 (toℕ (- b)) (sym lemma-comm-Ex-CZ-n)) ⟩
  CZ^ (- b) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
aux-dd {n} d@(a@(₁₊ _) , b) = begin
  Ex • CZ^ (- a) • H • S^ -b/a ≈⟨ sym assoc ⟩
  (Ex • CZ^ (- a)) • H • S^ -b/a ≈⟨ (cleft comm⇒pow-comm 1 (toℕ (- a)) (sym (lemma-comm-Ex-CZ-n))) ⟩
  (CZ^ (- a) • Ex) • H • S^ -b/a ≈⟨ assoc ⟩
  CZ^ (- a) • Ex • H • S^ -b/a ≈⟨ cright sym assoc ⟩
  CZ^ (- a) • (Ex • H) • S^ -b/a ≈⟨ cright (cleft lemma-Ex-H) ⟩
  CZ^ (- a) • (H ↑ • Ex) • S^ -b/a ≈⟨ cright assoc ⟩
--  CZ^ (- a) • H ↑ • S ↑ ^ toℕ -b/a • Ex ≈⟨ {!!} ⟩
  CZ^ (- a) • H ↑ • Ex • S^ -b/a ≈⟨ (cright cright lemma-Ex-S^ᵏ n -b/a) ⟩
  CZ^ (- a) • H ↑ • S^ -b/a ↑ • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


{-
aux-dd : let open PB ((₂₊ n) QRel,_===_) in ∀ d → [ d ]ᵈ ≈ [ d ]ᵈ'
aux-dd {n} d@(₀ , ₀) = PB.refl
aux-dd {n} d@(a@₀ , b@(₁₊ _)) = begin
  Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ≈⟨ sym assoc ⟩
  (Ex • CZ^ (- ₁)) • [ (a , b) , (λ ()) ]ᵃ ≈⟨ (cleft comm⇒pow-comm 1 (toℕ (- ₁)) (sym (lemma-comm-Ex-CZ-n))) ⟩
  (CZ^ (- ₁) • Ex) • [ (a , b) , (λ ()) ]ᵃ ≈⟨ assoc ⟩
  CZ^ (- ₁) • Ex • [ (a , b) , (λ ()) ]ᵃ ≈⟨ (cright Sym4n.lemma-Ex-MC n ((b , λ ()) ⁻¹ , ε)) ⟩
  CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
aux-dd {n} d@(a@(₁₊ _) , b) = begin
  Ex • CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ≈⟨ sym assoc ⟩
  (Ex • CZ^ (- ₁)) • [ (a , b) , (λ ()) ]ᵃ ≈⟨ (cleft comm⇒pow-comm 1 (toℕ (- ₁)) (sym (lemma-comm-Ex-CZ-n))) ⟩
  (CZ^ (- ₁) • Ex) • [ (a , b) , (λ ()) ]ᵃ ≈⟨ assoc ⟩
  CZ^ (- ₁) • Ex • [ (a , b) , (λ ()) ]ᵃ ≈⟨ (cright Sym4n.lemma-Ex-MC n ((a , λ ()) ⁻¹ , HS^ -b/a)) ⟩
  CZ^ (- ₁) • [ (a , b) , (λ ()) ]ᵃ ↑ • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

-}

aux-comm-CZ-S^k↑ : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k → CZ • S^ k ↑ ≈ S^ k ↑ • CZ
aux-comm-CZ-S^k↑ {n} k = begin
   CZ • S^ k ↑ ≈⟨ (cright sym (refl' (lemma-^-↑ S (toℕ k)))) ⟩
   CZ • S ↑ ^ toℕ k ≈⟨ comm⇒pow-comm 1 (toℕ k) (axiom comm-CZ-S↑) ⟩
   S ↑ ^ toℕ k • CZ ≈⟨ (cleft refl' (lemma-^-↑ S (toℕ k))) ⟩
   S^ k ↑ • CZ ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


aux-CZ^-k : let open PB ((₂₊ n) QRel,_===_) in
  ∀ k → CZ⁻¹ ^ toℕ k ≈ CZ^ (- k)
aux-CZ^-k {n} k = begin
  CZ⁻¹ ^ toℕ k ≈⟨ ^^ CZ p-1 (toℕ k) ⟩
  CZ ^ (p-1 Nat.* toℕ k) ≈⟨ lemma-CZ^k-% (p-1 Nat.* toℕ k) ⟩
  CZ ^ ((p-1 Nat.* toℕ k) Nat.% p) ≡⟨ Eq.cong (CZ ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (p-1 Nat.* toℕ k) p))) ⟩
  CZ ^ toℕ (fromℕ< (m%n<n (p-1 Nat.* toℕ k) p)) ≡⟨ auto ⟩
  CZ^ (fromℕ< (m%n<n (p-1 Nat.* toℕ k) p)) ≡⟨ Eq.cong (\ xx → CZ^ (fromℕ< (m%n<n (xx Nat.* toℕ k) p))) (Eq.sym lemma-toℕ-1ₚ) ⟩
  CZ^ (fromℕ< (m%n<n (toℕ (- 1ₚ) Nat.* toℕ k) p)) ≡⟨ auto ⟩
  CZ^ (- 1ₚ * k) ≡⟨ Eq.cong CZ^ (-1*x≈-x k) ⟩
  CZ^ (- k) ∎
  where
  open PB ((₂₊ n) QRel,_===_)  
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Lemmas-2Q n
