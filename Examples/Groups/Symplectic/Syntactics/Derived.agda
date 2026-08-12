------------------------------------------------------------------------
-- Presentations of groups
--
-- Derived rules at width 0, and the rewriting tactic that proves them.
--
-- The step relation feeding Presentation.Tactic.Rewriting, and the
-- lemmas about S-powers, H and CZ that it discharges.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_)

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃ ; Σ-syntax)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality

open import Notations
import Circuit.Base

module Examples.Groups.Symplectic.Syntactics.Derived (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Syntactics.Gates p-2 p-prime

module Rewriting-Sym0 where

  -- This module provides a complete rewrite system for 1-qubit
  -- Swap operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  variable
    n : ℕ

  open Symplectic
  open Rewriting
  
  
  step-sym0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  -- step-sym0 ((S-gen) ∷ (S-gen) ∷ (S-gen) ∷ xs) = just (xs , at-head (PB.axiom order-S))
  -- step-sym0 ((S-gen ↥) ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-S)))
  -- step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-S))))
  step-sym0 ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
  step-sym0 ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))
  -- step-sym0 ((CZ-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs) = just (xs , at-head (PB.axiom order-CZ))
  -- step-sym0 ((CZ-gen ↥) ∷ (CZ-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-CZ)))

  step-sym0 ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
  step-sym0 ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

--  step-sym0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (PB.axiom order-Ex))
--  step-sym0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-Ex)))

  -- Commuting of generators.
  step-sym0 ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↓)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom comm-CZ-S↑)))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↓))))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-CZ-S↑))))

  step-sym0 ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))

  -- step-sym0 ((EX-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-CZ))
  -- step-sym0 ((EX-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (EX-gen ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-sym0 ((EX-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (EX-gen ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (EX-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (EX-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  -- step-sym0 ((EX-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (EX-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  -- step-sym0 ((EX-gen ↥ ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (EX-gen ↥ ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-CZ))))
  -- step-sym0 ((H-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))
  -- step-sym0 ((S-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))
  -- step-sym0 ((CZ-gen ↥ ↥) ∷ (EX-gen) ∷ xs) = just ((EX-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-EX))

  step-sym0 ((S-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))
  step-sym0 ((S-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((H-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-H)))
  step-sym0 ((H-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom comm-S)))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-H))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-H))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ comm-S))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom comm-S))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom comm-CZ)))
  step-sym0 ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom selinger-c12)))

  step-sym0 ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom comm-HHS)))
  step-sym0 ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ comm-HHS))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (cong↑ comm-HHS)))))

  -- Others.
--  step-sym0 ((CZ-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↓))
--  step-sym0 ((CZ-gen) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ (CZ-gen) ∷ xs , at-head (PB.axiom semi-CZ-HH↑))

  -- step-sym0 ((CZ-gen) ∷ (H-gen) ∷ (CZ-gen) ∷ xs) = just ((S-gen) ∷ (S-gen) ∷ H-gen ∷ (S-gen) ∷ (S-gen) ∷ CZ-gen ∷ H-gen ∷ S-gen ∷ S-gen ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom selinger-c11 ))
  -- step-sym0 ((CZ-gen ↥) ∷ (H-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c11 )))
  -- step-sym0 ((CZ-gen) ∷ (H-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥) ∷ H-gen ↥ ∷ (S-gen ↥) ∷ (S-gen ↥) ∷ CZ-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ S-gen ∷ S-gen ∷ xs , at-head (PB.axiom selinger-c10 ))
  -- step-sym0 ((CZ-gen ↥) ∷ (H-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ H-gen ↥ ↥ ∷ (S-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ CZ-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ S-gen ↥ ∷ S-gen ↥ ∷ xs , at-head (PB.axiom (cong↑ selinger-c10 )))

  -- Catch-all
  step-sym0 _ = nothing

module Sym0-Rewriting (n : ℕ) where
  open Symplectic
  open Rewriting
  open Rewriting-Sym0 hiding (n)
  open Rewriting.Step (step-cong (step-sym0 {n})) renaming (general-rewrite to rewrite-sym0) public


module Lemmas0 (n : ℕ) where

  open Symplectic
--  open Symplectic-GroupLike
  open import ForStdlib.Data.Fin.Mod

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Pattern-Assoc
  open import Data.Nat.DivMod
  open import Data.Fin.Properties


  lemma-S^k+l : ∀ k l → S^ k • S^ l ≈ S^ (k + l)
  lemma-S^k+l k l = begin
    S^ k • S^ l ≈⟨ refl ⟩
    S ^ toℕ k • S ^ toℕ l ≈⟨ sym (^-+ S (toℕ k) (toℕ l)) ⟩
    S ^ (toℕ k Nat.+ toℕ l) ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k+l p) ⟩
    S ^ (k+l Nat.% p Nat.+ (k+l Nat./ p) Nat.* p) ≈⟨ ^-+ S (k+l Nat.% p) (((k+l Nat./ p) Nat.* p)) ⟩
    S ^ (k+l Nat.% p) • S ^ ((k+l Nat./ p) Nat.* p) ≈⟨ cong (refl' (Eq.cong (S ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k+l p))))) (refl' (Eq.cong (S ^_) (NP.*-comm ((k+l Nat./ p)) p))) ⟩
    S ^ toℕ (fromℕ< (m%n<n k+l p)) • S ^ (p Nat.* (k+l Nat./ p) ) ≈⟨ cong (sym (refl)) (sym (^^ S p (k+l Nat./ p))) ⟩
    S^ (k + l) • (S ^ p) ^ (k+l Nat./ p) ≈⟨ cright (^-cong (S ^ p) ε (k+l Nat./ p) (axiom order-S)) ⟩
    S^ (k + l) • ε ^ (k+l Nat./ p) ≈⟨ cright ε^k=ε (k+l Nat./ p) ⟩
    S^ (k + l) • ε ≈⟨ right-unit ⟩
    S^ (k + l) ∎
    where
    k+l = toℕ k Nat.+ toℕ l
    open SR word-setoid


  lemma-S^k-k : ∀ k → S^ k • S^ (- k) ≈ ε
  lemma-S^k-k k = begin
    S^ k • S^ (- k) ≈⟨ lemma-S^k+l k (- k) ⟩
    S^ (k + - k) ≡⟨ Eq.cong S^ (+-inverseʳ k) ⟩
    S^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid
    k-k = toℕ k Nat.+ toℕ (- k)

  lemma-S^-k+k : ∀ k → S^ (- k) • S^ k ≈ ε
  lemma-S^-k+k k = begin
    S^ (- k) • S^ k ≈⟨ refl ⟩
    S ^ toℕ (- k) • S ^ toℕ k ≈⟨ comm⇒pow-comm (toℕ (- k)) (toℕ ( k)) refl ⟩
    S ^ toℕ k • S ^ toℕ (- k) ≈⟨ refl ⟩
    S^ k • S^ (- k) ≈⟨ lemma-S^k-k k ⟩
    ε ∎
    where
    open SR word-setoid

  open Eq using (_≢_)

  ₁⁻¹ = ((₁ , λ ()) ⁻¹) .proj₁

  
  lemma-M1 : ε ≈ M (₁ , λ ())
  lemma-M1 = begin
    ε ≈⟨ _≈_.sym (axiom order-SH) ⟩
    (S • H) ^ 3 ≈⟨ by-assoc auto ⟩
    S • H • S • H • S • H ≡⟨ auto ⟩
    S^ ₁ • H • S^ ₁ • H • S^ ₁ • H ≡⟨ Eq.cong (\ xx → S^ ₁ • H • S^ xx • H • S^ ₁ • H) (Eq.sym inv-₁) ⟩
    S^ ₁ • H • S^ ₁⁻¹ • H • S^ ₁ • H ≈⟨ refl ⟩
    M (₁ , λ ()) ∎
    where
    open SR word-setoid


  lemma-[H⁻¹S⁻¹]^3 : (H⁻¹ • S⁻¹) ^ 3 ≈ ε
  lemma-[H⁻¹S⁻¹]^3 = begin
    (H⁻¹ • S⁻¹) ^ 3 ≈⟨ sym left-unit ⟩
    ε • (H⁻¹ • S⁻¹) ^ 3 ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    (S • H) ^ 3 • (H⁻¹ • S⁻¹) ^ 3 ≈⟨ rewrite-sym0 100 auto ⟩
    ((S • H • S • H • S) • (H • H⁻¹)) • S⁻¹ • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ ( cleft trans (cright axiom order-H) (by-assoc auto)) ⟩
    ((S • H • S • H) • S) • S⁻¹ • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • H) • (S • S⁻¹) • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ (cright cleft axiom order-S) ⟩
    (S • H • S • H) • ε • (H⁻¹ • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • H • H⁻¹) • S⁻¹ • (H⁻¹ • S⁻¹) ≈⟨ (cleft cright cright cright axiom order-H) ⟩
    (S • H • S • ε) • S⁻¹ • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • S • S⁻¹) • (H⁻¹ • S⁻¹) ≈⟨ (cleft cright cright axiom order-S) ⟩
    (S • H • ε) • (H⁻¹ • S⁻¹) ≈⟨ by-assoc auto ⟩
    (S • H • H⁻¹) • S⁻¹ ≈⟨ (cleft cright axiom order-H) ⟩
    (S • ε) • S⁻¹ ≈⟨ by-assoc auto ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
    open SR word-setoid
    open Sym0-Rewriting n


  lemma-[S⁻¹H⁻¹]^3 : (S⁻¹ • H⁻¹) ^ 3 ≈ ε
  lemma-[S⁻¹H⁻¹]^3 = begin
    (S⁻¹ • H⁻¹) ^ 3 ≈⟨ sym (trans (cright trans (comm⇒pow-comm p-1 1 refl) (axiom order-S)) right-unit) ⟩
    (S⁻¹ • H⁻¹) ^ 3 • (S⁻¹ • S) ≈⟨ by-passoc ((□ • □) ^ 3 • □ • □) (□ • (□ • □) ^ 3 • □) auto ⟩
    S⁻¹ • (H⁻¹ • S⁻¹) ^ 3 • S ≈⟨ cright cleft lemma-[H⁻¹S⁻¹]^3 ⟩
    S⁻¹ • ε • S ≈⟨ by-assoc auto ⟩
    S⁻¹ • S ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
    S • S⁻¹ ≈⟨ axiom order-S ⟩
    ε ∎
    where
--    open Group-Lemmas _ grouplike renaming (_⁻¹ to winv)
    open SR word-setoid

  lemma-S⁻¹ : S⁻¹ ≈ S^ ₚ₋₁
  lemma-S⁻¹ = begin
    S⁻¹ ≈⟨ refl ⟩
    S ^ p-1 ≡⟨ Eq.cong (S ^_) (Eq.sym lemma-toℕ-ₚ₋₁) ⟩
    S ^ toℕ ₚ₋₁ ≡⟨ Eq.refl ⟩
    S^ ₚ₋₁ ∎
    where
    open SR word-setoid

  lemma-HH-M-1 : let -'₁ = -' ((₁ , λ ())) in HH ≈ M -'₁
  lemma-HH-M-1 = begin
    HH ≈⟨ trans (sym right-unit) (cright sym lemma-[S⁻¹H⁻¹]^3) ⟩
    HH • (S⁻¹ • H⁻¹) ^ 3 ≈⟨ (cright ^-cong (S⁻¹ • H⁻¹) (S⁻¹ • H • HH) 3 refl) ⟩
    HH • (S⁻¹ • H • HH) ^ 3 ≈⟨ refl ⟩
    HH • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) • (S⁻¹ • H • HH) ≈⟨ (cright cong (cright sym assoc) (by-passoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto)) ⟩
    HH • (S⁻¹ • HH • H) • (S⁻¹ • H) • (HH • S⁻¹) • H • HH ≈⟨ (cright cong (sym assoc) (cright cleft comm⇒pow-comm 1 p-1 (trans assoc (axiom comm-HHS)))) ⟩
    HH • ((S⁻¹ • HH) • H) • (S⁻¹ • H) • (S⁻¹ • HH) • H • HH ≈⟨ (cright cong (cleft comm⇒pow-comm p-1 1 (sym (trans assoc (axiom comm-HHS)))) (cright assoc)) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • HH • H • HH ≈⟨ (cright cright cright cright rewrite-sym0 100 auto) ⟩
    HH • ((HH • S⁻¹) • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ by-passoc (□ • (□ ^ 2 • □) • □) (□ ^ 2 • □ ^ 2 • □) auto ⟩
    (HH • HH) • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ (cleft rewrite-sym0 100 auto) ⟩
    ε • (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ left-unit ⟩
    (S⁻¹ • H) • (S⁻¹ • H) • S⁻¹ • H ≈⟨ by-passoc ((□ ^ 2) ^ 3) (□ ^ 6) auto ⟩
    S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ≈⟨ cong lemma-S⁻¹ (cright cong lemma-S⁻¹ (cright cong lemma-S⁻¹ refl)) ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ ₚ₋₁ • H ≡⟨ Eq.cong (\ xx → S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ xx • H) p-1=-1ₚ ⟩
    S^ ₚ₋₁ • H • S^ ₚ₋₁ • H • S^ -₁ • H ≡⟨ Eq.cong₂ (\ xx yy → S^ xx • H • S^ yy • H • S^ -₁ • H) (p-1=-1ₚ) p-1=-1ₚ ⟩
    S^ -₁ • H • S^ -₁ • H • S^ -₁ • H ≡⟨ Eq.cong (\ xx → S^ -₁ • H • S^ xx • H • S^ -₁ • H) (Eq.sym aux-₁⁻¹) ⟩
    S^ -₁ • H • S^ -₁⁻¹ • H • S^ -₁ • H ≈⟨ refl ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.refl ⟩
    M x' ∎
    where
    open Sym0-Rewriting n


    x' = -'₁
    -₁ = -'₁ .proj₁
    -₁⁻¹ = (-'₁ ⁻¹) .proj₁
    x = x' .proj₁
    x⁻¹ = (x' ⁻¹) .proj₁
    open SR word-setoid


  aux-M≡M : ∀ y y' → y .proj₁ ≡ y' .proj₁ → M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    S^ x • H • S^ x⁻¹ • H • S^ x • H ≡⟨ Eq.cong₂ (\ xx yy → S^ xx • H • S^ yy • H • S^ x • H) eq aux-eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x • H ≡⟨ Eq.cong (\ xx → S^ x' • H • S^ x'⁻¹ • H • S^ xx • H) eq ⟩
    S^ x' • H • S^ x'⁻¹ • H • S^ x' • H ≡⟨ auto ⟩
    M y' ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )
    aux-eq : x⁻¹ ≡ x'⁻¹
    aux-eq  = begin
      x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
      x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
      x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx → (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎


  lemma-M-power : ∀ (x : ℤ* ₚ) k → let x' = x .proj₁ in  M x ^ k ≈ M (x ^' k)
  lemma-M-power x k@0 = lemma-M1 
  lemma-M-power x k@1 = begin
    M x ^ 1 ≡⟨ aux-M≡M x (x ^' 1) (Eq.sym (lemma-x^′1=x (x .proj₁))) ⟩
    M (x ^' 1) ∎
    where
    open SR word-setoid
  lemma-M-power x k@(₂₊ k') = begin
    M x • M x ^ ₁₊ k' ≈⟨ (cright lemma-M-power x (₁₊ k')) ⟩
    M x • M (x ^' ₁₊ k') ≈⟨ axiom (M-mul x (x ^' ₁₊ k')) ⟩
    M (x *' (x ^' ₁₊ k')) ≡⟨ aux-M≡M (x *' (x ^' ₁₊ k')) (x ^' ₂₊ k') auto ⟩
    M (x ^' ₂₊ k') ∎
    where
    open SR word-setoid


  derived-D : ∀ x → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    H • S^ x • H ≈ H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹
  derived-D  x nz = begin
    H • S^ x • H ≈⟨ (cright cright sym right-unit) ⟩
    H • S^ x • H • ε ≈⟨ cright cright cright sym (lemma-S^k-k x⁻¹) ⟩
    H • S^ x • H • S^ x⁻¹ • S^ -x⁻¹ ≈⟨ cright cright cright cright sym left-unit ⟩
    H • S^ x • H • S^ x⁻¹ • ε • S^ -x⁻¹ ≈⟨ cright cright cright cright sym (cong (axiom order-H) refl) ⟩
    H • S^ x • H • S^ x⁻¹ • H ^ 4 • S^ -x⁻¹ ≈⟨ (cright cright cright cright by-passoc (□ ^ 4 • □) (□ • □ ^ 3 • □) auto) ⟩
    H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ∎
    where
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹ 
    open SR word-setoid

  derived-5 : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S ^ k ≈ S ^ (k Nat.* toℕ (x * x)) • M (x , nz)
  derived-5 x k@0 nz = trans right-unit (sym left-unit)
  derived-5 x k@1 nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S ≈⟨ axiom (semi-MS (x , nz)) ⟩
    S^ (x * x) • M (x , nz) ≈⟨ refl ⟩
    S ^ toℕ (x * x) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym ( NP.*-identityˡ (toℕ (x * x)))))) ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
  derived-5 x k@(₂₊ k') nz = begin  
    M (x , nz) • S ^ k ≈⟨ refl ⟩
    M (x , nz) • S • S ^ ₁₊ k' ≈⟨ sym assoc ⟩
    (M (x , nz) • S) • S ^ ₁₊ k' ≈⟨ (cleft derived-5 x 1 nz) ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • M (x , nz)) • S ^ ₁₊ k' ≈⟨ assoc ⟩
    S ^ (1 Nat.* toℕ (x * x)) • M (x , nz) • S ^ ₁₊ k' ≈⟨ (cright derived-5 x (₁₊ k') nz) ⟩
    S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ sym assoc ⟩
    (S ^ (1 Nat.* toℕ (x * x)) • S ^ (₁₊ k' Nat.* toℕ (x * x))) • M (x , nz) ≈⟨ (cleft sym (^-+ S ((1 Nat.* toℕ (x * x))) ((₁₊ k' Nat.* toℕ (x * x))))) ⟩
    (S ^ ((1 Nat.* toℕ (x * x)) Nat.+ (₁₊ k' Nat.* toℕ (x * x)))) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (Eq.sym (NP.*-distribʳ-+ (toℕ (x * x)) ₁ (₁₊ k'))))) ⟩
    S ^ ((1 Nat.+ ₁₊ k') Nat.* toℕ (x * x) ) • M (x , nz) ≈⟨ refl ⟩
    S ^ (k Nat.* toℕ (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid

  lemma-S^k-% : ∀ k → S ^ k ≈ S ^ (k % p)
  lemma-S^k-% k = begin
    S ^ k ≡⟨ Eq.cong (S ^_) (m≡m%n+[m/n]*n k p) ⟩
    S ^ (k Nat.% p Nat.+ k Nat./ p Nat.* p) ≈⟨ ^-+ S (k Nat.% p) (k Nat./ p Nat.* p) ⟩
    S ^ (k Nat.% p) • S ^ (k Nat./ p Nat.* p) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm (k Nat./ p) p))) ⟩
    S ^ (k Nat.% p) • S ^ (p Nat.* (k Nat./ p)) ≈⟨ sym (cright ^^ S p (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • (S ^ p) ^ (k Nat./ p) ≈⟨ (cright ^-cong (S ^ p) ε (k Nat./ p) (axiom order-S)) ⟩
    S ^ (k Nat.% p) • (ε) ^ (k Nat./ p) ≈⟨ (cright ε^k=ε (k Nat./ p)) ⟩
    S ^ (k Nat.% p) • ε ≈⟨ right-unit ⟩
    S ^ (k % p) ∎
    where
    open SR word-setoid


  lemma-MS^k : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ k ≈ S^ (k * (x * x)) • M (x , nz)
  lemma-MS^k x k nz = begin 
    M (x , nz) • S^ k ≈⟨ refl ⟩
    M (x , nz) • S ^ toℕ k ≈⟨ derived-5 x (toℕ k) nz ⟩
    S ^ (toℕ k Nat.* toℕ (x * x)) • M (x , nz) ≈⟨ (cleft lemma-S^k-% (toℕ k Nat.* toℕ (x * x))) ⟩
    S ^ ((toℕ k Nat.* toℕ (x * x)) % p) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong (S ^_) (lemma-toℕ-% k (x * x)))) ⟩
    S ^ toℕ (k * (x * x)) • M (x , nz) ≈⟨ refl ⟩
    S^ (k * (x * x)) • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹

  lemma-MS^k' : ∀ x k → (nz : x ≢ ₀) → let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in
    M (x , nz) • S^ (k * (x⁻¹ * x⁻¹)) ≈ S^ k • M (x , nz)
  lemma-MS^k' x k nz = begin 
    M (x , nz) • S^ (k * (x⁻¹ * x⁻¹)) ≈⟨ lemma-MS^k x (k * (x⁻¹ * x⁻¹)) nz ⟩
    S^ (k * (x⁻¹ * x⁻¹) * (x * x)) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong S^ (Eq.trans (*-assoc k (x⁻¹ * x⁻¹)  (x * x)) (Eq.cong (k *_) (aux-xxxx (x , nz)))))) ⟩
    S^ (k * ₁) • M (x , nz) ≈⟨ (cleft refl' (Eq.cong S^ (*-identityʳ k))) ⟩
    S^ k • M (x , nz) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹


  lemma-S^ab : ∀ (a b : ℤ ₚ) → S ^ toℕ (a * b) ≈ S ^ (toℕ a Nat.* toℕ b)
  lemma-S^ab a b = begin
    S ^ toℕ (a * b) ≡⟨ auto ⟩
    S ^ toℕ (fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ≡⟨ Eq.cong (S ^_) (toℕ-fromℕ< (m%n<n (toℕ a Nat.* toℕ b) p)) ⟩
    S ^ ((toℕ a Nat.* toℕ b) % p) ≈⟨ sym right-unit ⟩
    S ^ (ab Nat.% p) • ε ≈⟨ (cright sym (ε^k=ε (ab Nat./ p))) ⟩
    S ^ (ab Nat.% p) • (ε) ^ (ab Nat./ p) ≈⟨ (cright sym (^-cong (S ^ p) ε (ab Nat./ p) (axiom order-S))) ⟩
    S ^ (ab Nat.% p) • (S ^ p) ^ (ab Nat./ p) ≈⟨ (cright ^^ S p (ab Nat./ p)) ⟩
    S ^ (ab Nat.% p) • S ^ (p Nat.* (ab Nat./ p)) ≈⟨ (cright refl' (Eq.cong (S ^_) (NP.*-comm p (ab Nat./ p)))) ⟩
    S ^ (ab Nat.% p) • S ^ (ab Nat./ p Nat.* p) ≈⟨ sym (^-+ S (ab Nat.% p) (ab Nat./ p Nat.* p)) ⟩
    S ^ (ab Nat.% p Nat.+ ab Nat./ p Nat.* p) ≡⟨ Eq.cong (S ^_) (Eq.sym (m≡m%n+[m/n]*n ab p)) ⟩
    S ^ (toℕ a Nat.* toℕ b) ∎
    where
    ab = toℕ a Nat.* toℕ b
    open SR word-setoid


  derived-7 : ∀ x y → (nz : x ≢ ₀) → (nzy : y ≢ ₀) → let -'₁ = -' ((₁ , λ ())) in let x⁻¹ = ((x , nz) ⁻¹) .proj₁ in let -x⁻¹ = - x⁻¹ in let -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) in let -y/x = -y/x' .proj₁ in
  
    M (y , nzy) • H • S^ x • H ≈ S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹)
    
  derived-7 x y nzx nzy = begin
    M (y , nzy) • H • S^ x • H ≈⟨ (cright derived-D x nzx) ⟩
    M (y , nzy) • H • S^ x • H • S^ x⁻¹ • H • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright by-passoc (□ • □ • □ • □ • □ • □ • □) (□ ^ 5 • □ • □) auto) ⟩
    M (y , nzy) • (H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft sym left-unit) ⟩
    M (y , nzy) • (ε • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft cleft sym (lemma-S^-k+k x⁻¹)) ⟩
    M (y , nzy) • ((S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ by-passoc (□ • (□ ^ 2 • □ ^ 5) • □) (□ ^ 2 • □ ^ 6 • □) auto ⟩
    (M (y , nzy) • S^ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ refl ⟩
    (M (y , nzy) • S ^ toℕ -x⁻¹) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cleft derived-5 y (toℕ -x⁻¹) nzy) ⟩
    (S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M (y , nzy)) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H) • H ^ 3 • S^ -x⁻¹ ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • (S^ x⁻¹ • H • S^ x • H • S^ x⁻¹ • H)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft (cright (cright cright cleft refl' (Eq.cong S^ (Eq.sym (inv-involutive ((x , nz)))))))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (y , nzy) • M ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (y , nzy) ((x , nz) ⁻¹))) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • M ((y , nzy) *' ((x , nz) ⁻¹)) • H ^ 3 • S^ -x⁻¹ ≈⟨ (cright by-passoc (□ • □ ^ 3 • □) (□ ^ 3 • □ ^ 2) auto) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • HH) • H • S^ -x⁻¹ ≈⟨ (cright cleft (cright lemma-HH-M-1)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M ((y , nzy) *' ((x , nz) ⁻¹)) • M -'₁) • H • S^ -x⁻¹ ≈⟨ (cright cleft axiom (M-mul (((y , nzy) *' ((x , nz) ⁻¹))) -'₁)) ⟩
    S ^ (toℕ -x⁻¹ Nat.* toℕ (y * y)) • (M (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁) ) • H • S^ -x⁻¹ ≈⟨ (cleft sym (lemma-S^ab -x⁻¹ (y * y))) ⟩
    S ^ toℕ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ≈⟨ refl ⟩
    S^ (-x⁻¹ * (y * y)) • M -y/x' • (H • S^ -x⁻¹) ∎
    where
    open SR word-setoid
    nz = nzx
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    x⁻¹⁻¹ = (((x , nz) ⁻¹) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    -y/x' = (((y , nzy) *' ((x , nz) ⁻¹)) *' -'₁)
    -y/x = -y/x' .proj₁

  aux-MM : ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) → x ≡ y → M (x , nzx) ≈ M (y , nzy)
  aux-MM {x} {y} nz1 nz2 eq rewrite eq = refl


  aux-M-mul : ∀ m → M m • M (m ⁻¹) ≈ ε
  aux-M-mul m = begin
    M m • M (m ⁻¹) ≈⟨ axiom (M-mul m ( m ⁻¹)) ⟩
    M (m *' m ⁻¹) ≈⟨ aux-MM ((m *' m ⁻¹) .proj₂) (λ ()) (lemma-⁻¹ʳ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ sym lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid

  aux-M-mulˡ : ∀ m → M (m ⁻¹) • M m ≈ ε
  aux-M-mulˡ m = begin
    M (m ⁻¹) • M m ≈⟨ axiom (M-mul ( m ⁻¹) m) ⟩
    M (m ⁻¹ *' m) ≈⟨ aux-MM ((m ⁻¹ *' m) .proj₂) (λ ()) (lemma-⁻¹ˡ (m ^1) {{nztoℕ {y = m ^1} {neq0 = m .proj₂}}}) ⟩
    M₁ ≈⟨ sym lemma-M1 ⟩
    ε ∎
    where
    open SR word-setoid


  semi-HM : ∀ (x : ℤ* ₚ) → H • M x ≈ M (x ⁻¹) • H
  semi-HM x' = begin
    H • (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ by-passoc (□ • □ ^ 6) (□ ^ 3 • □ ^ 4) auto ⟩
    (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ (trans (sym left-unit) (cong lemma-M1 refl)) ⟩
    M₁ • (H • S^ x • H) • S^ x⁻¹ • H • S^ x • H ≈⟨ sym assoc ⟩
    (M₁ • (H • S^ x • H)) • S^ x⁻¹ • H • S^ x • H ≈⟨ (cleft derived-7 x ₁ (x' .proj₂) λ ()) ⟩
    (S^ (-x⁻¹ * (₁ * ₁)) • M (((₁ , λ ()) *' x' ⁻¹) *' -'₁) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ cleft (cright (cleft aux-MM ((((₁ , λ ()) *' x' ⁻¹) *' -'₁) .proj₂) ((-' (x' ⁻¹)) .proj₂) aux-a1)) ⟩
    (S^ (-x⁻¹ * ₁) • M (-' (x' ⁻¹)) • H • S^ -x⁻¹) • S^ x⁻¹ • H • S^ x • H ≈⟨ by-passoc (□ ^ 4 • □ ^ 4) (□ • □ ^ 4 • □ ^ 3) auto ⟩
    S^ (-x⁻¹ * ₁) • (M (-' (x' ⁻¹)) • H • S^ -x⁻¹ • S^ x⁻¹) • H • S^ x • H ≈⟨ cong (refl' (Eq.cong S^ (*-identityʳ -x⁻¹))) (cleft cright (cright lemma-S^-k+k x⁻¹)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • ε) • H • S^ x • H ≈⟨ (cright cleft (cright right-unit)) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H) • H • S^ x • H ≈⟨ (cright by-passoc (□ ^ 2 • □ ^ 3) (□ ^ 3 • □ ^ 2) auto) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • H • H) • S^ x • H ≈⟨ (cright cleft cright lemma-HH-M-1) ⟩
    S^ -x⁻¹ • (M (-' (x' ⁻¹)) • M -'₁) • S^ x • H ≈⟨ (cright cleft axiom (M-mul (-' (x' ⁻¹)) -'₁)) ⟩
    S^ -x⁻¹ • M (-' (x' ⁻¹) *' -'₁) • S^ x • H ≈⟨ (cright cleft aux-MM ((-' (x' ⁻¹) *' -'₁) .proj₂) ((x' ⁻¹) .proj₂) aux-a2) ⟩
    S^ -x⁻¹ • M (x' ⁻¹) • S^ x • H ≈⟨ sym (cong refl assoc) ⟩
    S^ -x⁻¹ • (M (x' ⁻¹) • S^ x) • H ≈⟨ (cright cleft lemma-MS^k x⁻¹ x ((x' ⁻¹) .proj₂)) ⟩
    S^ -x⁻¹ • (S^ (x * (x⁻¹ * x⁻¹)) • M (x' ⁻¹)) • H ≈⟨ (cright cleft (cleft refl' (Eq.cong S^ aux-a3))) ⟩
    S^ -x⁻¹ • (S^ x⁻¹ • M (x' ⁻¹)) • H ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
    (S^ -x⁻¹ • S^ x⁻¹) • M (x' ⁻¹) • H ≈⟨ (cleft lemma-S^-k+k x⁻¹) ⟩
    ε • M (x' ⁻¹) • H ≈⟨ left-unit ⟩
    M (x' ⁻¹) • H ∎
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )
    open Pattern-Assoc
    -x = - x
    -x⁻¹ = - x⁻¹
    aux-a1 : ₁ * x⁻¹ * (-'₁ .proj₁) ≡ -x⁻¹
    aux-a1 = begin
      ₁ * x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (\ xx → xx * (-'₁ .proj₁)) (*-identityˡ x⁻¹) ⟩
      x⁻¹ * (-'₁ .proj₁) ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym p-1=-1ₚ) ⟩
      x⁻¹ * ₋₁ ≡⟨ *-comm x⁻¹ ₋₁ ⟩
      ₋₁ * x⁻¹ ≡⟨ auto ⟩
      -x⁻¹ ∎
      where open ≡-Reasoning

    aux-a2 : -x⁻¹ * - ₁ ≡ x⁻¹
    aux-a2 = begin
      -x⁻¹ * - ₁ ≡⟨ *-comm -x⁻¹ (- ₁) ⟩
      - ₁ * -x⁻¹ ≡⟨ -1*x≈-x -x⁻¹ ⟩
      - -x⁻¹ ≡⟨ -‿involutive x⁻¹ ⟩
      x⁻¹ ∎
      where
      open ≡-Reasoning
      open import Algebra.Properties.Ring (+-*-ring p-2)


    aux-a3 : x * (x⁻¹ * x⁻¹) ≡ x⁻¹
    aux-a3 = begin
      x * (x⁻¹ * x⁻¹) ≡⟨ Eq.sym (*-assoc x x⁻¹ x⁻¹) ⟩
      x * x⁻¹ * x⁻¹ ≡⟨ Eq.cong (_* x⁻¹) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) ⟩
      ₁ * x⁻¹ ≡⟨ *-identityˡ x⁻¹ ⟩
      x⁻¹ ∎
      where open ≡-Reasoning

    open SR word-setoid

  aux-comm-MM' : ∀ m m' → M m • M m' ≈ M m' • M m
  aux-comm-MM' m m' = begin
    M m • M m' ≈⟨ axiom (M-mul m m') ⟩
    M (m *' m') ≈⟨ aux-MM ((m *' m') .proj₂) ((m' *' m) .proj₂) (*-comm (m .proj₁) (m' .proj₁)) ⟩
    M (m' *' m) ≈⟨ sym (axiom (M-mul m' m)) ⟩
    M m' • M m ∎
    where
    open SR word-setoid
    
  aux-comm-HHM : ∀ m → HH • M m ≈ M m • HH
  aux-comm-HHM m = begin
    HH • M m ≈⟨ (cleft lemma-HH-M-1) ⟩
    M -'₁ • M m ≈⟨ aux-comm-MM' -'₁ m ⟩
    M m • M -'₁ ≈⟨ (cright sym lemma-HH-M-1) ⟩
    M m • HH ∎
    where
    open SR word-setoid

  lemma-S^kM : ∀ x k → (nz : x ≢ ₀) →
    let
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    x⁻² = x⁻¹ * x⁻¹
    in
    S^ k • M (x , nz) ≈ M (x , nz) • S^ (k * x⁻²)
  lemma-S^kM x k nz = begin
    S^ k • M (x , nz) ≈⟨ sym (trans left-unit (cong refl right-unit)) ⟩
    ε • S^ k • M (x , nz) • ε ≈⟨ cong (sym (aux-M-mul (x , nz))) (cright cright sym (aux-M-mulˡ (x , nz))) ⟩
    (M ((x , nz)) • M ((x , nz) ⁻¹) ) • S^ k • M (x , nz) • (M ((x , nz) ⁻¹) • M ((x , nz)))  ≈⟨ by-passoc (□ ^ 2 • □ • □ • □ ^ 2) (□ • (□ • □ ^ 2 • □) • □) auto ⟩
    M ((x , nz)) • (M ((x , nz) ⁻¹)  • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹)) • M ((x , nz))  ≈⟨ (cright cleft aux) ⟩
    M ((x , nz)) • (M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹)) • M ((x , nz))  ≈⟨ sym (by-passoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • (□ • □ ^ 2 • □) • □) auto) ⟩
    (M ((x , nz)) • M ((x , nz) ⁻¹)) • (M (x , nz) • S^ (k * x⁻²)) • (M ((x , nz) ⁻¹) • M ((x , nz)))  ≈⟨ cong (aux-M-mul (x , nz)) (cright aux-M-mulˡ (x , nz)) ⟩
    ε • (M (x , nz) • S^ (k * x⁻²)) • ε  ≈⟨ trans left-unit right-unit ⟩
    M (x , nz) • S^ (k * x⁻²) ∎
    where
    open SR word-setoid
    x⁻¹ = ((x , nz) ⁻¹) .proj₁
    -x⁻¹ = - x⁻¹
    x⁻² = x⁻¹ * x⁻¹
    aux : M ((x , nz) ⁻¹) • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹) ≈ M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹)
    aux = begin
      M ((x , nz) ⁻¹) • (S^ k • M (x , nz)) • M ((x , nz) ⁻¹) ≈⟨ cong refl assoc ⟩
      M ((x , nz) ⁻¹) • S^ k • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ sym assoc ⟩
      (M ((x , nz) ⁻¹) • S^ k) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ (cleft lemma-MS^k x⁻¹ k (((x , nz) ⁻¹) .proj₂)) ⟩
      (S^ (k * x⁻²) • M ((x , nz) ⁻¹)) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ assoc ⟩
      S^ (k * x⁻²) • M ((x , nz) ⁻¹) • M (x , nz) • M ((x , nz) ⁻¹) ≈⟨ (cright sym assoc) ⟩
      S^ (k * x⁻²) • (M ((x , nz) ⁻¹) • M (x , nz)) • M ((x , nz) ⁻¹) ≈⟨  (cright cleft (aux-M-mulˡ (x , nz))) ⟩
      S^ (k * x⁻²) • ε • M ((x , nz) ⁻¹) ≈⟨ cong refl left-unit ⟩
      S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ sym left-unit ⟩
      ε • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ (cleft sym ((aux-M-mulˡ (x , nz)))) ⟩
      (M ((x , nz) ⁻¹) • M (x , nz)) • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ assoc ⟩
      M ((x , nz) ⁻¹) • M (x , nz) • S^ (k * x⁻²) • M ((x , nz) ⁻¹) ≈⟨ sym (cong refl assoc) ⟩
      M ((x , nz) ⁻¹) • (M (x , nz) • S^ (k * x⁻²)) • M ((x , nz) ⁻¹) ∎


  aux-H³M : ∀ m* → H ^ 3 • M m* ≈ M (m* ⁻¹) • H ^ 3
  aux-H³M m*  = begin
    H ^ 3 • M m* ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2 ) auto ⟩
    H ^ 2 • H • M m* ≈⟨ cright semi-HM m* ⟩
    H ^ 2 • M (m* ⁻¹) • H ≈⟨ sym assoc ⟩
    (H ^ 2 • M (m* ⁻¹)) • H ≈⟨ cleft aux-comm-HHM (m* ⁻¹) ⟩
    (M (m* ⁻¹) • H ^ 2) • H ≈⟨ trans assoc (cong refl assoc) ⟩
    M (m* ⁻¹) • H ^ 3 ∎
    where
    open SR word-setoid

  aux-H³M' : ∀ m'* → H ^ 3 • M (m'* ⁻¹) ≈ M m'* • H ^ 3
  aux-H³M' m'* = begin
    H ^ 3 • M (m'* ⁻¹) ≈⟨ aux-H³M (m'* ⁻¹) ⟩
    M (m'* ⁻¹ ⁻¹) • H ^ 3 ≈⟨ cleft aux-MM ((m'* ⁻¹ ⁻¹).proj₂) (m'* .proj₂) (inv-involutive m'* ) ⟩
    M (m'*) • H ^ 3 ∎
    where
    open SR word-setoid
