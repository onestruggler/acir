------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing single dirty gates (S, H, S↑, H↑) through a D-vector, with the
-- residual exposed as a `dir ↑` (one wire up).  S/H (wire 0) interact
-- only with the bottom D-box (aux-DS / aux-DH) and commute past the
-- lifted tail; S↑/H↑ (wire 1) descend one box and recurse.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.DVecPush (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_)
open import Data.Vec using (Vec ; _∷_ ; [])

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-S-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime using (comm-dbox-w↑↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime using (aux-DS ; dir-of-DS ; d-of-DS)

open import Notations
open import Word.Base using (Word ; _•_ ; ε)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Wire-0 gates: interact with the bottom box, commute past the tail.

module _ {n : ℕ} where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  dvec-S : ∀ (d₁ : D) (tl : Vec D n) →
    [ (d₁ ∷ tl) ]ᵛᵈ • S ≈ (dir-of-DS d₁ ↑) • [ (d-of-DS d₁ ∷ tl) ]ᵛᵈ
  dvec-S d₁ tl = begin
    ([ d₁ ]ᵈ • [ tl ]ᵛᵈ ↑) • S                              ≈⟨ assoc ⟩
    [ d₁ ]ᵈ • ([ tl ]ᵛᵈ ↑ • S)                              ≈⟨ cright (sym (lemma-comm-S-w↑ [ tl ]ᵛᵈ)) ⟩
    [ d₁ ]ᵈ • (S • [ tl ]ᵛᵈ ↑)                              ≈⟨ sym assoc ⟩
    ([ d₁ ]ᵈ • S) • [ tl ]ᵛᵈ ↑                              ≈⟨ cleft (aux-DS d₁) ⟩
    ((dir-of-DS d₁ ↑) • [ d-of-DS d₁ ]ᵈ) • [ tl ]ᵛᵈ ↑       ≈⟨ assoc ⟩
    (dir-of-DS d₁ ↑) • ([ d-of-DS d₁ ]ᵈ • [ tl ]ᵛᵈ ↑)       ∎

------------------------------------------------------------------------
-- Wire-1 gates: g↑ combines with the lifted tail, recurse via dvec, and
-- the residual (now two wires up) commutes past the bottom box.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  dvec-S↑ : ∀ (d₁ h : D) (t : Vec D n) →
    [ (d₁ ∷ h ∷ t) ]ᵛᵈ • S ↑ ≈ (dir-of-DS h ↑ ↑) • [ (d₁ ∷ d-of-DS h ∷ t) ]ᵛᵈ
  dvec-S↑ d₁ h t = begin
    ([ d₁ ]ᵈ • [ h ∷ t ]ᵛᵈ ↑) • S ↑                                        ≈⟨ assoc ⟩
    [ d₁ ]ᵈ • (([ h ∷ t ]ᵛᵈ • S) ↑)                                        ≈⟨ cright (lemma-cong↑ _ _ (dvec-S h t)) ⟩
    [ d₁ ]ᵈ • ((dir-of-DS h ↑ ↑) • [ d-of-DS h ∷ t ]ᵛᵈ ↑)                  ≈⟨ sym assoc ⟩
    ([ d₁ ]ᵈ • (dir-of-DS h ↑ ↑)) • [ d-of-DS h ∷ t ]ᵛᵈ ↑                  ≈⟨ cleft (comm-dbox-w↑↑ d₁ (dir-of-DS h)) ⟩
    ((dir-of-DS h ↑ ↑) • [ d₁ ]ᵈ) • [ d-of-DS h ∷ t ]ᵛᵈ ↑                  ≈⟨ assoc ⟩
    (dir-of-DS h ↑ ↑) • ([ d₁ ]ᵈ • [ d-of-DS h ∷ t ]ᵛᵈ ↑)                  ∎
