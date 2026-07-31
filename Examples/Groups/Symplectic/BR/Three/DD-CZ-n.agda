{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- General-width bottom-CZ push through a D-vector.
--
-- Generalises BR.Three.DD-CZ.lemma-dir-and-vd' from `Vec D 2` to
-- `Vec D (₂₊ n)`: bottom CZ (wires 0,1) interacts only with the bottom
-- two D boxes and commutes past the wire-≥2 tail.  The bottom-two
-- interaction is DD-CZ (width 3) widened by CongDownK.cong↓ᵏ; the tail
-- commute is lemma-comm-CZ-w↑↑.
------------------------------------------------------------------------

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as ℕ
open import Data.Vec using (Vec ; [] ; _∷_)

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.BR.Three.DD-CZ-n (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime using (lemma-comm-CZ-w↑↑)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ

------------------------------------------------------------------------
-- Box widening at an arbitrary base width.

d-↓ᵏ : ∀ {m} (d : D) (k : ℕ) → [_]ᵈ {m} d ↓ᵏ k ≡ [_]ᵈ {m ℕ.+ k} d
d-↓ᵏ (₀ , b) k = Eq.cong₂ _•_ Eq.refl (CZ^-↓ᵏ (- b) k)
d-↓ᵏ (a@(₁₊ _) , b) k =
  Eq.cong₂ _•_ Eq.refl
    (Eq.cong₂ _•_ (CZ^-↓ᵏ (- a) k)
      (Eq.cong₂ _•_ Eq.refl (S^-↓ᵏ -b/a k)))
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

d↑-↓ᵏ : ∀ (d : D) (k : ℕ) → ([_]ᵈ {0} d ↑) ↓ᵏ k ≡ [_]ᵈ {k} d ↑
d↑-↓ᵏ d k = Eq.trans (↑↓ᵏ-comm ([_]ᵈ {0} d) k) (Eq.cong _↑ (d-↓ᵏ {0} d k))

------------------------------------------------------------------------
-- vd'-of / dir-of at general width: only the bottom two entries change.

gen-vd'-of : ∀ {n} → Vec D (₂₊ n) → Vec D (₂₊ n)
gen-vd'-of ((a , b) ∷ (c , d) ∷ dr) = (a , b + - c) ∷ (c , d + - a) ∷ dr

gen-dir-of : ∀ {n} → Vec D (₂₊ n) → Word (Gen (₂₊ n))
gen-dir-of {n} (d1 ∷ d2 ∷ dr) = DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ n

------------------------------------------------------------------------
-- The general lemma.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  -- The bottom CZ interacts with only the bottom two D boxes; the tail
  -- above them (wires ≥ 2) is an ARBITRARY word w, commuted past CZ by
  -- lemma-comm-CZ-w↑↑.  gen-dd-cz below is the D-vector-tail instance.
  gen-dd-cz-tail : ∀ (d1 d2 : D) (w : Word (Gen (₁₊ n))) →
    ([ d1 ]ᵈ • ([ d2 ]ᵈ • w ↑) ↑) • CZ ≈
      ((DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ n) ↑) •
        ([ (proj₁ d1 , proj₂ d1 + - proj₁ d2) ]ᵈ •
          ([ (proj₁ d2 , proj₂ d2 + - proj₁ d1) ]ᵈ • w ↑) ↑)
  gen-dd-cz-tail d1 d2 w = begin
    (A1 • (A2 • T)) • CZ                     ≈⟨ assoc ⟩
    A1 • ((A2 • T) • CZ)                     ≈⟨ cright assoc ⟩
    A1 • (A2 • (T • CZ))                     ≈⟨ cright (cright (sym (lemma-comm-CZ-w↑↑ w))) ⟩
    A1 • (A2 • (CZ • T))                     ≈⟨ cright (sym assoc) ⟩
    A1 • ((A2 • CZ) • T)                     ≈⟨ sym assoc ⟩
    (A1 • (A2 • CZ)) • T                     ≈⟨ cleft widened-DDCZ ⟩
    (dir ↑ • (A1' • A2')) • T                ≈⟨ assoc ⟩
    dir ↑ • ((A1' • A2') • T)                ≈⟨ cright assoc ⟩
    dir ↑ • (A1' • (A2' • T))                ∎
    where
    A1  = [ d1 ]ᵈ
    A2  = [ d2 ]ᵈ ↑
    T   = w ↑ ↑
    dir = DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ n
    -- bottom-two update, spelled out to match gen-vd'-of / DDCZ.vd'-of:
    head-vd' = (proj₁ d1 , proj₂ d1 + - proj₁ d2)
    head-tl-vd' = (proj₁ d2 , proj₂ d2 + - proj₁ d1)
    A1' = [ head-vd' ]ᵈ
    A2' = [ head-tl-vd' ]ᵈ ↑

    eqL : ([ d1 ∷ d2 ∷ [] ]ᵛᵈ • CZ) ↓ᵏ n ≡ (A1 • (A2 • ε)) • CZ
    eqL = Eq.cong₂ _•_
            (Eq.cong₂ _•_ (d-↓ᵏ {1} d1 n) (Eq.cong₂ _•_ (d↑-↓ᵏ d2 n) Eq.refl))
            Eq.refl

    eqR : (DDCZ.dir-of (d1 ∷ d2 ∷ []) ↑ • [ DDCZ.vd'-of (d1 ∷ d2 ∷ []) ]ᵛᵈ) ↓ᵏ n
          ≡ dir ↑ • (A1' • (A2' • ε))
    eqR = Eq.cong₂ _•_ (↑↓ᵏ-comm (DDCZ.dir-of (d1 ∷ d2 ∷ [])) n)
            (Eq.cong₂ _•_ (d-↓ᵏ {1} head-vd' n) (Eq.cong₂ _•_ (d↑-↓ᵏ head-tl-vd' n) Eq.refl))

    widened-DDCZ : A1 • (A2 • CZ) ≈ dir ↑ • (A1' • A2')
    widened-DDCZ = begin
      A1 • (A2 • CZ)                                     ≈⟨ sym (trans (refl' eqL) (trans (cleft (cright right-unit)) assoc)) ⟩
      ([ d1 ∷ d2 ∷ [] ]ᵛᵈ • CZ) ↓ᵏ n                    ≈⟨ cong↓ᵏ n _ _ (DDCZ.lemma-dir-and-vd' (d1 ∷ d2 ∷ [])) ⟩
      (DDCZ.dir-of (d1 ∷ d2 ∷ []) ↑ • [ DDCZ.vd'-of (d1 ∷ d2 ∷ []) ]ᵛᵈ) ↓ᵏ n ≈⟨ trans (refl' eqR) (cright (cright right-unit)) ⟩
      dir ↑ • (A1' • A2')                               ∎

  gen-dd-cz : ∀ (vd : Vec D (₂₊ n)) →
    [ vd ]ᵛᵈ • CZ ≈ (gen-dir-of vd ↑) • [ gen-vd'-of vd ]ᵛᵈ
  gen-dd-cz (d1 ∷ d2 ∷ dr) = gen-dd-cz-tail d1 d2 [ dr ]ᵛᵈ
