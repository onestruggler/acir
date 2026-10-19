------------------------------------------------------------------------
-- Presentations of groups
--
-- Paper-V0's circuits as qutrit matrices, and their Weyl law
--
-- Paper-V0 (Examples.Groups.ProjectiveClifford.Qupit) is Figure 1 of
-- the qupit paper with its scalars erased; it presents the semidirect
-- product Pauli ⋊ Sp(2n, ℤ/3ℤ), and its interpretation ⟦_⟧ᵖ sends a
-- circuit to a pair (P , S).  Here its gates are read as Blake's
-- qutrit matrices — H the Fourier matrix, S = diag(1, 1, ω), CZ =
-- ω^(xy) — in operator order (a word is the product of its letters,
-- the rightmost applied first, as the qupit library reads it), and
-- every circuit's matrix obeys the Weyl law of its interpretation
-- (law): M(u) D(v) = ω^(sform P (S v)) D(S v) M(u).  So the matrix
-- determines (P , S), and with it the circuit modulo Paper-V0's rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.V0Mat where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_) renaming (_ʷ to _ʷ′)
open import Function.Base using (_∋_)

open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Independence.Semantics.Qutrit
open import Examples.Independence.Qutrit-Clifford.Weyl
import Examples.Independence.Qutrit-Clifford.P3 as P3
import ForStdlib.Data.Fin.Mod as F3

import Examples.Groups.ProjectivePauli.Semantics 1 P3.p-prime as PS
open PS using (Pauli ; _+ₚ_ ; pIₙ)
open import Examples.Groups.Symplectic.Semantics 1 P3.p-prime using (Symplectic ; _∘ˢ_ ; εˢ)
open Symplectic using (ap)

import Examples.Groups.Symplectic.Syntactics.Gates 1 P3.p-prime as Gates
module G = Gates.Symplectic
open G using (Gen ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; _↥ ; H-gate ; S-gate ; CZ-gate)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
  P3.p-3 P3.p-prime P3.g* P3.g-gen as PV0
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  P3.p-3 P3.p-prime P3.g* P3.g-gen as SDPres
open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics
  P3.p-3 P3.p-prime P3.g* P3.g-gen using (module SemiDirect)
module SD = SemiDirect
import Examples.Groups.ProjectivePauli.Presentation-Alt 1 P3.p-prime as PZ
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Forward
  P3.p-3 P3.p-prime P3.g* P3.g-gen as Fwd
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  P3.p-3 P3.p-prime P3.g* P3.g-gen as V1S

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The interpretations

-- The semidirect product's, on its own words.
⟦_⟧ˢᵈ : Word (SD.Gen n) → Pauli n × Symplectic n
⟦_⟧ˢᵈ {n} = _IsPresentationOf_.⟦_⟧ (SDPres.presentation {n})

-- Paper-V0's.
⟦_⟧ᵖ : Word (Gen n) → Pauli n × Symplectic n
⟦_⟧ᵖ {n} = _IsPresentationOf_.⟦_⟧ (PV0.presentation n)

------------------------------------------------------------------------
-- The matrices

M₀ : Gen n → Sc n
M₀ (gate₁ H-gate)  = embs Hᵍ
M₀ (gate₁ S-gate)  = embs Sᵍ
M₀ (gate₂ CZ-gate) = embs CZᵍ
M₀ (g ↥)           = ↑s (M₀ g)

-- In operator order.
M : Word (Gen n) → Sc n
M [ g ]ʷ  = M₀ g
M ε       = εs
M (u • v) = M v ∙ M u

------------------------------------------------------------------------
-- Products, through `ap`
--
-- The semidirect product's action is transported through two
-- presentations; SDPres.Semidirect.∙-agrees identifies the product with
-- the one whose action is `ap`, which is all that is used of it.

private
  module SDn (m : ℕ) = SDPres.Semidirect m

  ∙ˢᵈ : (x y : Word (SD.Gen n)) →
        ⟦ x • y ⟧ˢᵈ ≡ (proj₁ ⟦ x ⟧ˢᵈ +ₚ ap (proj₂ ⟦ x ⟧ˢᵈ) (proj₁ ⟦ y ⟧ˢᵈ) ,
                      proj₂ ⟦ x ⟧ˢᵈ ∘ˢ proj₂ ⟦ y ⟧ˢᵈ)
  ∙ˢᵈ {n} x y = SDn.∙-agrees n ⟦ x ⟧ˢᵈ ⟦ y ⟧ˢᵈ

  -- Its Pauli component, over variable words: `Eq.cong proj₁ (∙ˢᵈ x y)`
  -- at particular words has its endpoints matched against the goal at
  -- the pair type, comparing the two readings symplectic part and all.
  ∙ˢᵈ₁ : (x y : Word (SD.Gen n)) →
         proj₁ ⟦ x • y ⟧ˢᵈ ≡ proj₁ ⟦ x ⟧ˢᵈ +ₚ ap (proj₂ ⟦ x ⟧ˢᵈ) (proj₁ ⟦ y ⟧ˢᵈ)
  ∙ˢᵈ₁ x y = Eq.cong proj₁ (∙ˢᵈ x y)

  pI-+ : (v : Pauli n) → pIₙ +ₚ v ≡ v
  pI-+ []            = refl
  pI-+ ((a , b) ∷ v) = Eq.cong₂ _∷_ (Eq.cong₂ _,_ (F3.+-identityˡ a) (F3.+-identityˡ b)) (pI-+ v)

  +-pI : (v : Pauli n) → v +ₚ pIₙ ≡ v
  +-pI []            = refl
  +-pI ((a , b) ∷ v) = Eq.cong₂ _∷_ (Eq.cong₂ _,_ (F3.+-identityʳ a) (F3.+-identityʳ b)) (+-pI v)

------------------------------------------------------------------------
-- A word one wire up: the new wire 0 is idle

shift-P : (w : Word (SD.Gen n)) → proj₁ ⟦ w SD.↑ ⟧ˢᵈ ≡ PS.pI ∷ proj₁ ⟦ w ⟧ˢᵈ
shift-S : (w : Word (SD.Gen n)) → ∀ p v →
          ap (proj₂ ⟦ w SD.↑ ⟧ˢᵈ) (p ∷ v) ≡ p ∷ ap (proj₂ ⟦ w ⟧ˢᵈ) v

shift-P [ inj₁ x ]ʷ = refl
shift-P [ inj₂ y ]ʷ = refl
shift-P ε           = refl
shift-P {n} (w • w') = begin
  proj₁ ⟦ (w • w') SD.↑ ⟧ˢᵈ
    ≡⟨ ∙ˢᵈ₁ (w SD.↑) (w' SD.↑) ⟩
  proj₁ ⟦ w SD.↑ ⟧ˢᵈ +ₚ ap (proj₂ ⟦ w SD.↑ ⟧ˢᵈ) (proj₁ ⟦ w' SD.↑ ⟧ˢᵈ)
    ≡⟨ Eq.cong₂ (λ a b → a +ₚ ap (proj₂ ⟦ w SD.↑ ⟧ˢᵈ) b) (shift-P w) (shift-P w') ⟩
  (PS.pI ∷ proj₁ ⟦ w ⟧ˢᵈ) +ₚ ap (proj₂ ⟦ w SD.↑ ⟧ˢᵈ) (PS.pI ∷ proj₁ ⟦ w' ⟧ˢᵈ)
    ≡⟨ Eq.cong ((PS.pI ∷ proj₁ ⟦ w ⟧ˢᵈ) +ₚ_) (shift-S w PS.pI (proj₁ ⟦ w' ⟧ˢᵈ)) ⟩
  PS.pI ∷ (proj₁ ⟦ w ⟧ˢᵈ +ₚ ap (proj₂ ⟦ w ⟧ˢᵈ) (proj₁ ⟦ w' ⟧ˢᵈ))
    ≡⟨ Eq.cong (PS.pI ∷_) (Eq.sym (∙ˢᵈ₁ w w')) ⟩
  PS.pI ∷ proj₁ ⟦ w • w' ⟧ˢᵈ ∎
  where open Eq.≡-Reasoning

shift-S [ inj₁ x ]ʷ p v = refl
shift-S [ inj₂ y ]ʷ p v = refl
shift-S ε           p v = refl
shift-S (w • w')    p v =
  Eq.trans (Eq.cong (ap (proj₂ ⟦ w SD.↑ ⟧ˢᵈ)) (shift-S w' p v)) (shift-S w p _)

------------------------------------------------------------------------
-- The law, generator by generator

private
  ε-law : Law (ix (idM {n})) εˢ pIₙ
  ε-law = mkLaw λ v → ε-law′ v
    where
    scale-≡′ : {m : ℕ} {a b : Q} (N : Op m) → a ≡ b → scale a N ≐ scale b N
    scale-≡′ N refl = ≐-refl _
    ε-law′ : LawF (ix (idM {n})) εˢ pIₙ
    ε-law′ v = ≐-trans (⊙-cong ix-id (≐-refl (D v)))
              (≐-trans (⊙-identityˡ (D v))
                (≐-trans (≐-sym (⊙-identityʳ (D v)))
                  (≐-trans (≐-sym (scale-1 (D v ⊙ Idₒ)))
                    (≐-trans (scale-≡′ (D v ⊙ Idₒ)
                               (Eq.sym (Eq.cong ω^ (sform-I v))))
                      (scale-cong {c = ω^ (PS.sform pIₙ v)} (⊙-cong (≐-refl (D v)) (≐-sym ix-id)))))))

-- Stated for Forward's translation at any of its module arguments m,
-- which it ignores: at a variable letter the copies at different m
-- are different neutral terms.
lawᵐ : (m : ℕ) (g : Gen n) →
       Law (ix (proj₂ (M₀ g))) (proj₂ ⟦ Fwd.Iso.h m g ⟧ˢᵈ) (proj₁ ⟦ Fwd.Iso.h m g ⟧ˢᵈ)
lawᵐ m (gate₁ H-gate)  =
  law-cong (≐-sym (ix-emb (proj₂ Hᵍ))) (law-emb₁ local-H _ (λ p v → refl))
lawᵐ {ℕ.suc n} m (gate₁ S-gate)  =
  law-cong (≐-sym (ix-emb (proj₂ Sᵍ)))
    (law-P (Eq.sym P-S) (law-emb₁ local-S _ (λ p v → refl)))
  where
  P-S : proj₁ ⟦ Fwd.Iso.h m (gate₁ {n} S-gate) ⟧ˢᵈ ≡ (zero , suc zero) ∷ pIₙ
  P-S = Eq.trans (∙ˢᵈ₁ (SD.Z^ V1S.-1/2) SD.S) (+-pI _)
lawᵐ m (gate₂ CZ-gate) =
  law-cong (≐-sym (ix-emb (proj₂ CZᵍ))) (law-emb₂ local-CZ _ (λ p q v → refl))
lawᵐ m (g ↥) =
  law-cong (≐-sym (ix-up (proj₂ (M₀ g))))
    (law-P (Eq.sym (shift-P (Fwd.Iso.h m g)))
      (law-up (lawᵐ m g) (proj₂ ⟦ Fwd.Iso.h m g SD.↑ ⟧ˢᵈ) (shift-S (Fwd.Iso.h m g))))

law₀ : (g : Gen n) → Law (ix (proj₂ (M₀ g))) (proj₂ ⟦ [ g ]ʷ ⟧ᵖ) (proj₁ ⟦ [ g ]ʷ ⟧ᵖ)
law₀ {n} g = lawᵐ n g

------------------------------------------------------------------------
-- The law, for every word

law : (u : Word (Gen n)) → Law (ix (proj₂ (M u))) (proj₂ ⟦ u ⟧ᵖ) (proj₁ ⟦ u ⟧ᵖ)
law [ g ]ʷ  = law₀ g
law ε       = ε-law
law (u • v) =
  law-cong (≐-sym (ix-mul (proj₂ (M u)) (proj₂ (M v))))
    (law-P (Eq.sym (∙ˢᵈ₁ ((Fwd.Iso.h _ ʷ′) u) ((Fwd.Iso.h _ ʷ′) v)))
      (law-⊙ (law u) (law v)))
