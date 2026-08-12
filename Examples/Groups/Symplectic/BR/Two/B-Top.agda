{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Pushing a top gate (H-gen ↥ or S-gen ↥) through a B box.
--
-- This is the top-wire fragment of BR.Two.B: b'-of, dir-of and
-- lemma-B-br restricted to g ∈ { H-gen ↥ , S-gen ↥ }.  The direction is
-- the dual of the corresponding bottom D-box push (dir-of-d), inlined
-- into dir-of.
--
-- The proof reuses BR.Two.B.lemma-B-br (which already covers the
-- top-gate cases via lemma-B~dualD and lemma-D-br).  There the residual
-- is a Gen-2 word `dual dir`; here it is a Gen-1 word placed on the
-- bottom wire with `_↓ᵏ 1`.  The bridge is lemma-dual↑: for a Gen-1 word
-- w, dual (w ↑) is definitionally w ↓ᵏ 1 (swapping the two wires just
-- sends the top copy back down), and the leading bottom phase is S^ ₀ = ε.
------------------------------------------------------------------------

open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.BR.Two.B-Top (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open Duality
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
import Examples.Groups.Symplectic.BR.Two.B p-2 p-prime as BB

open PB (₂ QRel,_===_)
open PP (₂ QRel,_===_)
open SR word-setoid

b'-of : ∀ (d : B) (x₁ : SympGate 1) -> B
b'-of (a , b) H-gate = b , - a
b'-of (a , b) S-gate = a , b + - a

dir-of : ∀ (d : B) (x₁ : SympGate 1) -> Word (Gen 1)
dir-of (₀ , ₀)    H-gate = H
dir-of (₀ , ₁₊ b) H-gate = ε
dir-of (₁₊ a , ₀) H-gate = H ^ 2
dir-of (a@(₁₊ a') , b@(₁₊ b')) H-gate = ZM a/b • S^ b/a
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  b/a = b * a⁻¹
  a/b = (a , λ ()) *' (b , λ ()) ⁻¹
dir-of (₀ , b)    S-gate = S
dir-of (₁₊ a , b) S-gate = ε

------------------------------------------------------------------------
-- Bridge: dual of a top-wire Gen-1 word is that word on the bottom.

-- A Gen-1 word has only gate₁ letters (Gen 0 is empty), so on each
-- letter dual (gate₁ h ↥) = gate₁ h = gate₁ h ↧ᵏ 1.
lemma-dual↑ : ∀ (w : Word (Gen 1)) -> dual (w ↑) ≡ w ↓ᵏ 1
lemma-dual↑ [ gate₁ H-gate ]ʷ = Eq.refl
lemma-dual↑ [ gate₁ S-gate ]ʷ = Eq.refl
lemma-dual↑ [ gate₀ () ↥ ]ʷ
lemma-dual↑ ε                 = Eq.refl
lemma-dual↑ (w • v)           = Eq.cong₂ _•_ (lemma-dual↑ w) (lemma-dual↑ v)

-- BR.Two.B's direction for a top gate is dual (S^ ₀ • w ↑); since
-- dual (S^ ₀) = dual ε = ε this reduces to ε • dual (w ↑), and
-- lemma-dual↑ turns dual (w ↑) into w ↓ᵏ 1.
bridge : ∀ (w : Word (Gen 1)) -> ε • dual (w ↑) ≈ w ↓ᵏ 1
bridge w = trans (refl' (Eq.cong (ε •_) (lemma-dual↑ w))) left-unit

------------------------------------------------------------------------
-- The push lemma.

lemma-B-br : ∀ (b : B) (x₁ : SympGate 1) ->
  let
  dir = dir-of b x₁
  b' = b'-of b x₁
  in

  [ b ]ᵇ • [ gate₁ x₁ ↥ ]ʷ ≈ (dir ↓ᵏ 1) • [ b' ]ᵇ

lemma-B-br d@(₀ , ₀) H-gate = begin
  [ d ]ᵇ • [ H-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (H-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (H-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (H-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d H-gate)) ⟩
  (dir-of d H-gate ↓ᵏ 1) • [ b'-of d H-gate ]ᵇ                     ∎
lemma-B-br d@(₀ , ₁₊ _) H-gate = begin
  [ d ]ᵇ • [ H-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (H-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (H-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (H-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d H-gate)) ⟩
  (dir-of d H-gate ↓ᵏ 1) • [ b'-of d H-gate ]ᵇ                     ∎
lemma-B-br d@(₁₊ _ , ₀) H-gate = begin
  [ d ]ᵇ • [ H-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (H-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (H-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (H-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d H-gate)) ⟩
  (dir-of d H-gate ↓ᵏ 1) • [ b'-of d H-gate ]ᵇ                     ∎
lemma-B-br d@(₁₊ _ , ₁₊ _) H-gate = begin
  [ d ]ᵇ • [ H-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (H-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (H-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (H-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d H-gate)) ⟩
  (dir-of d H-gate ↓ᵏ 1) • [ b'-of d H-gate ]ᵇ                     ∎

lemma-B-br d@(₀ , ₀) S-gate = begin
  [ d ]ᵇ • [ S-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (S-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (S-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (S-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d S-gate)) ⟩
  (dir-of d S-gate ↓ᵏ 1) • [ b'-of d S-gate ]ᵇ                     ∎
lemma-B-br d@(₀ , ₁₊ _) S-gate = begin
  [ d ]ᵇ • [ S-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (S-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (S-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (S-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d S-gate)) ⟩
  (dir-of d S-gate ↓ᵏ 1) • [ b'-of d S-gate ]ᵇ                     ∎
lemma-B-br d@(₁₊ _ , ₀) S-gate = begin
  [ d ]ᵇ • [ S-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (S-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (S-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (S-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d S-gate)) ⟩
  (dir-of d S-gate ↓ᵏ 1) • [ b'-of d S-gate ]ᵇ                     ∎
lemma-B-br d@(₁₊ _ , ₁₊ _) S-gate = begin
  [ d ]ᵇ • [ S-gen ↥ ]ʷ                                            ≈⟨ BB.lemma-B-br d (S-gen ↥) (λ ()) (λ ()) ⟩
  BB.dir-of d (S-gen ↥) (λ ()) (λ ()) • [ BB.b'-of d (S-gen ↥) (λ ()) (λ ()) ]ᵇ ≈⟨ cleft (bridge (dir-of d S-gate)) ⟩
  (dir-of d S-gate ↓ᵏ 1) • [ b'-of d S-gate ]ᵇ                     ∎
