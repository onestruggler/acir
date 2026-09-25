------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7: decoding the encoding of a generator gives it back
-- (Clément, Appendix E.4), on n = m + 3 qubits
--
-- A generator is a gate on a wire, or on two neighbouring wires, as
-- Encoding's `view` reads it (`view-one`, `view-two`); the four gates
-- are Lemma87Z, Lemma87CZ and Lemma87H.  Their parameters: the
-- canonical box facts at the full width (Lemma 8.4), the merge (309) at
-- every width up to it, and completeness on two qubits (for the rule
-- (18) and (113), through ThreeQubit).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _≤_ ; suc)
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Word.Base using (_•_)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87
  {m : ℕ} (C : Canon m)
  (mergeAt′ : ∀ K → 1 ≤ K → K ≤ ₁₊ m → ∀ c → 1 ≤ c → c ≤ suc K →
              (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K))
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Nat using (zero ; _<_ ; s≤s ; z≤n)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Encoding using (View ; one ; two ; view)
open import Examples.Groups.Real-Clifford+CH.Section8 using (Lemma-8-7)
open import Examples.Groups.Real-Clifford+CH.GeneralN.OneWire using (on1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (on2)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z C mergeAt′ using (lemmaZ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87CZ C mergeAt′ using (lemmaCZ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87H C mergeAt′ complete₂ using (lemmaH ; lemmaCH)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- The position of a generator

view-one : ∀ (g : Gen k) {p h} → view g ≡ one p h → ([ g ]ʷ ≡ on1 [ gate₁ h ]ʷ p) × (p < k)
view-one (gate₀ ())
view-one (gate₁ h) Eq.refl = Eq.refl , s≤s z≤n
view-one (gate₂ h) ()
view-one (g ↥) e with view g in e′
view-one (g ↥) Eq.refl | one p h = Eq.cong _↑ (proj₁ (view-one g e′)) , s≤s (proj₂ (view-one g e′))
view-one (g ↥) ()      | two p h

view-two : ∀ (g : Gen k) {p h} → view g ≡ two p h → ([ g ]ʷ ≡ on2 [ gate₂ h ]ʷ p) × (₂₊ p ≤ k)
view-two (gate₀ ())
view-two (gate₁ h) ()
view-two (gate₂ h) Eq.refl = Eq.refl , s≤s (s≤s z≤n)
view-two (g ↥) e with view g in e′
view-two (g ↥) ()      | one p h
view-two (g ↥) Eq.refl | two p h = Eq.cong _↑ (proj₁ (view-two g e′)) , s≤s (proj₂ (view-two g e′))

------------------------------------------------------------------------
-- Lemma 8.7

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

lemma-8-7 : Lemma-8-7 m
lemma-8-7 g with view g in eq
... | one p H-gate  = trans (≡→≈ (proj₁ (view-one g eq))) (lemmaH p (proj₂ (view-one g eq)))
... | one p Z-gate  = trans (≡→≈ (proj₁ (view-one g eq))) (lemmaZ p (proj₂ (view-one g eq)))
... | two p CZ-gate = trans (≡→≈ (proj₁ (view-two g eq))) (lemmaCZ p (proj₂ (view-two g eq)))
... | two p CH-gate = trans (≡→≈ (proj₁ (view-two g eq))) (lemmaCH p (proj₂ (view-two g eq)))
