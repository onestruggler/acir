------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 8.9 by induction on the width, with Lemma 8.7 proved
--
-- The paper proves Section 8's lemmas on n qubits using completeness on
-- fewer — its Lemma 5.1, "the induction hypothesis" — and so does this
-- development: Lemma 8.7 on 5 + k qubits (GeneralN.Lemma87All) takes
-- completeness at every width up to 4 + k.  Completeness.Theorem-8-9′
-- takes Lemmas 8.7 and 8.8 at every width outright, which cannot be fed
-- such a proof.  Here completeness is built width by width instead
-- (`below`: at every width below n, each from all the smaller ones), so
-- Lemma 8.7 is discharged, and Lemma 8.8 is asked for only in the form
-- the paper proves it: at each width, given completeness below.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.CompletenessInduction where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word)

open import Notations using (₀ ; ₁ ; ₂ ; ₃₊)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)
open import Normalization.StarPresentation using (module MonoidSem)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
open import Examples.Groups.Real-Clifford+CH.Soundness using (axiom-soundᴱ)

import Examples.Groups.Real-Clifford+CH.EncodingSemantics as EncodingSemantics
import Examples.Groups.Real-Clifford+CH.OneQubit as OneQubit
import Examples.Groups.Real-Clifford+CH.Section8 as Section8
import Examples.Groups.Real-Clifford+CH.TwoQubit as TwoQubit
import Examples.Groups.Real-Clifford+CH.TwoQubit.Decoding as Decoding
open TwoQubit.BF using () renaming (⟦_⟧Y to ⟦_⟧Y₂)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410Proof as T410
open import Examples.Groups.Real-Clifford+CH.Completeness using (zero-wires)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Three as L87₃
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All as L87ₙ

------------------------------------------------------------------------
-- Completeness at a width, and below it

Complete : ℕ → Set
Complete n = ∀ {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → n ⊢ w ≈ v

Below : ℕ → Set
Below n = ∀ {j} → j < n → Complete j

------------------------------------------------------------------------
-- Theorem 8.9

module Theorem-8-9″
  -- Two qubits: Theorem 4.4 of the literature; on more, Theorem 4.4 at
  -- the width of P, from which Theorem 4.10 is proved.
  (theorem-4-4  : ∀ {u t : Word (G.Gen 4)} → ⟦ u ⟧Y₂ ~ ⟦ t ⟧Y₂ →
                  PB._≈_ (4 G.G,_===_) u t)
  (theorem-4-4ₙ : ∀ k → T410.Theorem-4-4 k)
  -- Lemma 8.8 on 3 + k qubits, given completeness on fewer.
  (lemma-8-8    : ∀ k → Below (₃₊ k) → Section8.Lemma-8-8 k)
  where

  private
    module L76 = TwoQubit.Lemma-7-6 theorem-4-4 Decoding.lemma-7-4 Decoding.lemma-7-5

    -- Lemma 8.7, from completeness on two and three qubits and, on five
    -- and more, on every width up to the one below.
    lemma-8-7 : ∀ k → Below (₃₊ k) → Section8.Lemma-8-7 k
    lemma-8-7 zero          b = L87₃.lemma-8-7₃ (b {2} (s≤s (s≤s (s≤s z≤n))))
    lemma-8-7 (suc zero)    b = L87ₙ.lemma-8-7₄ (b {2} (s≤s (s≤s (s≤s z≤n))))
                                                (b {3} (s≤s (s≤s (s≤s (s≤s z≤n)))))
    lemma-8-7 (suc (suc k)) b =
      L87ₙ.lemma-8-7ₙ (b {2} (s≤s (s≤s (s≤s z≤n)))) (b {3} (s≤s (s≤s (s≤s (s≤s z≤n))))) k
                      (λ {j} j≤ → b {₃₊ j} (s≤s (s≤s (s≤s (s≤s j≤)))))

    -- One width, from all the smaller ones.
    step : ∀ n → Below n → Complete n
    step ₀      _ {w} {v} _ = PB.trans (zero-wires w) (PB.sym (zero-wires v))
    step ₁      _ = OneQubit.complete
    step ₂      _ = L76.complete
    step (₃₊ k) b = S8.complete
      where
      module S8 = Section8.Complete k (T410.theorem-4-10 k (theorem-4-4ₙ k))
                    (EncodingSemantics.e-sem k) (lemma-8-8 k b) (lemma-8-7 k b)

    -- Every width below n.
    below : ∀ n → Below n
    below zero    ()
    below (suc n) {j} (s≤s j≤n) with m≤n⇒m<n∨m≡n j≤n
    ... | inj₁ j<n     = below n j<n
    ... | inj₂ Eq.refl = step n (below n)

  -- Two circuits with the same matrix over ℤ[1/√2] are equal in QC.
  completeness : ∀ n → Complete n
  completeness n = step n (below n)

  -- With soundness (Proposition 3.1), Figure 4 presents its image at
  -- every width, as in Completeness.
  subpresentation : ∀ n → (n VRel,_===_) IsSubMonoidPresentationOf Scaled-monoid n
  subpresentation n = record
    { ⟦_⟧  = MS.⟦_⟧
    ; mono = record
      { isMonoidHomomorphism = MS.Cong.isMonoidHomomorphism axiom-soundᴱ
      ; injective            = λ {w} {v} e → completeness n {w} {v} (~-⟦⟧ᴱ {w = w} {v} e)
      }
    }
    where
    module MS = MonoidSem (n VRel,_===_) (Monoid.setoid (Scaled-monoid n))
                          (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ)
