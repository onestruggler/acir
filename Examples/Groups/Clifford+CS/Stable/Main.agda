------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford+CS circuits: completeness at every width, with no hypotheses
--
-- Theorem S (Stable.Theorem, Stable.Presentation) with its two
-- hypotheses discharged: completeness on four wires (Four.Complete) and
-- on five (Five.Main, embedded in the theory of Stable.Rules).  That
-- theory — the rules of Syntactics, the five-wire rules AX, λ(lf),
-- λ(hyb-sq), λ(hyb-yb), and the control schema over those four — is
-- sound and complete for the circuits' scaled operators on every number
-- of wires (`sound`, `complete`), and presents the submonoid of
-- U (2ⁿ) the gates generate, which is the subgroup they generate
-- (`grouplikeᵧ`): from four wires on as Stable.Presentation states it
-- (`presentation₄₊`), and on three wires and fewer from Unitary's
-- presentations (`presentation₀` … `presentation₃`), where the theory
-- derives what the old one does, back through soundness and the old
-- completeness (`Low`).
--
-- The presentations are stated with the size of the unitaries spelled
-- as their proofs spell it — 2 ^ ₀ … 2 ^ ₃, and Encoding's N, 2⁴⁺ᵐ as a
-- successor (`N≡`) — rather than as one family over every width: a
-- conversion between U at two spellings of the same size unfolds the
-- two group records (more than fifteen minutes).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Main where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ ; _^_)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄₊)

open import Presentation.Definitions using (_IsSubPresentationOf_ ; _IsSubMonoidPresentationOf_)

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _VRel,_===_ ; _⊢_≈_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Completeness
  using (Complete ; complete₀ ; complete₁ ; complete₂ ; complete₃)
open import Examples.Groups.Clifford+CS.Four.Complete using (complete₄)
open import Examples.Groups.Clifford+CS.Five.Main using (complete₅)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Stable.Rules
  using (_YVRel,_===_ ; _⊢ᵧ_≈_ ; embed ; embed₅)
open import Examples.Groups.Clifford+CS.Stable.Soundness using (soundᵧ)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (U)
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.Unitary as Unitary
import Examples.Groups.Clifford+CS.Stable.Presentation as Presentation

------------------------------------------------------------------------
-- The hypotheses of Theorem S

-- Completeness on five wires, in the theory of Stable.Rules.
complete₅ᵧ : Completeᵧ 5
complete₅ᵧ e = embed₅ (complete₅ e)

open Presentation complete₄ complete₅ᵧ public
  using (grouplikeᵧ ; completeᵧ₄) renaming (presentation to presentation₄₊)

------------------------------------------------------------------------
-- Soundness and completeness on every number of wires

sound : ∀ {n} {w v : Circuit n} → n ⊢ᵧ w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
sound = soundᵧ

complete : ∀ n → Completeᵧ n
complete ₀      e = embed (complete₀ e)
complete ₁      e = embed (complete₁ e)
complete ₂      e = embed (complete₂ e)
complete ₃      e = embed (complete₃ e)
complete (₄₊ m) e = completeᵧ₄ m e

------------------------------------------------------------------------
-- The presentations on three wires and fewer

private
  -- On n wires where the old theory is complete, a group sub-presentation
  -- by the old theory is a monoid sub-presentation by the new one: the
  -- new rules hold there, and the old theory is part of the new.
  module Low {n : ℕ} (c : Complete n) (P : (n VRel,_===_) IsSubPresentationOf U (2 ^ n)) where
    module P  = _IsSubPresentationOf_ P
    module Mo = GroupMorphisms.IsGroupMonomorphism P.mono
    module Ho = GroupMorphisms.IsGroupHomomorphism Mo.isGroupHomomorphism

    back : ∀ {w v : Circuit n} → n ⊢ᵧ w ≈ v → n ⊢ w ≈ v
    back e = c (soundᵧ e)

    presentationᵧ : (n YVRel,_===_) IsSubMonoidPresentationOf (Group.monoid (U (2 ^ n)))
    presentationᵧ = record
      { ⟦_⟧  = P.⟦_⟧
      ; mono = record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = λ e → IsRelHomomorphism.cong Ho.isRelHomomorphism (back e) }
            ; homo = Ho.homo
            }
          ; ε-homo = Ho.ε-homo
          }
        ; injective = λ e → embed (Mo.injective e)
        }
      }

presentation₀ : (₀ YVRel,_===_) IsSubMonoidPresentationOf (Group.monoid (U (2 ^ ₀)))
presentation₀ = Low.presentationᵧ {₀} complete₀ Unitary.presentation₀

presentation₁ : (₁ YVRel,_===_) IsSubMonoidPresentationOf (Group.monoid (U (2 ^ ₁)))
presentation₁ = Low.presentationᵧ {₁} complete₁ Unitary.presentation₁

presentation₂ : (₂ YVRel,_===_) IsSubMonoidPresentationOf (Group.monoid (U (2 ^ ₂)))
presentation₂ = Low.presentationᵧ {₂} complete₂ Unitary.presentation₂

presentation₃ : (₃ YVRel,_===_) IsSubMonoidPresentationOf (Group.monoid (U (2 ^ ₃)))
presentation₃ = Low.presentationᵧ {₃} complete₃ Unitary.presentation₃

------------------------------------------------------------------------
-- From four wires on: presentation₄₊ m, against U (Encoding.N m), and

N≡ : ∀ m → Encoding.N m ≡ 2 ^ (₄₊ m)
N≡ m = Encoding.N≡ m
