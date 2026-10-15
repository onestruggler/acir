------------------------------------------------------------------------
-- Presentations of groups
--
-- The corrected three-qubit rules, retaining the controlled-K
-- definition, present L₈, the exact orthogonal scaled dyadic matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.Presentation where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Repaired.GroupLike using (grouplike)
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ ; module BM)
import Examples.Groups.CCX+HH-3qubit.Interpretation as I
import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding as E
import Examples.Groups.CCX+HH-3qubit.Repaired.EncodingMatrices as EM
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingMatrices as DM
import Examples.Groups.CCX+HH-3qubit.Repaired.DyadicCompleteness as DC
import Examples.Groups.CCX+HH-3qubit.Repaired.TwoLevelScaled as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation as P₀
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as C₀
open import Presentation.Base _===_ hiding (_===_ ; _≈_)

module P = P₀ 3
module C = C₀ 3
module Dim = SS.Dim 4

ToffoliHadamard : Group _ _
ToffoliHadamard = P.L

⟦_⟧ᴳ : Word Gen → P.LMat
⟦ w ⟧ᴳ = P.⟦ (E.e ʷ) w ⟧ˡ

target-sound : ∀ {w v} → w ≈ v → proj₁ ⟦ w ⟧ᴳ ≡ proj₁ ⟦ v ⟧ᴳ
target-sound {w} {v} proof = Eq.trans (EM.encode-matrix w)
  (Eq.trans (DC.matrix-sound {w} {v} proof) (Eq.sym (EM.encode-matrix v)))

target-complete : ∀ {w v} → proj₁ ⟦ w ⟧ᴳ ≡ proj₁ ⟦ v ⟧ᴳ → w ≈ v
target-complete {w} {v} eq = trans (sym (E.word-back w))
  (trans (T.decode-cong {w = (E.e ʷ) w} {v = (E.e ʷ) v}
    (C.completeness {u = (E.e ʷ) w} {v = (E.e ʷ) v} eq)) (E.word-back v))

-- Completeness is stated for the circuit's matrix interpretation,
-- independently of the encoding used to construct the group element.
matrix-complete : ∀ {w v} → ⟦ w ⟧ᴹ ≡ ⟦ v ⟧ᴹ → w ≈ v
matrix-complete {w} {v} eq = target-complete {w} {v}
  (Eq.trans (EM.encode-matrix w)
    (Eq.trans eq (Eq.sym (EM.encode-matrix v))))

completeness : ∀ {w v} → I.⟦ w ⟧ I.~ I.⟦ v ⟧ → w ≈ v
completeness {w} {v} eq = matrix-complete {w} {v}
  (BM.Φ-~ {I.⟦ w ⟧} {I.⟦ v ⟧} eq)

private
  module Base = _IsMonoidPresentationOf_ P.monoidPresentation
  module Morph = MonoidMorphisms
    (Monoid.rawMonoid (PP.•-ε-monoid (L._===ᴸ_ {8})))
    (Monoid.rawMonoid (Group.monoid P.L))

  semantic-back : ∀ w → proj₁ ⟦ (E.decode ʷ) w ⟧ᴳ ≡ Dim.⟦ w ⟧ᴸ
  semantic-back w = Eq.trans (EM.encode-matrix ((E.decode ʷ) w))
    (Eq.sym (DM.decode-matrix w))

monoidPresentation : _===_ IsMonoidPresentationOf (Group.monoid ToffoliHadamard)
monoidPresentation = record
  { ⟦_⟧ = ⟦_⟧ᴳ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = target-sound }
          ; homo = λ w v → Dim.⟦•⟧ᴸ ((E.e ʷ) w) ((E.e ʷ) v) }
        ; ε-homo = Eq.refl }
      ; injective = target-complete }
    ; surjective = λ A →
        let witness = Morph.IsMonoidIsomorphism.surjective Base.iso A
            w = proj₁ witness
        in (E.decode ʷ) w , λ proof → Eq.trans (target-sound proof)
          (Eq.trans (semantic-back w) (proj₂ witness Presentation.Base.refl)) }
  }

presentation : _===_ IsPresentationOf ToffoliHadamard
presentation = monoidPresentation⇒presentation monoidPresentation grouplike
