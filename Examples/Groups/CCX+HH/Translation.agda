------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's back-and-forth translation, with the transported relations
-- made explicit.  Decode each auxiliary axiom and add one equation
-- recovering each circuit generator.  The resulting relation reflects
-- auxiliary derivations unconditionally.  Soundness additionally needs
-- the decoding to have the right auxiliary interpretation.
--
-- An encoding alone does not establish soundness of these equations:
-- the semantic section below is a separate, necessary obligation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)

module Examples.Groups.CCX+HH.Translation
  {X Y : Set} (Δ : WRel Y)
  (e : X → Word Y) (d : Y → Word X)
  where

open import Algebra.Bundles using (Monoid)
open import Level using (0ℓ)

import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.StarInterp as SI
open import Normalization.Reidemeister-Schreier
  using (module Star-Injective-Simplified)

E : Word X → Word Y
E = e ʷ

D : Word Y → Word X
D = d ʷ

infix 4 _===_

data _===_ : WRel X where
  decoded : ∀ {u v} → Δ u v → D u === D v
  recover : (x : X) → [ x ]ʷ === D (e x)

module Circuit = PB _===_
module Auxiliary = PB Δ

decode-cong : ∀ {u v} → u Auxiliary.≈ v → D u Circuit.≈ D v
decode-cong = PP.StarCongruence.fʷ-cong Δ _===_ d
  (λ h → Circuit.axiom (decoded h))

private
  module RS = Star-Injective-Simplified _===_ Δ
  module R = RS.Reidemeister-Schreier-Simplified e d
    (λ h → Circuit.axiom (decoded h))
    (λ x → Circuit.axiom (recover x))

encode-injective : ∀ {w v} → E w Auxiliary.≈ E v → w Circuit.≈ v
encode-injective = R.fʷ-inj

recover-word : (w : Word X) → w Circuit.≈ D (E w)
recover-word = R.left-inv

module Section
  (section : ∀ y → E (d y) Auxiliary.≈ [ y ]ʷ)
  where

  section-word : (u : Word Y) → E (D u) Auxiliary.≈ u
  section-word [ y ]ʷ = section y
  section-word ε = Auxiliary.refl
  section-word (u • v) = Auxiliary.cong (section-word u) (section-word v)

  encode-axiom : ∀ {w v} → w === v → E w Auxiliary.≈ E v
  encode-axiom (decoded {u} {v} h) =
    Auxiliary.trans (section-word u)
      (Auxiliary.trans (Auxiliary.axiom h) (Auxiliary.sym (section-word v)))
  encode-axiom (recover x) = Auxiliary.sym (section-word (e x))

  encode-cong : ∀ {w v} → w Circuit.≈ v → E w Auxiliary.≈ E v
  encode-cong = PP.StarCongruence.fʷ-cong _===_ Δ e encode-axiom

------------------------------------------------------------------------
-- The exact semantic obligations; no semantic equality is an axiom

module Semantics (M : Monoid 0ℓ 0ℓ)
  (interpret : Y → Monoid.Carrier M)
  where

  private
    module S = SI.Extend Δ M interpret
    open Monoid M using (_≈_ ; refl ; sym ; trans ; ∙-cong)

  ⟦_⟧ : Word X → Monoid.Carrier M
  ⟦ w ⟧ = S.⟦ E w ⟧

  -- Source completeness is supplied by the existing two-level theorem.
  module Complete
    (complete-Δ : ∀ {u v} → S.⟦ u ⟧ ≈ S.⟦ v ⟧ → u Auxiliary.≈ v)
    where

    complete : ∀ {w v} → ⟦ w ⟧ ≈ ⟦ v ⟧ → w Circuit.≈ v
    complete {w} {v} h = encode-injective
      (complete-Δ {u = E w} {v = E v} h)

  module Sound
    (sound-Δ : ∀ {u v} → u Auxiliary.≈ v → S.⟦ u ⟧ ≈ S.⟦ v ⟧)
    (section : ∀ y → S.⟦ E (d y) ⟧ ≈ S.⟦ [ y ]ʷ ⟧)
    where

    section-word : ∀ u → S.⟦ E (D u) ⟧ ≈ S.⟦ u ⟧
    section-word [ y ]ʷ = section y
    section-word ε = refl
    section-word (u • v) = ∙-cong (section-word u) (section-word v)

    sound-axiom : ∀ {w v} → w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
    sound-axiom (decoded {u} {v} h) =
      trans (section-word u)
        (trans (sound-Δ (Auxiliary.axiom h)) (sym (section-word v)))
    sound-axiom (recover x) = sym (section-word (e x))

    sound : ∀ {w v} → w Circuit.≈ v → ⟦ w ⟧ ≈ ⟦ v ⟧
    sound Circuit.refl = refl
    sound (Circuit.sym h) = sym (sound h)
    sound (Circuit.trans h j) = trans (sound h) (sound j)
    sound (Circuit.cong h j) = ∙-cong (sound h) (sound j)
    sound (Circuit.assoc {w} {v} {u}) = Monoid.assoc M _ _ _
    sound (Circuit.left-unit {w}) = Monoid.identityˡ M _
    sound (Circuit.right-unit {w}) = Monoid.identityʳ M _
    sound (Circuit.axiom h) = sound-axiom h
