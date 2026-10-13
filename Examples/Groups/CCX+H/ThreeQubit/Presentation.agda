------------------------------------------------------------------------
-- Presentations of groups
--
-- A three-wire circuit presentation by Clément's translation method.
-- Decode every instance of Tables 1 and 2 on eight levels and add the
-- nine generator-recovery equations.  These are equations between
-- circuits over X, CX, CCX and H only.
--
-- Completeness uses the existing scaled two-level presentation and
-- the back-and-forth lemma.  Soundness uses the verified decoding.
-- The semantics bridge identifies this denotation with the usual
-- gate matrices and their products.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.ThreeQubit.Presentation where

open import Relation.Binary.PropositionalEquality using (_≡_ ; sym ; trans)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Word.Base using ([_]ʷ)

open import Examples.Groups.CCX+H.Syntactics using (Circuit)
open import Examples.Groups.CCX+H.Encoding using (e ; encode)
open import Examples.Groups.CCX+H.ThreeQubit.Decoding using (d)
open import Examples.Groups.CCX+H.ThreeQubit.DecodingSoundness
  using (d-correct)
open import Examples.Groups.CCX+H.ThreeQubit.Semantics
  using (interpret ; bridge)
import Examples.Groups.CCX+HH.Translation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Sem
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (D)

private
  module M = Sem.Dim 4
  module C = Complete 3

module Rules = Translation (T._===ᴸ_ {8}) e d
open Rules public using (_===_ ; decoded ; recover ; module Circuit)

⟦_⟧ : Circuit 3 → Matrix 8 8 D
⟦ w ⟧ = M.⟦ encode w ⟧ᴸ

private
  section : ∀ g → Rules.E (d g) Rules.Auxiliary.≈ [ g ]ʷ
  section g = C.completeness {u = Rules.E (d g)} {v = [ g ]ʷ} (d-correct g)

  module S = Rules.Section section

encoded-sound : ∀ {w v} → w Circuit.≈ v → ⟦ w ⟧ ≡ ⟦ v ⟧
encoded-sound p = Sem.soundness 4 (S.encode-cong p)

encoded-complete : ∀ {w v} → ⟦ w ⟧ ≡ ⟦ v ⟧ → w Circuit.≈ v
encoded-complete {w} {v} p = Rules.encode-injective
  (C.completeness {u = encode w} {v = encode v} p)

sound : ∀ {w v} → w Circuit.≈ v → interpret w ≡ interpret v
sound {w} {v} p = trans (sym (bridge w)) (trans (encoded-sound p) (bridge v))

complete : ∀ {w v} → interpret w ≡ interpret v → w Circuit.≈ v
complete {w} {v} p = encoded-complete
  (trans (bridge w) (trans p (sym (bridge v))))
