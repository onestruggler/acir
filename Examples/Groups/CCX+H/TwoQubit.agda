------------------------------------------------------------------------
-- Presentations of groups
--
-- A complete two-wire circuit presentation by Clément's translation.
-- Decode Tables 1 and 2 on four levels and add five generator-recovery
-- equations.  Soundness uses finite, kernel-checked decoding identities.
-- Semantics here is the explicit encoding's matrix.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.TwoQubit where

import Data.Fin.Properties as FP
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using ([_]ʷ)

open import Examples.Groups.CCX+H.Syntactics using (Circuit)
open import Examples.Groups.CCX+H.Encoding using (e ; encode)
open import Examples.Groups.CCX+H.TwoQubit.Decoding using (d)
open import Examples.Groups.CCX+H.TwoQubit.Checks
open import Examples.Groups.CCX+H.TwoQubit.Semantics using (interpret ; bridge)
import Examples.Groups.CCX+HH.Translation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Sem
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (D)

private
  module M = Sem.Dim 2
  module C = Complete 1

d-correct : ∀ g → M.⟦ encode (d g) ⟧ᴸ ≡ M.⟦ [ g ]ʷ ⟧ᴸ
d-correct T.IH = refl
d-correct T.⌊ U.M-gen a ⌋ = sign-correct a
d-correct T.⌊ U.X-gen a b p ⌋ =
  exchange-correct a b (recompute (a FP.<? b) p)
d-correct T.⌊ U.K-gen a b c d p q r ⌋ =
  k-correct a b c d (recompute (a FP.<? b) p)
    (recompute (b FP.<? c) q) (recompute (c FP.<? d) r)

module Rules = Translation (T._===ᴸ_ {4}) e d
open Rules public using (_===_ ; decoded ; recover ; module Circuit)

⟦_⟧ : Circuit 2 → Matrix 4 4 D
⟦ w ⟧ = M.⟦ encode w ⟧ᴸ

private
  section : ∀ g → Rules.E (d g) Rules.Auxiliary.≈ [ g ]ʷ
  section g = C.completeness {u = Rules.E (d g)} {v = [ g ]ʷ} (d-correct g)
  module S = Rules.Section section

encoded-sound : ∀ {w v} → w Circuit.≈ v → ⟦ w ⟧ ≡ ⟦ v ⟧
encoded-sound p = Sem.soundness 2 (S.encode-cong p)

encoded-complete : ∀ {w v} → ⟦ w ⟧ ≡ ⟦ v ⟧ → w Circuit.≈ v
encoded-complete {w} {v} p = Rules.encode-injective
  (C.completeness {u = encode w} {v = encode v} p)

sound : ∀ {w v} → w Circuit.≈ v → interpret w ≡ interpret v
sound {w} {v} p = trans (sym (bridge w)) (trans (encoded-sound p) (bridge v))

complete : ∀ {w v} → interpret w ≡ interpret v → w Circuit.≈ v
complete {w} {v} p = encoded-complete
  (trans (bridge w) (trans p (sym (bridge v))))
