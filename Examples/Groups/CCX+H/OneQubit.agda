------------------------------------------------------------------------
-- Presentations of groups
--
-- A complete one-wire theory by Clément's translation method.
-- The four auxiliary generators have direct X/H decodings.  Translate
-- Tables 1 and 2 and add the two generator-recovery equations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.OneQubit where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (s≤s)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong₂)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+H.Syntactics
open import Examples.Groups.CCX+H.Encoding using (e ; encode)
open import Examples.Groups.CCX+H.Semantics using (gate-matrix ; interpret)
import Examples.Groups.CCX+HH.Translation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Sem
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
open R using (RingD)

private
  module M = Sem.Dim 1
  module C = Complete 0

sign : Fin 2 → Circuit 1
sign zero = X • H • X • H • X
sign (suc zero) = H • X • H

d : T.Genᴸ 2 → Circuit 1
d T.IH = H
d T.⌊ U.M-gen a ⌋ = sign a
d T.⌊ U.X-gen a b p ⌋ = X
d T.⌊ U.K-gen a b c d p q r ⌋ = ε

private
  no-chain : ∀ (a b c : Fin 2) → a < b → b < c → ⊥
  no-chain zero zero c () q
  no-chain zero (suc zero) zero p ()
  no-chain zero (suc zero) (suc zero) p (s≤s ())
  no-chain (suc zero) zero c () q
  no-chain (suc zero) (suc zero) c (s≤s ()) q

opaque
  unfolding Sem.actV Sem.set₁ Sem.set₂ R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  sign-correct : ∀ a → M.⟦ encode (sign a) ⟧ᴸ ≡ M.⟦ T.Mᴸ a ⟧ᴸ
  sign-correct zero = refl
  sign-correct (suc zero) = refl

  exchange-correct : ∀ (a b : Fin 2) (p : a < b) →
    M.⟦ encode (X {0}) ⟧ᴸ ≡ M.⟦ T.Xᴸ a b p ⟧ᴸ
  exchange-correct zero zero ()
  exchange-correct zero (suc zero) p = refl
  exchange-correct (suc zero) zero ()
  exchange-correct (suc zero) (suc zero) (s≤s ())

  gate-correct : ∀ (g : Gen 1) →
    M.⟦ encode [ g ]ʷ ⟧ᴸ ≡ gate-matrix g
  gate-correct (gate₀ ())
  gate-correct (gate₁ X-gate) = refl
  gate-correct (gate₁ H-gate) = refl
  gate-correct (gate₀ () ↥)

d-correct : ∀ g → M.⟦ encode (d g) ⟧ᴸ ≡ M.⟦ [ g ]ʷ ⟧ᴸ
d-correct T.IH = refl
d-correct T.⌊ U.M-gen a ⌋ = sign-correct a
d-correct T.⌊ U.X-gen a b p ⌋ =
  exchange-correct a b (recompute (a FP.<? b) p)
d-correct T.⌊ U.K-gen a b c d p q r ⌋ =
  ⊥-elim (no-chain a b c (recompute (a FP.<? b) p)
    (recompute (b FP.<? c) q))

bridge : ∀ (w : Circuit 1) → M.⟦ encode w ⟧ᴸ ≡ interpret w
bridge [ g ]ʷ = gate-correct g
bridge ε = refl
bridge (w • v) = trans (M.⟦•⟧ᴸ (encode w) (encode v))
  (cong₂ _·*·_ (bridge w) (bridge v))

module Rules = Translation (T._===ᴸ_ {2}) e d
open Rules public using (_===_ ; decoded ; recover ; module Circuit)

private
  section : ∀ g → Rules.E (d g) Rules.Auxiliary.≈ [ g ]ʷ
  section g = C.completeness {u = Rules.E (d g)} {v = [ g ]ʷ} (d-correct g)
  module S = Rules.Section section

sound : ∀ {w v} → w Circuit.≈ v → interpret w ≡ interpret v
sound {w} {v} p = trans (sym (bridge w))
  (trans (Sem.soundness 1 (S.encode-cong p)) (bridge v))

complete : ∀ {w v} → interpret w ≡ interpret v → w Circuit.≈ v
complete {w} {v} p = Rules.encode-injective
  (C.completeness {u = encode w} {v = encode v}
    (trans (bridge w) (trans p (sym (bridge v)))))
