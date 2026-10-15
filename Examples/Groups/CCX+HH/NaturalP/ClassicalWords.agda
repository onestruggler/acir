------------------------------------------------------------------------
-- Presentations of groups
--
-- Classical circuits encoded by transpositions alone.
--
-- StructuralEncoding writes the swap as CX HH CX HH CX, so its encoding
-- of a classical circuit has K letters.  Here the swap is encoded
-- directly, as the transposition of the coordinates 1 and 2 on two
-- wires, copied to every block of the wires above (`S-block`), so that
-- a classical circuit becomes a word of X letters (`encodeᶜ`) acting as
-- its classical semantics (`encodeᶜ-action`).  NaturalP.PermCheck
-- compares such words by their permutations of the indices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.ClassicalWords where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_ ; s≤s ; z≤n)
open import Data.Vec.Base using (_∷_ ; [])
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)
open import Notations using (₂₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (isCommutativeRing-D ; adj-D ; ½ᴰ)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.Clifford+CS-TwoLevel.Vector as V
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel-cong ; encode-parallel-correct)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (encoding-action ; swap ; swap₀ ; classical ; classical₀)

private
  variable
    n : ℕ

  x12 : TL.Gen 4
  x12 = TL.X-gen (suc zero) (suc (suc zero)) (s≤s (s≤s z≤n))

  opaque
    unfolding A.actV V.set₁ V.set₂

    x12-action : ∀ v → A.actV x12 v ≡ swap₀ v
    x12-action (a ∷ b ∷ c ∷ d ∷ []) = refl

-- The swap of wires 0 and 1.
S-block : (n : ℕ) → E.Levels (₂₊ n)
S-block zero    = [ x12 ]ʷ
S-block (suc n) = E.copy (contiguous (2 ^ ₂₊ n)) (S-block n)

S-block-action : ∀ n v → A.actVʷ (S-block n) v ≡ swap n v
S-block-action zero    v = x12-action v
S-block-action (suc n) v =
  trans (encode-parallel-correct (contiguous (2 ^ ₂₊ n)) (S-block n) (S-block n) v)
    (parallel-cong (contiguous (2 ^ ₂₊ n)) (S-block-action n) (S-block-action n) v)

eᶜ : C.Gen n → E.Levels n
eᶜ (C.gate₀ ())
eᶜ (C.gate₁ {n} C.X-gate)    = E.X-block n
eᶜ (C.gate₂ {n} C.CX-gate)   = E.CX-block n
eᶜ (C.gate₂ {n} C.SWAP-gate) = S-block n
eᶜ (C.gate₃ {n} C.CCX-gate)  = E.CCX-block n
eᶜ (C._↥ {n} g)              = E.copy (alternating (2 ^ n)) (eᶜ g)

encodeᶜ : C.Circuit n → E.Levels n
encodeᶜ = eᶜ ʷ

eᶜ-action : (g : C.Gen n) → ∀ v → A.actVʷ (eᶜ g) v ≡ classical₀ g v
eᶜ-action (C.gate₀ ())
eᶜ-action (C.gate₁ {n} C.X-gate)    v = encoding-action (H.X {n}) v
eᶜ-action (C.gate₂ {n} C.CX-gate)   v = encoding-action (H.CX {n}) v
eᶜ-action (C.gate₂ {n} C.SWAP-gate) v = S-block-action n v
eᶜ-action (C.gate₃ {n} C.CCX-gate)  v = encoding-action (H.CCX {n}) v
eᶜ-action (C._↥ {n} g) v =
  trans (encode-parallel-correct (alternating (2 ^ n)) (eᶜ g) (eᶜ g) v)
    (parallel-cong (alternating (2 ^ n)) (eᶜ-action g) (eᶜ-action g) v)

encodeᶜ-action : (w : C.Circuit n) → ∀ v → A.actVʷ (encodeᶜ w) v ≡ classical w v
encodeᶜ-action [ g ]ʷ   v = eᶜ-action g v
encodeᶜ-action ε        v = refl
encodeᶜ-action (u • w)  v =
  trans (cong (A.actVʷ (encodeᶜ u)) (encodeᶜ-action w v)) (encodeᶜ-action u (classical w v))
