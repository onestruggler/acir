------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness in TofH(3) = L₈.  A circuit without H₂ denotes there the
-- image of its matrix in O(8, 𝔻) (enc-noH), so Figures 4 and 7 and r_K
-- hold by Soundness; the relations of Figure 8 are checked by computing
-- their matrices over ℤ[1/√2].  Then the congruences R₁⁺ (in O(8, 𝔻))
-- and R₂, R₂⁺ (in L₈) are sound.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.SoundnessH where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (⌊_⌋ʷ)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SL
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics using (actV ; set₁ ; set₂ ; mapM)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using () renaming (RingD to RingD₁)
open import Quantum.Synthesis.Matrix using (_·*·_)

open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.Soundness
import Examples.Groups.CCX+HH-3qubit-opus.Congruence as C

open SL.Dim 4 using (⟦_⟧ᴸ)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Circuits without H₂

noHᵍ : Gate k → Bool
noHᵍ H₂ = false
noHᵍ _  = true

noH : Word (Gate k) → Bool
noH [ g ]ʷ = noHᵍ g
noH ε = true
noH (u • w) = noH u ∧ noH w

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl
  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} h = h

  enc-g : (g : Gate k) → noHᵍ g ≡ true → encᴸ g ≡ ⌊ enc g ⌋ʷ
  enc-g H₂ ()
  enc-g X₀ _ = refl
  enc-g X₁ _ = refl
  enc-g X₂ _ = refl
  enc-g Z₀ _ = refl
  enc-g Z₁ _ = refl
  enc-g Z₂ _ = refl
  enc-g CX₀₁ _ = refl
  enc-g CX₀₂ _ = refl
  enc-g CX₁₀ _ = refl
  enc-g CX₁₂ _ = refl
  enc-g CX₂₀ _ = refl
  enc-g CX₂₁ _ = refl
  enc-g CZ₀₁ _ = refl
  enc-g CZ₀₂ _ = refl
  enc-g CZ₁₂ _ = refl
  enc-g CCX₀₁ _ = refl
  enc-g CCX₀₂ _ = refl
  enc-g CCX₁₂ _ = refl
  enc-g K₀₁ _ = refl
  enc-g K₁₂ _ = refl
  enc-g SW₀₁ _ = refl
  enc-g SW₀₂ _ = refl
  enc-g SW₁₂ _ = refl
  enc-g NK _ = refl
  enc-g CCZ _ = refl

-- An H₂-free circuit is encoded as a word over 𝒢₈.
enc-noH : (w : Word (Gate k)) → noH w ≡ true → encᴸʷ w ≡ ⌊ encʷ w ⌋ʷ
enc-noH [ g ]ʷ h = enc-g g h
enc-noH ε h = refl
enc-noH (u • w) h = cong₂ _•_ (enc-noH u (∧-l {noH u} h)) (enc-noH w (∧-r {noH u} h))

-- Its matrix in L₈ is that of O(8, 𝔻).
⟦⟧ᴴ-noH : (w : Word (Gate k)) → noH w ≡ true → ⟦ w ⟧ᴴ ≡ mapM ⟦ w ⟧
⟦⟧ᴴ-noH w h = trans (cong ⟦_⟧ᴸ (enc-noH w h)) (SL.⟦⌊⌋⟧ 4 (encʷ w))

private
  transfer : {w v : Word (Gate k)} → noH w ≡ true → noH v ≡ true → ⟦ w ⟧ ≡ ⟦ v ⟧ → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
  transfer {w = w} {v} hw hv eq = trans (⟦⟧ᴴ-noH w hw) (trans (cong mapM eq) (sym (⟦⟧ᴴ-noH v hv)))

  noH₀ : {w v : Word (Gate k)} → w ===₀ v → noH w ≡ true × noH v ≡ true
  noH₀ r1 = refl , refl
  noH₀ r2 = refl , refl
  noH₀ r3 = refl , refl
  noH₀ r4 = refl , refl
  noH₀ r5 = refl , refl
  noH₀ r6 = refl , refl
  noH₀ r7 = refl , refl
  noH₀ r8 = refl , refl
  noH₀ r9 = refl , refl
  noH₀ r10 = refl , refl
  noH₀ r11 = refl , refl
  noH₀ r12 = refl , refl
  noH₀ r13 = refl , refl
  noH₀ r14 = refl , refl
  noH₀ r15 = refl , refl
  noH₀ r16 = refl , refl
  noH₀ r17 = refl , refl
  noH₀ r18 = refl , refl
  noH₀ r19 = refl , refl
  noH₀ r20 = refl , refl
  noH₀ r21 = refl , refl
  noH₀ r22 = refl , refl
  noH₀ r23 = refl , refl
  noH₀ r24 = refl , refl
  noH₀ r25 = refl , refl
  noH₀ r26 = refl , refl
  noH₀ r27 = refl , refl
  noH₀ r28 = refl , refl
  noH₀ r29 = refl , refl
  noH₀ r30 = refl , refl
  noH₀ r31 = refl , refl
  noH₀ r32 = refl , refl
  noH₀ r33 = refl , refl
  noH₀ r34 = refl , refl
  noH₀ r35 = refl , refl
  noH₀ r36 = refl , refl
  noH₀ r37 = refl , refl
  noH₀ r38 = refl , refl
  noH₀ r39 = refl , refl
  noH₀ r40 = refl , refl
  noH₀ r41 = refl , refl
  noH₀ r42 = refl , refl
  noH₀ r43 = refl , refl
  noH₀ r44 = refl , refl
  noH₀ r45 = refl , refl
  noH₀ r46 = refl , refl

  noH₇ : {w v : Word (Gate (suc k))} → w ===₇ v → noH w ≡ true × noH v ≡ true
  noH₇ r83 = refl , refl
  noH₇ r84 = refl , refl
  noH₇ r85 = refl , refl
  noH₇ r86 = refl , refl
  noH₇ r87 = refl , refl
  noH₇ r88 = refl , refl
  noH₇ r89 = refl , refl
  noH₇ r90 = refl , refl
  noH₇ r91 = refl , refl
  noH₇ r92 = refl , refl
  noH₇ r93 = refl , refl
  noH₇ r94 = refl , refl
  noH₇ r95 = refl , refl
  noH₇ r96 = refl , refl
  noH₇ r97 = refl , refl
  noH₇ r98 = refl , refl
  noH₇ r99 = refl , refl
  noH₇ r100 = refl , refl
  noH₇ r101 = refl , refl

  noHᴷ : {w v : Word (Gate (suc k))} → w ===ᴷ v → noH w ≡ true × noH v ≡ true
  noHᴷ rK = refl , refl

soundᴴ₀ : {w v : Word (Gate k)} → w ===₀ v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
soundᴴ₀ {w = w} {v} r = transfer {w = w} {v} (proj₁ (noH₀ {w = w} {v} r)) (proj₂ (noH₀ {w = w} {v} r)) (sound₀ {w = w} {v} r)

soundᴴ₇ : {w v : Word (Gate (suc k))} → w ===₇ v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
soundᴴ₇ {w = w} {v} r = transfer {w = w} {v} (proj₁ (noH₇ {w = w} {v} r)) (proj₂ (noH₇ {w = w} {v} r)) (sound₇ {w = w} {v} r)

soundᴴᴷ : {w v : Word (Gate (suc k))} → w ===ᴷ v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
soundᴴᴷ {w = w} {v} r = transfer {w = w} {v} (proj₁ (noHᴷ {w = w} {v} r)) (proj₂ (noHᴷ {w = w} {v} r)) (soundᴷ {w = w} {v} r)

------------------------------------------------------------------------
-- Figure 8, computed over ℤ[1/√2]

opaque
  unfolding actV set₁ set₂ R2._+ᴰ_ R2._*ᴰ_ R2.-ᴰ_

  sound₈ : {w v : Word (Gate (suc (suc k)))} → w ===₈ v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
  sound₈ r102 = refl
  sound₈ r103 = refl
  sound₈ r104 = refl
  sound₈ r105 = refl
  sound₈ r106 = refl
  sound₈ r107 = refl
  sound₈ r108 = refl

------------------------------------------------------------------------
-- The congruences

-- R₁⁺ in O(8, 𝔻).
sound₁⁺-ax : {w v : Word G₁} → w ===₁⁺ v → ⟦ w ⟧ ≡ ⟦ v ⟧
sound₁⁺-ax (fig4 r) = sound₀ r
sound₁⁺-ax (fig7 r) = sound₇ r
sound₁⁺-ax (rK r) = soundᴷ r

sound₁-ax : {w v : Word G₁} → w ===₁ v → ⟦ w ⟧ ≡ ⟦ v ⟧
sound₁-ax (fig4 r) = sound₀ r
sound₁-ax (fig7 r) = sound₇ r

module _ {X : Set} where

  -- A congruence over Σ-words whose axioms hold in O(8, 𝔻), resp. L₈.
  module SoundO {k} (Γ : _) (ax : ∀ {w v : Word (Gate k)} → Γ w v → ⟦ w ⟧ ≡ ⟦ v ⟧) =
    C.Sound Γ ⟦_⟧ (λ a b → a ·*· b) S1.𝕀 ⟦•⟧ refl (λ a b c → S1.·*·-assoc a b c) S1.·*·-identityˡ S1.·*·-identityʳ ax

  module SoundL {k} (Γ : _) (ax : ∀ {w v : Word (Gate k)} → Γ w v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ) =
    C.Sound Γ ⟦_⟧ᴴ (λ a b → a ·*· b) SL.𝕀 ⟦•⟧ᴴ refl (λ a b c → SL.·*·-assoc a b c) SL.·*·-identityˡ SL.·*·-identityʳ ax

-- R₀ (at level 0), R₁ and R₁⁺ are sound in O(8, 𝔻).
sound₀* : {w v : Word Gᴰ} → PB._≈_ _===₀_ w v → ⟦ w ⟧ ≡ ⟦ v ⟧
sound₀* = SoundO.sound {X = Gᴰ} _===₀_ sound₀

sound₁* : {w v : Word G₁} → PB._≈_ _===₁_ w v → ⟦ w ⟧ ≡ ⟦ v ⟧
sound₁* = SoundO.sound {X = G₁} _===₁_ sound₁-ax

sound₁⁺* : {w v : Word G₁} → PB._≈_ _===₁⁺_ w v → ⟦ w ⟧ ≡ ⟦ v ⟧
sound₁⁺* = SoundO.sound {X = G₁} _===₁⁺_ sound₁⁺-ax

-- R₂ and R₂⁺ are sound in L₈.
sound₂-ax : {w v : Word G₂} → w ===₂ v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
sound₂-ax (fig4 r) = soundᴴ₀ r
sound₂-ax (fig7 r) = soundᴴ₇ r
sound₂-ax (fig8 r) = sound₈ r

sound₂⁺-ax : {w v : Word G₂} → w ===₂⁺ v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
sound₂⁺-ax (fig4 r) = soundᴴ₀ r
sound₂⁺-ax (fig7 r) = soundᴴ₇ r
sound₂⁺-ax (fig8 r) = sound₈ r
sound₂⁺-ax (rK r) = soundᴴᴷ r

sound₂* : {w v : Word G₂} → PB._≈_ _===₂_ w v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
sound₂* = SoundL.sound {X = G₂} _===₂_ sound₂-ax

sound₂⁺* : {w v : Word G₂} → PB._≈_ _===₂⁺_ w v → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ
sound₂⁺* = SoundL.sound {X = G₂} _===₂⁺_ sound₂⁺-ax
