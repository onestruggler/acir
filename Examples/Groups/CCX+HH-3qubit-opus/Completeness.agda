------------------------------------------------------------------------
-- Presentations of groups
--
-- R₁⁺ presents O(8, 𝔻), given the Coxeter relations for the circuits
-- T d and a few circuit identities derived from Figure 4 (the record
-- Derived, which Derived.agda fills in).
--
-- Completeness by the encoding and the decoding: a circuit w denotes
-- the matrix of its encoding, two circuits with the same matrix have
-- encodings equal by Table 1 (Li, Ross and Selinger), the decoding
-- respects Table 1 (Decode), and decoding an encoded circuit gives it
-- back (Good): for the circuits T d, (-1)_[0] and NK by the aliases of
-- Decode, and for each gate from those along Figure 4's definitions,
-- Good being closed under products and, by soundness, under R₁⁺.
--
-- Surjectivity: the decoding of a generator has the generator's
-- matrix (dec-sem), by induction along Li, Ross and Selinger's
-- reduction of a generator to a basic one by adjacent transpositions
-- (Conjugation.decompose).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Perm using (Coxeter)
import Presentation.Base as PB
open import Word.Base using ([_]ʷ ; ε ; _•_)

module Examples.Groups.CCX+HH-3qubit-opus.Completeness where

open import Algebra.Bundles using (Group)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Fin using (#_)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Quantum.Synthesis.Matrix using (_·*·_)

open import Word.Base using (Word)
import Presentation.Properties as PP
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as L using (Gen ; M-gen ; X-gen ; K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
open import Examples.Groups.CCX+HH-TwoLevel.MainLemma {8} using () renaming (completeness to lrs-complete)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {8} using () renaming (sound-act to lrs-sound-act)
import Examples.Groups.CCX+HH-TwoLevel.Presentation {8} as LP
import Examples.Groups.CCX+HH-TwoLevel.Conjugation {8} as Conj

open import Examples.Groups.CCX+HH-3qubit-opus.Encoding
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.SoundnessH using (sound₁⁺*)
open import Examples.Groups.CCX+HH-3qubit-opus.StdMatrices

open PB _===₁⁺_ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

------------------------------------------------------------------------
-- What the search derives

record Derived : Set where
  field
    coxeter : Coxeter _===₁⁺_
    invol   : (g : G₁) → [ g ]ʷ • [ g ]ʷ ≈ ε
    cx12r   : CX12 ≈ T 2 • CCX01
    cx02r   : CX02 ≈ T 4 • CCX01
    x2r     : X2 ≈ T 0 • CCX01 • CX12 • CX02
    ccx02r  : CCX02 ≈ CX12 • T 5 • CX12
    cx21r   : CX21 ≈ CX12 • T 1 • CX12 • CCX02
    cx01r   : CX01 ≈ SW12 • CX02 • SW12
    ccx12r  : CCX12 ≈ CX02 • CX01 • T 3 • CX02 • CX01
    cx10r   : CX10 ≈ CCX12 • CX12 • CCX12 • CX12
    cx20r   : CX20 ≈ SW01 • CX21 • SW01
    x0r     : X0 ≈ SW02 • X2 • SW02
    cczr    : CCZw ≈ X2 • X1 • X0 • m0 • X0 • X1 • X2

module Complete (D : Derived) where

  open Derived D
  open import Examples.Groups.CCX+HH-3qubit-opus.Decode coxeter

  ----------------------------------------------------------------------
  -- Decoding an encoded circuit

  -- Two-level words with the same matrix decode to equivalent circuits.
  lrs : {u v : Word (Gen 8)} → S1.⟦ u ⟧ᵐ ≡ S1.⟦ v ⟧ᵐ → decʷ u ≈ decʷ v
  lrs {u} {v} h = dec-cong {u} {v} (lrs-complete {u} {v} h)

  Good : Word G₁ → Set
  Good w = decʷ (encʷ w) ≈ w

  Good-• : {u v : Word G₁} → Good u → Good v → Good (u • v)
  Good-• gu gv = cong gu gv

  Good-≈ : {w w′ : Word G₁} → w ≈ w′ → Good w′ → Good w
  Good-≈ {w} {w′} e g = trans (lrs {encʷ w} {encʷ w′} (sound₁⁺* e)) (trans g (sym e))

  private
    by : {g : G₁} {w : Word G₁} → [ g ]ʷ ≈ w → Good w → Good [ g ]ʷ
    by = Good-≈

    via-std : (w : Word G₁) (s : Std) → S1.⟦ encʷ w ⟧ᵐ ≡ S1.⟦ [ std s ]ʷ ⟧ᵐ → al s ≡ w → Good w
    via-std w s h Eq.refl = trans (lrs {encʷ w} {[ std s ]ʷ} h) (al-ok s)

  good-T : (i : ℕ) → Good (T i)
  good-T 0 = via-std (T 0) x01 mT0 Eq.refl
  good-T 1 = via-std (T 1) x12 mT1 Eq.refl
  good-T 2 = via-std (T 2) x23 mT2 Eq.refl
  good-T 3 = via-std (T 3) x34 mT3 Eq.refl
  good-T 4 = via-std (T 4) x45 mT4 Eq.refl
  good-T 5 = via-std (T 5) x56 mT5 Eq.refl
  good-T (suc (suc (suc (suc (suc (suc _)))))) = via-std (T 6) x67 mT6 Eq.refl

  good-m0 : Good m0
  good-m0 = via-std m0 m0ˢ mm0 Eq.refl

  good-NK : Good NKw
  good-NK = al-ok k0123

  -- Along the definitions of Figure 4.
  g-CCX01 = good-T 6
  g-CX12 = by cx12r (Good-• (good-T 2) g-CCX01)
  g-CX02 = by cx02r (Good-• (good-T 4) g-CCX01)
  g-X2 = by x2r (Good-• (good-T 0) (Good-• g-CCX01 (Good-• g-CX12 g-CX02)))
  g-CCX02 = by ccx02r (Good-• g-CX12 (Good-• (good-T 5) g-CX12))
  g-CX21 = by cx21r (Good-• g-CX12 (Good-• (good-T 1) (Good-• g-CX12 g-CCX02)))
  g-SW12 = by (axiom (fig4 r8)) (Good-• g-CX12 (Good-• g-CX21 g-CX12))
  g-CX01 = by cx01r (Good-• g-SW12 (Good-• g-CX02 g-SW12))
  g-CCX12 = by ccx12r (Good-• g-CX02 (Good-• g-CX01 (Good-• (good-T 3) (Good-• g-CX02 g-CX01))))
  g-CX10 = by cx10r (Good-• g-CCX12 (Good-• g-CX12 (Good-• g-CCX12 g-CX12)))
  g-SW01 = by (axiom (fig4 r13)) (Good-• g-CX01 (Good-• g-CX10 g-CX01))
  g-CX20 = by cx20r (Good-• g-SW01 (Good-• g-CX21 g-SW01))
  g-SW02 = by (axiom (fig4 r10)) (Good-• g-CX02 (Good-• g-CX20 g-CX02))
  g-X0 = by x0r (Good-• g-SW02 (Good-• g-X2 g-SW02))
  g-X1 = by (axiom (fig4 r2)) (Good-• g-CX01 (Good-• g-X0 (Good-• g-CX01 g-X0)))
  g-K12 = by (axiom (rK rK)) (Good-• g-X0 (Good-• good-NK (Good-• g-X0 good-NK)))
  g-CZ01 = by (axiom (fig4 r1)) (Good-• g-K12 (Good-• g-CX01 g-K12))
  g-Z0 = by (axiom (fig4 r3)) (Good-• g-CZ01 (Good-• g-CX01 (Good-• g-CZ01 g-CX01)))
  g-Z1 = by (axiom (fig4 r4)) (Good-• g-K12 (Good-• g-X1 g-K12))
  g-K01 = by (axiom (fig4 r11)) (Good-• g-SW02 (Good-• g-K12 g-SW02))
  g-Z2 = by (axiom (fig4 r16)) (Good-• g-SW02 (Good-• g-Z0 g-SW02))
  g-CZ02 = by (axiom (fig4 r18)) (Good-• g-SW12 (Good-• g-CZ01 g-SW12))
  g-CZ12 = by (axiom (fig4 r19)) (Good-• g-SW01 (Good-• g-CZ02 g-SW01))
  g-CCZ = by cczr (Good-• g-X2 (Good-• g-X1 (Good-• g-X0 (Good-• good-m0 (Good-• g-X0 (Good-• g-X1 g-X2))))))

  good-gate : (g : G₁) → Good [ g ]ʷ
  good-gate X₀ = g-X0
  good-gate X₁ = g-X1
  good-gate X₂ = g-X2
  good-gate Z₀ = g-Z0
  good-gate Z₁ = g-Z1
  good-gate Z₂ = g-Z2
  good-gate CX₀₁ = g-CX01
  good-gate CX₀₂ = g-CX02
  good-gate CX₁₀ = g-CX10
  good-gate CX₁₂ = g-CX12
  good-gate CX₂₀ = g-CX20
  good-gate CX₂₁ = g-CX21
  good-gate CZ₀₁ = g-CZ01
  good-gate CZ₀₂ = g-CZ02
  good-gate CZ₁₂ = g-CZ12
  good-gate CCX₀₁ = g-CCX01
  good-gate CCX₀₂ = g-CCX02
  good-gate CCX₁₂ = g-CCX12
  good-gate K₀₁ = g-K01
  good-gate K₁₂ = g-K12
  good-gate SW₀₁ = g-SW01
  good-gate SW₀₂ = g-SW02
  good-gate SW₁₂ = g-SW12
  good-gate NK = good-NK
  good-gate CCZ = g-CCZ

  good : (w : Word G₁) → Good w
  good [ g ]ʷ   = good-gate g
  good ε       = refl
  good (u • v) = Good-• (good u) (good v)

  ----------------------------------------------------------------------
  -- Completeness

  complete : {w v : Word G₁} → ⟦ w ⟧ ≡ ⟦ v ⟧ → w ≈ v
  complete {w} {v} h = trans (sym (good w)) (trans (lrs {encʷ w} {encʷ v} h) (good v))
