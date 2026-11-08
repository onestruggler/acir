------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 6.3 of Amy, Ross and Wesley, with r_K: the circuits over
-- Σ₂ = Σ₁ ∪ {H₂} modulo R₂⁺ = R₀ ∪ R₈₄ ∪ Figure 8 ∪ {r_K} present
-- TofH(3) = L₈.
--
-- Completeness as for O(8, 𝔻), now through Li, Ross and Selinger's
-- presentation of L₈ by Tables 1 and 2 (Scaled.Completeness): a circuit
-- over Σ₂ is the decoding of its encoding (Goodᴴ, from Good one level
-- down, and H₂ for I ⊗ H), and the decoding respects Tables 1 and 2
-- (DecodeH).  Surjectivity: the decoding of a generator of ℱ₈ has its
-- matrix (dec-sem, and H₂ for I ⊗ H).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.PresentationH where

open import Algebra.Bundles using (Group ; Monoid)
open import Data.Bool.Base using (true)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Quantum.Synthesis.Matrix using (_·*·_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as L using (Gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as LS using (Genᴸ ; ⌊_⌋ ; IH ; _===ᴸ_)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SL
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics using (mapM)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness 3 as LC
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation 3 as LP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.SoundnessH using (sound₂⁺* ; noH ; ⟦⟧ᴴ-noH)
open import Examples.Groups.CCX+HH-3qubit-opus.Lift using (lift₁₂)
open import Examples.Groups.CCX+HH-3qubit-opus.Completeness using (module Complete)
open import Examples.Groups.CCX+HH-3qubit-opus.Derived using (derived ; invol₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Decode coxeter₁ using (dec ; decʷ)
open import Examples.Groups.CCX+HH-3qubit-opus.PresentationO8 using (dec-sem)
open import Examples.Groups.CCX+HH-3qubit-opus.DecodeH

open PB _===₂⁺_ using (_≈_ ; refl ; sym ; trans ; cong ; axiom)
open SL.Dim 4 using (⟦_⟧ᴸ ; ⟦•⟧ᴸ)

------------------------------------------------------------------------
-- Completeness

Goodᴴ : Word G₂ → Set
Goodᴴ w = decᴸʷ (encᴸʷ w) ≈ w

private
  good₁ = Complete.good derived

good-gate : (g : G₂) → Goodᴴ [ g ]ʷ
good-gate X₀ = lift₁₂ (good₁ [ X₀ ]ʷ)
good-gate X₁ = lift₁₂ (good₁ [ X₁ ]ʷ)
good-gate X₂ = lift₁₂ (good₁ [ X₂ ]ʷ)
good-gate Z₀ = lift₁₂ (good₁ [ Z₀ ]ʷ)
good-gate Z₁ = lift₁₂ (good₁ [ Z₁ ]ʷ)
good-gate Z₂ = lift₁₂ (good₁ [ Z₂ ]ʷ)
good-gate CX₀₁ = lift₁₂ (good₁ [ CX₀₁ ]ʷ)
good-gate CX₀₂ = lift₁₂ (good₁ [ CX₀₂ ]ʷ)
good-gate CX₁₀ = lift₁₂ (good₁ [ CX₁₀ ]ʷ)
good-gate CX₁₂ = lift₁₂ (good₁ [ CX₁₂ ]ʷ)
good-gate CX₂₀ = lift₁₂ (good₁ [ CX₂₀ ]ʷ)
good-gate CX₂₁ = lift₁₂ (good₁ [ CX₂₁ ]ʷ)
good-gate CZ₀₁ = lift₁₂ (good₁ [ CZ₀₁ ]ʷ)
good-gate CZ₀₂ = lift₁₂ (good₁ [ CZ₀₂ ]ʷ)
good-gate CZ₁₂ = lift₁₂ (good₁ [ CZ₁₂ ]ʷ)
good-gate CCX₀₁ = lift₁₂ (good₁ [ CCX₀₁ ]ʷ)
good-gate CCX₀₂ = lift₁₂ (good₁ [ CCX₀₂ ]ʷ)
good-gate CCX₁₂ = lift₁₂ (good₁ [ CCX₁₂ ]ʷ)
good-gate K₀₁ = lift₁₂ (good₁ [ K₀₁ ]ʷ)
good-gate K₁₂ = lift₁₂ (good₁ [ K₁₂ ]ʷ)
good-gate SW₀₁ = lift₁₂ (good₁ [ SW₀₁ ]ʷ)
good-gate SW₀₂ = lift₁₂ (good₁ [ SW₀₂ ]ʷ)
good-gate SW₁₂ = lift₁₂ (good₁ [ SW₁₂ ]ʷ)
good-gate NK = lift₁₂ (good₁ [ NK ]ʷ)
good-gate CCZ = lift₁₂ (good₁ [ CCZ ]ʷ)
good-gate H₂ = refl

goodᴴ : (w : Word G₂) → Goodᴴ w
goodᴴ [ g ]ʷ   = good-gate g
goodᴴ ε       = refl
goodᴴ (u • v) = cong (goodᴴ u) (goodᴴ v)

complete₂ : {w v : Word G₂} → ⟦ w ⟧ᴴ ≡ ⟦ v ⟧ᴴ → w ≈ v
complete₂ {w} {v} h =
  trans (sym (goodᴴ w)) (trans (decᴸ-cong (LC.completeness {encᴸʷ w} {encᴸʷ v} h)) (goodᴴ v))

------------------------------------------------------------------------
-- The decoding of a generator has its matrix

private
  noH-up : (w : Word G₁) → noH (↑ʷ w) ≡ true
  noH-up [ X₀ ]ʷ = Eq.refl
  noH-up [ X₁ ]ʷ = Eq.refl
  noH-up [ X₂ ]ʷ = Eq.refl
  noH-up [ Z₀ ]ʷ = Eq.refl
  noH-up [ Z₁ ]ʷ = Eq.refl
  noH-up [ Z₂ ]ʷ = Eq.refl
  noH-up [ CX₀₁ ]ʷ = Eq.refl
  noH-up [ CX₀₂ ]ʷ = Eq.refl
  noH-up [ CX₁₀ ]ʷ = Eq.refl
  noH-up [ CX₁₂ ]ʷ = Eq.refl
  noH-up [ CX₂₀ ]ʷ = Eq.refl
  noH-up [ CX₂₁ ]ʷ = Eq.refl
  noH-up [ CZ₀₁ ]ʷ = Eq.refl
  noH-up [ CZ₀₂ ]ʷ = Eq.refl
  noH-up [ CZ₁₂ ]ʷ = Eq.refl
  noH-up [ CCX₀₁ ]ʷ = Eq.refl
  noH-up [ CCX₀₂ ]ʷ = Eq.refl
  noH-up [ CCX₁₂ ]ʷ = Eq.refl
  noH-up [ K₀₁ ]ʷ = Eq.refl
  noH-up [ K₁₂ ]ʷ = Eq.refl
  noH-up [ SW₀₁ ]ʷ = Eq.refl
  noH-up [ SW₀₂ ]ʷ = Eq.refl
  noH-up [ SW₁₂ ]ʷ = Eq.refl
  noH-up [ NK ]ʷ = Eq.refl
  noH-up [ CCZ ]ʷ = Eq.refl
  noH-up ε = Eq.refl
  noH-up (u • v) rewrite noH-up u | noH-up v = Eq.refl

  enc-up : (g : G₁) → enc (up g) ≡ enc g
  enc-up X₀ = Eq.refl
  enc-up X₁ = Eq.refl
  enc-up X₂ = Eq.refl
  enc-up Z₀ = Eq.refl
  enc-up Z₁ = Eq.refl
  enc-up Z₂ = Eq.refl
  enc-up CX₀₁ = Eq.refl
  enc-up CX₀₂ = Eq.refl
  enc-up CX₁₀ = Eq.refl
  enc-up CX₁₂ = Eq.refl
  enc-up CX₂₀ = Eq.refl
  enc-up CX₂₁ = Eq.refl
  enc-up CZ₀₁ = Eq.refl
  enc-up CZ₀₂ = Eq.refl
  enc-up CZ₁₂ = Eq.refl
  enc-up CCX₀₁ = Eq.refl
  enc-up CCX₀₂ = Eq.refl
  enc-up CCX₁₂ = Eq.refl
  enc-up K₀₁ = Eq.refl
  enc-up K₁₂ = Eq.refl
  enc-up SW₀₁ = Eq.refl
  enc-up SW₀₂ = Eq.refl
  enc-up SW₁₂ = Eq.refl
  enc-up NK = Eq.refl
  enc-up CCZ = Eq.refl

  encʷ-up : (w : Word G₁) → encʷ (↑ʷ w) ≡ encʷ w
  encʷ-up [ g ]ʷ   = enc-up g
  encʷ-up ε       = Eq.refl
  encʷ-up (u • v) = Eq.cong₂ _•_ (encʷ-up u) (encʷ-up v)

decᴸ-sem : (x : Genᴸ 8) → ⟦ decᴸ x ⟧ᴴ ≡ ⟦ [ x ]ʷ ⟧ᴸ
decᴸ-sem ⌊ g ⌋ = Eq.trans (⟦⟧ᴴ-noH (↑ʷ (dec g)) (noH-up (dec g)))
  (Eq.trans (Eq.cong (λ u → mapM (S1.⟦ u ⟧ᵐ)) (encʷ-up (dec g)))
    (Eq.trans (Eq.cong mapM (dec-sem g)) (Eq.sym (SL.⟦⌊⌋⟧ 4 [ g ]ʷ))))
decᴸ-sem IH = Eq.refl

decᴸ-semʷ : (u : Word (Genᴸ 8)) → ⟦ decᴸʷ u ⟧ᴴ ≡ ⟦ u ⟧ᴸ
decᴸ-semʷ [ x ]ʷ   = decᴸ-sem x
decᴸ-semʷ ε       = Eq.refl
decᴸ-semʷ (u • v) = Eq.trans (⟦•⟧ᴴ (decᴸʷ u) (decᴸʷ v))
  (Eq.trans (Eq.cong₂ _·*·_ (decᴸ-semʷ u) (decᴸ-semʷ v)) (Eq.sym (⟦•⟧ᴸ u v)))

------------------------------------------------------------------------
-- The presentation

grouplike₂ : Grouplike _===₂⁺_
grouplike₂ X₀ = [ X₀ ]ʷ , lift₁₂ (invol₁ X₀)
grouplike₂ X₁ = [ X₁ ]ʷ , lift₁₂ (invol₁ X₁)
grouplike₂ X₂ = [ X₂ ]ʷ , lift₁₂ (invol₁ X₂)
grouplike₂ Z₀ = [ Z₀ ]ʷ , lift₁₂ (invol₁ Z₀)
grouplike₂ Z₁ = [ Z₁ ]ʷ , lift₁₂ (invol₁ Z₁)
grouplike₂ Z₂ = [ Z₂ ]ʷ , lift₁₂ (invol₁ Z₂)
grouplike₂ CX₀₁ = [ CX₀₁ ]ʷ , lift₁₂ (invol₁ CX₀₁)
grouplike₂ CX₀₂ = [ CX₀₂ ]ʷ , lift₁₂ (invol₁ CX₀₂)
grouplike₂ CX₁₀ = [ CX₁₀ ]ʷ , lift₁₂ (invol₁ CX₁₀)
grouplike₂ CX₁₂ = [ CX₁₂ ]ʷ , lift₁₂ (invol₁ CX₁₂)
grouplike₂ CX₂₀ = [ CX₂₀ ]ʷ , lift₁₂ (invol₁ CX₂₀)
grouplike₂ CX₂₁ = [ CX₂₁ ]ʷ , lift₁₂ (invol₁ CX₂₁)
grouplike₂ CZ₀₁ = [ CZ₀₁ ]ʷ , lift₁₂ (invol₁ CZ₀₁)
grouplike₂ CZ₀₂ = [ CZ₀₂ ]ʷ , lift₁₂ (invol₁ CZ₀₂)
grouplike₂ CZ₁₂ = [ CZ₁₂ ]ʷ , lift₁₂ (invol₁ CZ₁₂)
grouplike₂ CCX₀₁ = [ CCX₀₁ ]ʷ , lift₁₂ (invol₁ CCX₀₁)
grouplike₂ CCX₀₂ = [ CCX₀₂ ]ʷ , lift₁₂ (invol₁ CCX₀₂)
grouplike₂ CCX₁₂ = [ CCX₁₂ ]ʷ , lift₁₂ (invol₁ CCX₁₂)
grouplike₂ K₀₁ = [ K₀₁ ]ʷ , lift₁₂ (invol₁ K₀₁)
grouplike₂ K₁₂ = [ K₁₂ ]ʷ , lift₁₂ (invol₁ K₁₂)
grouplike₂ SW₀₁ = [ SW₀₁ ]ʷ , lift₁₂ (invol₁ SW₀₁)
grouplike₂ SW₀₂ = [ SW₀₂ ]ʷ , lift₁₂ (invol₁ SW₀₂)
grouplike₂ SW₁₂ = [ SW₁₂ ]ʷ , lift₁₂ (invol₁ SW₁₂)
grouplike₂ NK = [ NK ]ʷ , lift₁₂ (invol₁ NK)
grouplike₂ CCZ = [ CCZ ]ʷ , lift₁₂ (invol₁ CCZ)
grouplike₂ H₂ = [ H₂ ]ʷ , axiom (fig8 r108)

-- The matrices of TofH(3), as elements of L₈.
⟦_⟧ˡ : Word G₂ → Group.Carrier TofH3
⟦ w ⟧ˡ = LP.⟦ encᴸʷ w ⟧ˡ

private
  open _IsMonoidPresentationOf_ LP.monoidPresentation using () renaming (iso to lp-iso)
  open MonoidMorphisms (Monoid.rawMonoid (PP.•-ε-monoid (_===ᴸ_ {8}))) (Monoid.rawMonoid (Group.monoid TofH3))
    using (module IsMonoidIsomorphism)

  -- Every element of L₈ is the matrix of a word over ℱ₈.
  word-of : (A : Group.Carrier TofH3) → Word (Genᴸ 8)
  word-of A = proj₁ (IsMonoidIsomorphism.surjective lp-iso A)

  word-of-correct : (A : Group.Carrier TofH3) → ⟦ word-of A ⟧ᴸ ≡ proj₁ A
  word-of-correct A = proj₂ (IsMonoidIsomorphism.surjective lp-iso A) PB.refl

monoidPresentation : _===₂⁺_ IsMonoidPresentationOf (Group.monoid TofH3)
monoidPresentation = record
  { ⟦_⟧ = ⟦_⟧ˡ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = sound₂⁺* }
          ; homo = ⟦•⟧ᴴ
          }
        ; ε-homo = Eq.refl
        }
      ; injective = complete₂
      }
    ; surjective = λ A → decᴸʷ (word-of A) , λ z≈ →
        Eq.trans (sound₂⁺* z≈) (Eq.trans (decᴸ-semʷ (word-of A)) (word-of-correct A))
    }
  }

-- Theorem 6.3, with r_K.
presentation : _===₂⁺_ IsPresentationOf TofH3
presentation = monoidPresentation⇒presentation monoidPresentation grouplike₂
