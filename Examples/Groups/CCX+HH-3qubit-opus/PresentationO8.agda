------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 5.2 of Amy, Ross and Wesley, with r_K: the circuits over Σ₁
-- modulo R₁⁺ = R₀ ∪ R₈₄ ∪ {r_K} present O(8, 𝔻).
--
-- * ⟦_⟧ is a homomorphism and respects R₁⁺ (SoundnessH);
-- * it is one-to-one on circuits modulo R₁⁺ (Completeness, with the
--   identities of Derived);
-- * it is onto: an orthogonal matrix is the matrix of a word over Li,
--   Ross and Selinger's generators, and the decoding of that word has
--   the same matrix (dec-sem).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.PresentationO8 where

open import Algebra.Bundles using (Group)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (RingD)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as L using (Gen ; M-gen ; X-gen ; K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {8} using () renaming (sound-act to lrs-sound-act)
import Examples.Groups.CCX+HH-TwoLevel.Presentation {8} as LP
import Examples.Groups.CCX+HH-TwoLevel.Conjugation {8} as Conj

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics
open import Examples.Groups.CCX+HH-3qubit-opus.SoundnessH using (sound₁⁺*)
open import Examples.Groups.CCX+HH-3qubit-opus.Completeness using (module Complete)
open import Examples.Groups.CCX+HH-3qubit-opus.Derived using (derived ; invol₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Decode coxeter₁ using (dec ; decʷ ; dec-cong)
open import Examples.Groups.CCX+HH-3qubit-opus.DecMatrices

open PB _===₁⁺_ using (_≈_)

------------------------------------------------------------------------
-- Completeness

complete₁ : {w v : Word G₁} → ⟦ w ⟧ ≡ ⟦ v ⟧ → w ≈ v
complete₁ = Complete.complete derived

------------------------------------------------------------------------
-- The decoding of a generator has its matrix

private
  not8 : (b : Fin 8) → toℕ b ≡ 8 → ∀ {A : Set} → A
  not8 b h = ⊥-elim (ℕP.<-irrefl Eq.refl (Eq.subst (ℕ._< 8) h (FinP.toℕ<n b)))

  basicX : (a b : Fin 8) .(p : a < b) → toℕ b ≡ suc (toℕ a) → ⟦ dec (X-gen a b p) ⟧ ≡ S1.⟦ [ X-gen a b p ]ʷ ⟧ᵐ
  basicX zero b p h with FinP.toℕ-injective {i = b} {j = # 1} h
  ... | Eq.refl = dX01
  basicX (suc zero) b p h with FinP.toℕ-injective {i = b} {j = # 2} h
  ... | Eq.refl = dX12
  basicX (suc (suc zero)) b p h with FinP.toℕ-injective {i = b} {j = # 3} h
  ... | Eq.refl = dX23
  basicX (suc (suc (suc zero))) b p h with FinP.toℕ-injective {i = b} {j = # 4} h
  ... | Eq.refl = dX34
  basicX (suc (suc (suc (suc zero)))) b p h with FinP.toℕ-injective {i = b} {j = # 5} h
  ... | Eq.refl = dX45
  basicX (suc (suc (suc (suc (suc zero))))) b p h with FinP.toℕ-injective {i = b} {j = # 6} h
  ... | Eq.refl = dX56
  basicX (suc (suc (suc (suc (suc (suc zero)))))) b p h with FinP.toℕ-injective {i = b} {j = # 7} h
  ... | Eq.refl = dX67
  basicX (suc (suc (suc (suc (suc (suc (suc zero))))))) b p h = not8 b h

  basic : (g : Gen 8) → Conj.Basic g → ⟦ dec g ⟧ ≡ S1.⟦ [ g ]ʷ ⟧ᵐ
  basic (M-gen zero) _ = dM0
  basic (M-gen (suc a)) ()
  basic (X-gen a b p) h = basicX a b p h
  basic (K-gen a b c d p q r) (a0 , b1 , c2 , d3)
    with FinP.toℕ-injective {i = a} {j = # 0} a0 | FinP.toℕ-injective {i = b} {j = # 1} b1
       | FinP.toℕ-injective {i = c} {j = # 2} c2 | FinP.toℕ-injective {i = d} {j = # 3} d3
  ... | Eq.refl | Eq.refl | Eq.refl | Eq.refl = dK0123

  dec-sem′ : (k : ℕ) (g : Gen 8) → Conj.size g ℕ.< k → ⟦ dec g ⟧ ≡ S1.⟦ [ g ]ʷ ⟧ᵐ
  dec-sem′ (suc k) g (s≤s lt) with Conj.decompose g
  ... | inj₁ b = basic g b
  ... | inj₂ s = begin
    ⟦ dec g ⟧                                                ≡⟨ sound₁⁺* (dec-cong (Conj.Step.rel s)) ⟩
    ⟦ dec X • (dec g′ • dec X) ⟧                             ≡⟨ ⟦•⟧ (dec X) (dec g′ • dec X) ⟩
    ⟦ dec X ⟧ ·*· ⟦ dec g′ • dec X ⟧                         ≡⟨ Eq.cong (⟦ dec X ⟧ ·*·_) (⟦•⟧ (dec g′) (dec X)) ⟩
    ⟦ dec X ⟧ ·*· (⟦ dec g′ ⟧ ·*· ⟦ dec X ⟧)                 ≡⟨ Eq.cong₂ _·*·_ bX (Eq.cong₂ _·*·_ ih bX) ⟩
    S1.⟦ [ X ]ʷ ⟧ᵐ ·*· (S1.⟦ [ g′ ]ʷ ⟧ᵐ ·*· S1.⟦ [ X ]ʷ ⟧ᵐ)  ≡⟨ Eq.cong (S1.⟦ [ X ]ʷ ⟧ᵐ ·*·_) (Eq.sym (S1.⟦•⟧ᵐ [ g′ ]ʷ [ X ]ʷ)) ⟩
    S1.⟦ [ X ]ʷ ⟧ᵐ ·*· S1.⟦ [ g′ ]ʷ • [ X ]ʷ ⟧ᵐ             ≡⟨ Eq.sym (S1.⟦•⟧ᵐ [ X ]ʷ ([ g′ ]ʷ • [ X ]ʷ)) ⟩
    S1.⟦ [ X ]ʷ • ([ g′ ]ʷ • [ X ]ʷ) ⟧ᵐ                      ≡⟨ Eq.sym (lrs-sound-act (Conj.Step.rel s) S1.𝕀) ⟩
    S1.⟦ [ g ]ʷ ⟧ᵐ                                           ∎
    where
    open Eq.≡-Reasoning
    g′ = Conj.Step.g′ s
    X = X-gen (Conj.Step.x s) (Conj.Step.y s) (Conj.Step.xy s)
    bX = basic X (Conj.Step.adj s)
    ih = dec-sem′ k g′ (ℕP.<-≤-trans (Conj.Step.small s) lt)

dec-sem : (g : Gen 8) → ⟦ dec g ⟧ ≡ S1.⟦ [ g ]ʷ ⟧ᵐ
dec-sem g = dec-sem′ (suc (Conj.size g)) g ℕP.≤-refl

dec-semʷ : (u : Word (Gen 8)) → ⟦ decʷ u ⟧ ≡ S1.⟦ u ⟧ᵐ
dec-semʷ [ g ]ʷ   = dec-sem g
dec-semʷ ε       = Eq.refl
dec-semʷ (u • v) = Eq.trans (⟦•⟧ (decʷ u) (decʷ v))
  (Eq.trans (Eq.cong₂ _·*·_ (dec-semʷ u) (dec-semʷ v)) (Eq.sym (S1.⟦•⟧ᵐ u v)))

------------------------------------------------------------------------
-- The presentation

grouplike₁ : Grouplike _===₁⁺_
grouplike₁ g = [ g ]ʷ , invol₁ g

monoidPresentation : _===₁⁺_ IsMonoidPresentationOf (Group.monoid O8)
monoidPresentation = record
  { ⟦_⟧ = ⟦_⟧ᵒ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = sound₁⁺* }
          ; homo = ⟦•⟧
          }
        ; ε-homo = Eq.refl
        }
      ; injective = complete₁
      }
    ; surjective = λ A → decʷ (LP.word-of A) , λ z≈ →
        Eq.trans (sound₁⁺* z≈) (Eq.trans (dec-semʷ (LP.word-of A)) (LP.word-of-correct A))
    }
  }

-- Theorem 5.2, with r_K.
presentation : _===₁⁺_ IsPresentationOf O8
presentation = monoidPresentation⇒presentation monoidPresentation grouplike₁
