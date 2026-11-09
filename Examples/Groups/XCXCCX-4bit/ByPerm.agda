------------------------------------------------------------------------
-- Presentations of groups
--
-- Presentations of permutation groups from completeness
--
-- Number the 2ᵏ states of k wires (enc, with inverse dec), and read each
-- circuit as a word of Coxeter generators (tr) whose permutation it
-- carries out on the numbered states (at).  Then the circuit's
-- permutation (perm) is a monoid homomorphism by the semantics, it is
-- injective when the theory is complete, and it is onto when every
-- permutation is carried out by some circuit; with every letter
-- invertible (Grouplike), the theory presents the symmetric group
-- (presentation).  When every circuit's word is even (four wires),
-- the same data present the alternating group (Even), given that
-- every even word is carried out.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.XCXCCX-4bit.ByPerm where

open import Algebra.Bundles using (Group)
open import Data.Bool.Base using (Bool ; false)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (Permutation′ ; _⟨$⟩ʳ_)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsMonoidPresentationOf_ ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike)

import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Semantics as SymSem
open import Examples.Groups.Alternating.Parity using (sign ; sign-of ; parity)
import Examples.Groups.Symmetric.Surjectivity as SSurj
open import Examples.Groups.Alternating.Semantics using (Alt ; Alt-group)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; ⟦_⟧ ; _≐_ ; sound)
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox

module ByPerm
  (k N : ℕ)
  (enc : Fin N → Bits k) (dec : Bits k → Fin N)
  (dec-enc : ∀ i → dec (enc i) ≡ i) (enc-dec : ∀ x → enc (dec x) ≡ x)
  (tr : Circuit k → Word (Cox.SG N))
  (at : ∀ u i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ tr u ⟧ ⟨$⟩ʳ i))
  (complete : ∀ {u v : Circuit k} → ⟦ u ⟧ ≐ ⟦ v ⟧ → k ⊢ u ≈ v)
  (grouplike : Grouplike (k VRel,_===_))
  where

  -- The permutation of the numbered states that a circuit carries out.
  perm : Circuit k → Permutation′ N
  perm u = SymI.⟦ tr u ⟧

  perm-at : ∀ u i → perm u ⟨$⟩ʳ i ≡ dec (⟦ u ⟧ (enc i))
  perm-at u i = Eq.trans (Eq.sym (dec-enc _)) (Eq.cong dec (Eq.sym (at u i)))

  perm-cong : ∀ {u v} → k ⊢ u ≈ v → ∀ i → perm u ⟨$⟩ʳ i ≡ perm v ⟨$⟩ʳ i
  perm-cong {u} {v} e i =
    Eq.trans (perm-at u i) (Eq.trans (Eq.cong dec (sound e (enc i))) (Eq.sym (perm-at v i)))

  perm-• : ∀ u v i → perm (u • v) ⟨$⟩ʳ i ≡ perm v ⟨$⟩ʳ (perm u ⟨$⟩ʳ i)
  perm-• u v i =
    Eq.trans (perm-at (u • v) i)
      (Eq.trans (Eq.cong (λ x → dec (⟦ v ⟧ x)) (at u i)) (Eq.sym (perm-at v _)))

  perm-ε : ∀ i → perm ε ⟨$⟩ʳ i ≡ i
  perm-ε i = Eq.trans (perm-at ε i) (dec-enc i)

  perm-inj : ∀ {u v} → (∀ i → perm u ⟨$⟩ʳ i ≡ perm v ⟨$⟩ʳ i) → k ⊢ u ≈ v
  perm-inj {u} {v} e = complete λ x →
    Eq.trans (Eq.cong ⟦ u ⟧ (Eq.sym (enc-dec x)))
      (Eq.trans (at u (dec x))
        (Eq.trans (Eq.cong enc (e (dec x)))
          (Eq.trans (Eq.sym (at v (dec x))) (Eq.cong ⟦ v ⟧ (enc-dec x)))))

  -- A circuit that carries out π has π as its permutation.
  perm-of : ∀ u (π : Permutation′ N) → (∀ i → ⟦ u ⟧ (enc i) ≡ enc (π ⟨$⟩ʳ i)) →
            ∀ i → perm u ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
  perm-of u π h i = Eq.trans (perm-at u i) (Eq.trans (Eq.cong dec (h i)) (dec-enc _))

  ----------------------------------------------------------------------
  -- The symmetric group

  module Full
    (realise : (w : Word (Cox.SG N)) → Σ (Circuit k) (λ u → ∀ i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i)))
    where

    -- Every permutation: the circuit of a word that denotes it.
    onto : (π : Permutation′ N) → Σ (Circuit k) (λ u → ∀ i → perm u ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i)
    onto π = proj₁ r , λ i → Eq.trans (perm-of (proj₁ r) π (λ j → Eq.trans (proj₂ r j) (Eq.cong enc (hw j))) i) Eq.refl
      where
      w = proj₁ (SSurj.go N π)
      hw = proj₂ (SSurj.go N π)
      r = realise w

    monoid-presentation : (k VRel,_===_) IsMonoidPresentationOf (Group.monoid (SymSem.Permutation′-group N))
    monoid-presentation = record
      { ⟦_⟧ = perm
      ; iso = record
        { isMonoidMonomorphism = record
          { isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = perm-cong }
              ; homo              = perm-•
              }
            ; ε-homo = perm-ε
            }
          ; injective = perm-inj
          }
        ; surjective = λ π →
            proj₁ (onto π) , λ {z} z≈ i → Eq.trans (perm-cong z≈ i) (proj₂ (onto π) i)
        }
      }

    presentation : (k VRel,_===_) IsPresentationOf (SymSem.Permutation′-group N)
    presentation = monoidPresentation⇒presentation monoid-presentation grouplike

  ----------------------------------------------------------------------
  -- The alternating group

  -- The sign is reasoned about here, at a variable N: at a numeral,
  -- comparing two spellings of a sign makes Agda evaluate Symmetric's
  -- word for the permutation, which for S₁₆ exhausts the heap.
  module Even
    (even : ∀ u → parity (tr u) ≡ false)
    (realise : (w : Word (Cox.SG N)) → parity w ≡ false →
               Σ (Circuit k) (λ u → ∀ i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i)))
    where

    even′ : ∀ u → sign (perm u) ≡ false
    even′ u = Eq.trans (sign-of {N} (tr u) (perm u) (λ _ → Eq.refl)) (even u)

    -- The even permutation of a circuit.
    permᴬ : Circuit k → Alt N
    permᴬ u = record { perm = perm u ; even = even′ u }

    -- Every even permutation: the circuit of an even word that denotes it.
    onto : (π : Permutation′ N) → sign π ≡ false → Σ (Circuit k) (λ u → ∀ i → perm u ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i)
    onto π s = proj₁ r , λ i → perm-of (proj₁ r) π (λ j → Eq.trans (proj₂ r j) (Eq.cong enc (hw j))) i
      where
      w = proj₁ (SSurj.go N π)
      hw = proj₂ (SSurj.go N π)
      r = realise w (Eq.trans (Eq.sym (sign-of {N} w π hw)) s)

    monoid-presentation : (k VRel,_===_) IsMonoidPresentationOf (Group.monoid (Alt-group N))
    monoid-presentation = record
      { ⟦_⟧ = permᴬ
      ; iso = record
        { isMonoidMonomorphism = record
          { isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = perm-cong }
              ; homo              = perm-•
              }
            ; ε-homo = perm-ε
            }
          ; injective = perm-inj
          }
        ; surjective = λ a →
            let r = onto (Alt.perm a) (Alt.even a) in
            proj₁ r , λ {z} z≈ i → Eq.trans (perm-cong z≈ i) (proj₂ r i)
        }
      }

    presentation : (k VRel,_===_) IsPresentationOf (Alt-group N)
    presentation = monoidPresentation⇒presentation monoid-presentation grouplike
