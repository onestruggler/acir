------------------------------------------------------------------------
-- Presentations of groups
--
-- The rule set with -1 presents the Clifford group of the paper:
--
--     (n Exact±,_===_)  IsPresentationOf  Clifford± n,
--
-- Clifford± n = Exact-group n × ℤ/2ℤ (Semantics).  Nothing is proved
-- afresh.  The rule set is the direct product of presentations
-- (n Exact,_===_) ⊕ ⟨ -1 ∣ (-1)² = 1 ⟩, and Presentation.Construct.
-- Properties.DirectProduct turns presentations of the two factors into
-- one of the product: Clifford.Qupit's presentation-exact for the left,
-- Cyclic.Presentation at order 2 for the right.
--
-- The scalars are then separated.  A power of the paper's scalar -ω
-- has a well-defined exponent modulo p AND modulo 2:
--
--     (-ω)ᵃ ≈ (-ω)ᵇ   ⟹   ωᵃ ≈ ωᵇ  (mod ωᵖ = 1)  and  (-1)ᵃ ≈ (-1)ᵇ.
--
-- By soundness the two sides are equal in the product, where (-ω)ᵃ
-- reads componentwise: it splits as (-1)ᵃ • ωᵃ (Translation's -ω^),
-- ωᵃ lands in the left factor as the scalar ωᵃ with no gate
-- (Semantics.Reading.emb-l), and (-1)ᵃ in the right factor, whose
-- interpretation is injective.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
import Algebra.Morphism.Structures as GM
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (tt)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using ([_]ʷ ; _•_ ; _^_ ; wmap)
import Presentation.Base as PB
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)
import Presentation.Construct.Properties.DirectProduct as DP
open import Presentation.Definitions using (_IsPresentationOf_)

import Examples.Groups.Cyclic.Syntactics as Cy
import Examples.Groups.Cyclic.Presentation as CyP

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Translation
  p-3 p-prime g* g-gen as T
open import Examples.Groups.Clifford+MinusOne.Qupit.Semantics
  p-3 p-prime g* g-gen
  using (Exact-group ; Z₂ ; Clifford± ; module Exact-Reading)

import Examples.Groups.Clifford.Qupit.Presentation
  p-3 p-prime g* g-gen as QP

------------------------------------------------------------------------
-- The direct product of the two presentations

private
  module DPP (n : ℕ) =
    DP.Presentation (n N.Exact,_===_) N.MinusOne-relation
      (Exact-group n) Z₂ (QP.presentation-exact n) (CyP.presentation {1})

presentation± : ∀ n → (n N.Exact±,_===_) IsPresentationOf (Clifford± n)
presentation± n = DPP.dpres n

------------------------------------------------------------------------
-- The exponent of a power of -ω, modulo p and modulo 2

scalar-injective :
  ∀ n (a b : ℕ) →
  PB._≈_ (n N.Exact±,_===_) (N.-ω± ^ a) (N.-ω± ^ b) →
  PB._≈_ N.Scalar-relation (N.ω ^ a) (N.ω ^ b) ×
  PB._≈_ N.MinusOne-relation (Cy.T ^ a) (Cy.T ^ b)
scalar-injective n a b h = first , second
  where
  module D  = Group (Clifford± n)
  module G₁ = Group (Exact-group n)
  module G₂ = Group Z₂
  module A  = T.Algebra n
  module R  = Exact-Reading n
  module P  = _IsPresentationOf_ (presentation± n)
  module P₁ = _IsPresentationOf_ (QP.presentation-exact n)
  module P₂ = _IsPresentationOf_ (CyP.presentation {1})

  open GM.GroupMorphisms (Group.rawGroup P.GL.•-ε-group)
                         (Group.rawGroup (Clifford± n))
    using () renaming (module IsGroupIsomorphism to IGI)
  open GM.GroupMorphisms (Group.rawGroup P₂.GL.•-ε-group)
                         (Group.rawGroup Z₂)
    using () renaming (module IsGroupIsomorphism to IGI₂)
  module Iso  = IGI P.iso
  module Iso₂ = IGI₂ P₂.iso

  -- (-ω)ᵏ, split and moved into the two factors' alphabets.
  split : ∀ k → N.-ω± ^ k A.≈ [ Cy.T ^ k ]ᵣ • [ [ N.ω ^ k ]ₗ ]ₗ
  split k = A.trans (A.-ω^ k) (A.cong (A.refl' minus) (A.refl' omega))
    where
    minus : N.-1± ^ k ≡ [ Cy.T ^ k ]ᵣ
    minus = Eq.sym (T.wmap-^ inj₂ Cy.T k)
    omega : N.ω± ^ k ≡ [ [ N.ω ^ k ]ₗ ]ₗ
    omega = Eq.sym (Eq.trans (Eq.cong (wmap inj₁) (T.wmap-^ inj₁ N.ω k))
                             (T.wmap-^ inj₁ [ inj₁ tt ]ʷ k))

  -- ... and read componentwise.
  value : ∀ k → D._≈_ (P.⟦ N.-ω± ^ k ⟧) (P₁.⟦ [ N.ω ^ k ]ₗ ⟧ , P₂.⟦ Cy.T ^ k ⟧)
  value k =
    D.trans (Iso.⟦⟧-cong (split k))
      (D.trans (D.∙-cong (DPP.emb-r n (Cy.T ^ k))
                         (DPP.emb-l n [ N.ω ^ k ]ₗ))
               (G₁.identityˡ _ , G₂.identityʳ _))

  both : D._≈_ (P₁.⟦ [ N.ω ^ a ]ₗ ⟧ , P₂.⟦ Cy.T ^ a ⟧)
               (P₁.⟦ [ N.ω ^ b ]ₗ ⟧ , P₂.⟦ Cy.T ^ b ⟧)
  both = D.trans (D.sym (value a)) (D.trans (Iso.⟦⟧-cong h) (value b))

  -- The left factor: a left-embedded scalar word is that scalar.
  first : PB._≈_ N.Scalar-relation (N.ω ^ a) (N.ω ^ b)
  first =
    proj₁ (R.G-sym (R.emb-l (N.ω ^ a))
             R.⟨G⟩ proj₁ both R.⟨G⟩ R.emb-l (N.ω ^ b))

  -- The right factor: the cyclic interpretation is injective.
  second : PB._≈_ N.MinusOne-relation (Cy.T ^ a) (Cy.T ^ b)
  second = Iso₂.injective (proj₂ both)
