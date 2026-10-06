------------------------------------------------------------------------
-- Presentations of groups
--
-- The main theorem of Bian and Selinger, "Generators and relations for
-- 3-qubit Clifford+CS operators" (arXiv:2306.08530): the 3-qubit
-- Clifford+CS group is presented by the generators iI, S₀, S₁, S₂,
-- K₀, K₁, K₂, CS₀₁, CS₁₂ and the relations of Figure 2 (Theorem,
-- module CliffordCS).
--
-- A Clifford+CS word denotes a unitary 8 × 8 matrix over ℤ[1/2,i]
-- through the translation f into the two-level generators (Theorem,
-- module TwoLevel), with indices in Fin 8 (TwoLevel-Bridge), and their
-- matrices (Clifford+CS-TwoLevel).  Then
--
-- * sound: related words have the same matrix, by Proof.soundness and
--   the soundness of the two-level relations;
-- * complete: words with the same matrix are related, by the
--   completeness of the two-level relations (Clifford+CS-TwoLevel,
--   proved there from the exact synthesis algorithm) and
--   Proof.completeness (the Reidemeister–Schreier theorem, Steps 1–8);
--
-- so the relations present the subgroup of U₈(ℤ[1/2,i]) the generators
-- generate: the 3-qubit Clifford+CS group.  Nothing here is about its
-- index: the Reidemeister–Schreier theorem needs only the hypotheses
-- (a) and (b) on Step3's coset table, which do not make its two cosets
-- the actual ones.  That the index is 2 is the paper's, from the
-- determinant characterisation of Amy, Glaudell and Ross.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-3qubit.Presentation where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product.Base using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Word.Base
import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)
open import Presentation.Tactics.Judgement using (_⊢_ ; _===_)
open import Presentation.Tactics.Equality using (auto)
open import Presentation.Tactics.Words using (module Associative)
open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module TwoLevel ; module CliffordCS ; f)
open import Examples.Groups.Clifford+CS-3qubit.Proof using (soundness ; completeness)
open import Examples.Groups.Clifford+CS-3qubit.TwoLevel-Bridge using (to ; from ; to-cong ; from-cong ; from-to)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (UMat ; U ; ⟦_⟧ᵐ ; ⟦•⟧ᵐ)
import Examples.Groups.Clifford+CS-TwoLevel.Presentation {8} as TLP
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {8} using (sound-act)
open import Examples.Groups.Clifford+CS-TwoLevel.MainLemma {8} using (relations-complete)

open CliffordCS
open Associative using (general-assoc)

private
  module P₈ = PB (TL._===_ {8})
  open PB Rel using (refl ; sym ; trans ; cong ; assoc ; axiom)

  -- g* ∘ f* = (g* ∘ f)*.
  ʷ-ʷ : ∀ {X Y Z : Set} (f : X → Word Y) (g : Y → Word Z) (w : Word X) →
        (g ʷ) ((f ʷ) w) ≡ ((λ y → (g ʷ) (f y)) ʷ) w
  ʷ-ʷ f g [ x ]ʷ = Eq.refl
  ʷ-ʷ f g ε = Eq.refl
  ʷ-ʷ f g (w • w′) = Eq.cong₂ _•_ (ʷ-ʷ f g w) (ʷ-ʷ f g w′)

------------------------------------------------------------------------
-- The relations are group-like

-- (K • iI) • K = K • K • iI = iI⁴ = ε, when iI commutes with K and
-- K² = iI³.
private
  K⁻¹K : ∀ {K} → Rel (iI • K) (K • iI) → Rel (K • K) (iI • iI • iI) → Rel ⊢ (K • iI) • K === ε
  K⁻¹K c o =
    trans assoc (trans (cong refl (axiom c)) (trans (sym assoc)
      (trans (cong (axiom o) refl) (trans (general-assoc auto) (axiom ax-iI-iI-iI-iI=ε)))))

group-like : Grouplike Rel
group-like S0-gen = S0 • S0 • S0 , trans (general-assoc auto) (axiom ax-S0-S0-S0-S0=ε)
group-like S1-gen = S1 • S1 • S1 , trans (general-assoc auto) (axiom ax-S1-S1-S1-S1=ε)
group-like S2-gen = S2 • S2 • S2 , trans (general-assoc auto) (axiom ax-S2-S2-S2-S2=ε)
group-like CS01-gen = CS01 • CS01 • CS01 , trans (general-assoc auto) (axiom ax-CS01-CS01-CS01-CS01=ε)
group-like CS12-gen = CS12 • CS12 • CS12 , trans (general-assoc auto) (axiom ax-CS12-CS12-CS12-CS12=ε)
group-like iI-gen = iI • iI • iI , trans (general-assoc auto) (axiom ax-iI-iI-iI-iI=ε)
group-like K0-gen = K0 • iI , K⁻¹K ax-iI-K0=K0-iI ax-K0-K0=iI-iI-iI
group-like K1-gen = K1 • iI , K⁻¹K ax-iI-K1=K1-iI ax-K1-K1=iI-iI-iI
group-like K2-gen = K2 • iI , K⁻¹K ax-iI-K2=K2-iI ax-K2-K2=iI-iI-iI

------------------------------------------------------------------------
-- The semantics

-- A Clifford+CS generator as a word in the two-level generators.
tl : Gen → Word (TL.Gen 8)
tl x = (to ʷ) (f x)

⟦_⟧ : Word Gen → UMat 8
⟦ w ⟧ = TLP.⟦ (tl ʷ) w ⟧ᵘ

------------------------------------------------------------------------
-- Soundness and completeness

sound : ∀ {w v} → Rel ⊢ w === v → proj₁ ⟦ w ⟧ ≡ proj₁ ⟦ v ⟧
sound {w} {v} hyp =
  Eq.subst₂ (λ a b → ⟦ a ⟧ᵐ ≡ ⟦ b ⟧ᵐ) (ʷ-ʷ f to w) (ʷ-ʷ f to v)
    (sound-act (to-cong (soundness hyp)) _)

complete : ∀ {w v} → proj₁ ⟦ w ⟧ ≡ proj₁ ⟦ v ⟧ → Rel ⊢ w === v
complete {w} {v} eq =
  completeness (Eq.subst₂ (λ a b → TwoLevel.Rel ⊢ a === b) (back w) (back v) (from-cong tl≈))
  where
  tl≈ : (tl ʷ) w P₈.≈ (tl ʷ) v
  tl≈ = relations-complete eq
  back : ∀ u → (from ʷ) ((tl ʷ) u) ≡ (f ʷ) u
  back u = Eq.trans (Eq.cong (from ʷ) (Eq.sym (ʷ-ʷ f to u))) (from-to ((f ʷ) u))

------------------------------------------------------------------------
-- The presentation

-- The relations present the subgroup of U₈(ℤ[1/2,i]) generated by the
-- Clifford+CS gates: ⟦_⟧ is a group monomorphism.
presentation : Rel IsSubPresentationOf U 8
presentation = record
  { gl = group-like
  ; ⟦_⟧ = ⟦_⟧
  ; mono = record
    { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (U 8) isMonoidHomomorphism
    ; injective = complete
    }
  }
  where
  module GL = Group-Lemmas Rel group-like
  open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (U 8))
  isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = sound }
      ; homo = λ w v → ⟦•⟧ᵐ ((tl ʷ) w) ((tl ʷ) v)
      }
    ; ε-homo = Eq.refl
    }
