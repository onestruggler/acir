------------------------------------------------------------------------
-- Presentations of groups
--
-- Group homomorphism from the free-group presentation
-- (Word (Gen n) / ≈) to the symplectic group Sp(2n, ℤ/pℤ), via the
-- symplectic (Pauli-action) semantics.
--
-- Adapted from Examples.Groups.Symmetric.Tight.Presentation.  The
-- symmetric development threads the interpretation through the coset
-- section explicitly; here the interpretation is the linear symplectic
-- action ⟦_⟧ : Circuit n → Symplectic n, the normal form is the box
-- normal form of Normalization.Section, and injectivity of the section
-- (the completeness crux) is Normalization.NF-Inj.⟦[]⟧-injective.
--
-- SOUNDNESS AND COMPLETENESS ARE NOW POSTULATE-FREE.  The completeness
-- crux is Normalization.LMHeadInj.lemma-lm-head-inj-proved, and the
-- normalizer is no longer postulated: Normalization.nfp'-sec is the
-- coset tower's own normal form, transported onto Section's NF, the
-- tower having been completed by the width induction (see
-- Normalization.agda, which is --safe and hole-free).  So
-- `subpresentation` below rests on nothing.
--
-- `presentation` additionally needs SURJECTIVITY, and that is still
-- open: Surjectivity.agda postulates Theorem-LM (every symplectic
-- transformation is realised by some circuit).  That is why this
-- module cannot yet carry --safe — the obligation is a different one
-- from anything on the normalization route.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Presentation (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Algebra.Bundles using (Group)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function.Definitions using (Surjective)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Presentation.Definitions
open import Normalization.StarPresentation
import Normalization.NormalForm.Setoid as SNF

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen ; _QRel,_===_)
open Symplectic-GroupLike using (grouplike)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (_≈ˢ_ ; Sp-group)
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ)

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (NF ; [_])
-- The normal form is now the coset tower's own, transported onto
-- Section's NF: no normalizer is postulated any more.
open import Examples.Groups.Symplectic.Normalization p-2 p-prime
  using (nfp'-sec-agree) renaming (nfp'-sec to nfp'-t)
open import Examples.Groups.Symplectic.Normalization.Uniqueness p-2 p-prime
  using (⟦[]⟧-injective) renaming (sound to soundQ)

open SNF using (UniqueNormalForm)

------------------------------------------------------------------------
-- Soundness and surjectivity (both proven)
--
-- sound-ax : the raw relations of the presentation preserve the
-- symplectic action ⟦_⟧.  Proved in Transport, by carrying the extended
-- gate set's soundness back along the group isomorphism f'*.
--
-- surj-nf : every symplectic transformation is the action of some
-- circuit — surjectivity of ⟦_⟧ onto Sp-group.  Proved directly in
-- Surjectivity via the box normal-form inversion engine `lemma-invnf`
-- (the whole reduction is verified; its single remaining gate-specific
-- input is the single-level `Theorem-LM`, postulated there).

open import Examples.Groups.Symplectic.Transport p-2 p-prime using (sound-ax)
open import Examples.Groups.Symplectic.Surjectivity p-2 p-prime using (surj-nf)

------------------------------------------------------------------------
-- The presentation, assembled level by level
--
-- Everything below folds through the StarPresentation.GroupSem builder,
-- whose interpretation GS.⟦_⟧ is the free-monoid extension of ⟦_⟧ᵍ.  It
-- agrees pointwise with the directly-recursive ⟦_⟧ of Semantics (agree),
-- which lets soundness, uniqueness and surjectivity — all stated for
-- ⟦_⟧ — be transported to GS.⟦_⟧.

private
  module Build (n : ℕ) where

    open PB (n QRel,_===_) using (_≈_)

    module GS = GroupSem (n QRel,_===_) (Eq.setoid (NF n)) (Sp-group n) (⟦_⟧ᵍ {n})

    -- The extension GS.⟦_⟧ agrees with the recursive ⟦_⟧ on the nose: on
    -- generators and ε they are definitionally equal, and _•_ is sent to
    -- ∘ˢ by both, so composition threads through.
    agree : ∀ (w : Circuit n) → ⟦ w ⟧ ≈ˢ GS.⟦ w ⟧
    agree [ g ]ʷ  p = Eq.refl
    agree ε       p = Eq.refl
    agree (w • v) p =
      Eq.trans (Eq.cong (ap ⟦ w ⟧) (agree v p)) (agree w (ap GS.⟦ v ⟧ p))

    -- Soundness for GS.⟦_⟧ = soundness for ⟦_⟧ conjugated by agree.
    soundE : ∀ {w v : Circuit n} → n QRel, w === v → GS.⟦ w ⟧ ≈ˢ GS.⟦ v ⟧
    soundE {w} {v} r p =
      Eq.trans (Eq.sym (agree w p)) (Eq.trans (sound-ax r p) (agree v p))

    -- Uniqueness for GS.⟦_⟧ = uniqueness for ⟦_⟧ conjugated by agree.
    unfp : UniqueNormalForm (n QRel,_===_) (Eq.setoid (NF n))
                            (Group.setoid (Sp-group n)) GS.⟦_⟧ (nfp'-t n)
    -- The section is now the tower's, which is [_] only up to the
    -- congruence, so the chain is bridged through that agreement.
    bridge : ∀ (u : NF n) p →
             ap GS.⟦ SNF.NormalForm.inv-nf (nfp'-t n) u ⟧ p ≡
             ap GS.⟦ [ u ] ⟧ p
    bridge u p =
      Eq.trans (Eq.sym (agree (SNF.NormalForm.inv-nf (nfp'-t n) u) p))
        (Eq.trans (soundQ (nfp'-sec-agree n u) p) (agree [ u ] p))

    unfp = record
      { unique = λ {u} {v} eq →
          ⟦[]⟧-injective n
            (λ p → Eq.trans (agree [ u ] p)
                   (Eq.trans (Eq.sym (bridge u p))
                   (Eq.trans (eq p)
                   (Eq.trans (bridge v p) (Eq.sym (agree [ v ] p)))))) }

    module GSP = GS.GetSubPresentation soundE grouplike (nfp'-t n) unfp

    subpres : (n QRel,_===_) IsSubPresentationOf (Sp-group n)
    subpres = GSP.groupSubPres

    -- Congruence of GS.⟦_⟧ over the presentation _≈_, by induction on the
    -- derivation.  The monoid laws hold on the nose (∘ˢ is strictly
    -- associative and unital), and axioms are handled by soundE.
    ⟦⟧-cong : ∀ {w v : Circuit n} → w ≈ v → GS.⟦ w ⟧ ≈ˢ GS.⟦ v ⟧
    ⟦⟧-cong PB.refl        p = Eq.refl
    ⟦⟧-cong (PB.sym e)     p = Eq.sym (⟦⟧-cong e p)
    ⟦⟧-cong (PB.trans e f) p = Eq.trans (⟦⟧-cong e p) (⟦⟧-cong f p)
    ⟦⟧-cong (PB.cong {w} {_} {_} {v'} e f) p =
      Eq.trans (Eq.cong (ap GS.⟦ w ⟧) (⟦⟧-cong f p))
               (⟦⟧-cong e (ap GS.⟦ v' ⟧ p))
    ⟦⟧-cong PB.assoc       p = Eq.refl
    ⟦⟧-cong PB.left-unit   p = Eq.refl
    ⟦⟧-cong PB.right-unit  p = Eq.refl
    ⟦⟧-cong (PB.axiom x)   p = soundE x p

    -- Surjectivity of GS.⟦_⟧ onto Sp-group, transported from surj-nf.
    claim : Surjective _≈_ (Group._≈_ (Sp-group n)) GS.⟦_⟧
    claim S = w , λ {z} z≈w p →
      Eq.trans (⟦⟧-cong z≈w p)
        (Eq.trans (Eq.sym (agree w p)) (w≈S p))
      where
      w   = proj₁ (surj-nf S)
      w≈S = proj₂ (surj-nf S)

------------------------------------------------------------------------
-- The symplectic presentation

subpresentation : ∀ {n} → (n QRel,_===_) IsSubPresentationOf (Sp-group n)
subpresentation {n} = Build.subpres n

presentation : ∀ {n} → (n QRel,_===_) IsPresentationOf (Sp-group n)
presentation {n} = isPresentationOf (Build.subpres n) (Build.claim n)
