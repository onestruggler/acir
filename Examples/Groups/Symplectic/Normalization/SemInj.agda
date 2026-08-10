------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization.CosetNF2 instantiated at the Symplectic semantics.
--
-- The tower in Normalization.agda extends the presentation at width n to
-- width ₁₊ n along the wire embedding f = [_]ʷ ∘ _↥.  Its hard
-- hypothesis is h-wd-ax (= srel-wd), needed only to obtain
--
--   fʷ-injective : (f ʷ) w ≈₂ (f ʷ) v → w ≈₁ v
--
-- which, for this f, IS faithfulness of the wire lift:
--
--   w ↑ ≈ v ↑  (at width ₁₊ n)   ⟹   w ≈ v  (at width n)
--
-- — exactly the `↑-inj` that RhoExAbstract.Strategy-B needs, and whose
-- only proof in the repo goes through Reidemeister–Schreier and is
-- therefore circular (RhoExAbstract.Converse machine-checks that loop).
--
-- CosetNF2.SemInjective supplies it from a model instead.  Here the
-- model is the symplectic representation, and the model obligations
-- discharge as follows:
--
--   * the monoid laws are FREE — ⟦ w • v ⟧ is *definitionally*
--     ⟦ w ⟧ ∘ˢ ⟦ v ⟧ and ⟦ ε ⟧ is εˢ (Semantics.agda:331-334), so the
--     four structural fields are just Sp-isGroup's ∙-cong/assoc/identity;
--   * soundness of the axioms is SoundnessDirect.sound-ax, already proved,
--     postulate-free and --safe.
--
-- What is left is `reflect`, and it factors into two independent
-- statements, both recorded below with their exact types:
--
--   sem-↑-inj : ⟦ w ↑ ⟧ ≈ˢ ⟦ v ↑ ⟧ → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
--       injectivity of the semantic wire embedding.  Pure linear algebra
--       over ℤ/p: ⟦ w ↑ ⟧ is the block-diagonal extension of ⟦ w ⟧, and
--       block-diagonal extension is injective.  PROVED below (lift-act
--       + sem-↑-inj): the lifted action is head-preserving cons, so the
--       tail component recovers the unlifted action.
--
--   complete : ⟦ w ⟧ ≈ˢ ⟦ v ⟧ → w ≈ v   (at width n)
--       faithfulness of the representation at width n — completeness.
--       This is what Uniqueness.agda:73 and NF-Inj.agda:111 currently
--       postulate.
--
-- Neither mentions the coset action, so neither can loop back through
-- Reidemeister–Schreier.  That is the whole point.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.SemInj
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Algebra.Structures using (IsGroup)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_)
open import Data.Vec.Properties using (∷-injectiveʳ)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Gen ; Circuit ; _↥ ; _↑ ; _QRel,_===_ ; lemma-[⇑]=[⇑]')

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (_≈ˢ_ ; _∘ˢ_ ; εˢ ; Sp-isGroup)
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1)

open import Examples.Groups.Symplectic.SoundnessDirect p-2 p-prime
  using (sound-ax)

import Normalization.CosetNF2 as CNF2

------------------------------------------------------------------------
-- The semantic setoid.

Sp-setoid : ℕ → Setoid 0ℓ 0ℓ
Sp-setoid n = record
  { Carrier       = Sem.Symplectic n
  ; _≈_           = _≈ˢ_
  ; isEquivalence = IsGroup.isEquivalence (Sp-isGroup n)
  }

------------------------------------------------------------------------
-- The wire embedding, in the form CosetNF2 expects.

fᵤ : ∀ {n} → Gen n → Word (Gen (₁₊ n))
fᵤ g = [ g ↥ ]ʷ

------------------------------------------------------------------------
-- The model obligations, discharged.

module Model (n : ℕ) where

  private
    G = Sp-isGroup (₁₊ n)

  -- ⟦ w • v ⟧ ≡ ⟦ w ⟧ ∘ˢ ⟦ v ⟧ definitionally, so this is ∙-cong.
  -- Stated with explicit words: the pointwise shape of _≈ˢ_ leaves
  -- implicits unsolvable at the instantiation site.
  ⟦⟧-congᵉ : ∀ (w w' v v' : Circuit (₁₊ n)) →
    ⟦ w ⟧ ≈ˢ ⟦ w' ⟧ → ⟦ v ⟧ ≈ˢ ⟦ v' ⟧ → ⟦ w • v ⟧ ≈ˢ ⟦ w' • v' ⟧
  ⟦⟧-congᵉ w w' v v' e₁ e₂ = IsGroup.∙-cong G {⟦ w ⟧} {⟦ w' ⟧} {⟦ v ⟧} {⟦ v' ⟧} e₁ e₂

  ⟦⟧-assocᵉ : ∀ (w v u : Circuit (₁₊ n)) →
    ⟦ (w • v) • u ⟧ ≈ˢ ⟦ w • (v • u) ⟧
  ⟦⟧-assocᵉ w v u = IsGroup.assoc G ⟦ w ⟧ ⟦ v ⟧ ⟦ u ⟧

  ⟦⟧-lunitᵉ : ∀ (w : Circuit (₁₊ n)) → ⟦ ε • w ⟧ ≈ˢ ⟦ w ⟧
  ⟦⟧-lunitᵉ w = IsGroup.identityˡ G ⟦ w ⟧

  ⟦⟧-runitᵉ : ∀ (w : Circuit (₁₊ n)) → ⟦ w • ε ⟧ ≈ˢ ⟦ w ⟧
  ⟦⟧-runitᵉ w = IsGroup.identityʳ G ⟦ w ⟧

  -- Soundness of the axioms: already proved, postulate-free.
  ⟦⟧-axᵉ : ∀ (u t : Circuit (₁₊ n)) →
    (₁₊ n) QRel, u === t → ⟦ u ⟧ ≈ˢ ⟦ t ⟧
  ⟦⟧-axᵉ u t = sound-ax

------------------------------------------------------------------------
-- The two remaining obligations, named.
--
-- Recorded as Set-valued statements, NOT postulated and NOT inhabited.

-- Injectivity of the semantic wire embedding.
--
-- Phrased with (fᵤ ʷ) rather than _↑ so that it plugs into CosetNF2
-- definitionally: (fᵤ ʷ) w is wconcat (wmap fᵤ w) whereas w ↑ is
-- wmap (_↥ᵏ 1) w, and the two agree only propositionally
-- (Syntactics.lemma-[⇑]=[⇑]').  Semantically they are the same map, so
-- this is the same obligation with no bridge lemma in the way.
Sem-↑-Inj : ℕ → Set
Sem-↑-Inj n = ∀ (w v : Circuit n) →
  ⟦ (fᵤ ʷ) w ⟧ ≈ˢ ⟦ (fᵤ ʷ) v ⟧ → ⟦ w ⟧ ≈ˢ ⟦ v ⟧

-- Faithfulness of the representation at width n (completeness).
Faithful : ℕ → Set
Faithful n = ∀ (w v : Circuit n) →
  ⟦ w ⟧ ≈ˢ ⟦ v ⟧ → PB._≈_ (n QRel,_===_) w v

------------------------------------------------------------------------
-- Sem-↑-Inj HOLDS.  The lifted generator action is head-preserving
-- cons (Semantics.actg (g ↥) (x ∷ ps) = x ∷ actg g ps), so a lifted
-- word acts as id ⊕ ⟦ w ⟧ on the phase space, and injectivity reads
-- off the tail component.  This discharges the first of the two
-- CosetNF2 obligations; the residual halves of srel-wd now hinge ONLY
-- on Faithful (completeness one width down).

private
  lift-act : ∀ {n} (w : Circuit n) (x : Pauli1) (ps : Pauli n) →
    ap ⟦ (fᵤ ʷ) w ⟧ (x ∷ ps) ≡ x ∷ ap ⟦ w ⟧ ps
  lift-act [ g ]ʷ  x ps = Eq.refl
  lift-act ε       x ps = Eq.refl
  lift-act (w • v) x ps =
    Eq.trans (Eq.cong (ap ⟦ (fᵤ ʷ) w ⟧) (lift-act v x ps))
             (lift-act w x (ap ⟦ v ⟧ ps))

sem-↑-inj : ∀ (n : ℕ) → Sem-↑-Inj n
sem-↑-inj n w v hyp ps =
  ∷-injectiveʳ
    (Eq.trans (Eq.sym (lift-act w (₀ , ₀) ps))
      (Eq.trans (hyp ((₀ , ₀) ∷ ps)) (lift-act v (₀ , ₀) ps)))

------------------------------------------------------------------------
-- The payoff.
--
-- Given the two obligations above, fʷ-injective — i.e. ↑-faithfulness —
-- follows, with no appeal to the coset action and hence no circularity.

module Injectivity (n : ℕ)
  (sem-↑-inj : Sem-↑-Inj n)
  (faithful  : Faithful n)
  where

  open Model n

  -- `reflect` in the sense of CosetNF2: equal interpretations after
  -- embedding imply relatedness in the smaller presentation.
  reflect : ∀ (w v : Circuit n) →
    ⟦ (fᵤ ʷ) w ⟧ ≈ˢ ⟦ (fᵤ ʷ) v ⟧ → PB._≈_ (n QRel,_===_) w v
  reflect w v eq = faithful w v (sem-↑-inj w v eq)

  module SI = CNF2.SemInjective
    (n QRel,_===_) ((₁₊ n) QRel,_===_) fᵤ (Sp-setoid (₁₊ n)) ⟦_⟧

  -- ↑-faithfulness, the ingredient RhoExAbstract.Strategy-B needs.
  ↑-inj : ∀ (w v : Circuit n) →
    PB._≈_ ((₁₊ n) QRel,_===_) ((fᵤ ʷ) w) ((fᵤ ʷ) v) →
    PB._≈_ (n QRel,_===_) w v
  ↑-inj = SI.fʷ-injective
            (λ {w} {w'} {v} {v'} → ⟦⟧-congᵉ w w' v v')
            (λ {w} {v} {u} → ⟦⟧-assocᵉ w v u)
            (λ {w} → ⟦⟧-lunitᵉ w)
            (λ {w} → ⟦⟧-runitᵉ w)
            (λ {u} {t} → ⟦⟧-axᵉ u t)
            reflect

  -- The same, in the `w ↑` form that RhoExAbstract.Strategy-B consumes.
  -- (fᵤ ʷ) is wconcat ∘ wmap, _↑ is wmap; Syntactics.lemma-[⇑]=[⇑]'
  -- bridges them.
  private
    module P₂ = PB ((₁₊ n) QRel,_===_)

  ↑-inj-↑ : ∀ (w v : Circuit n) →
    P₂._≈_ (w ↑) (v ↑) → PB._≈_ (n QRel,_===_) w v
  ↑-inj-↑ w v eq = ↑-inj w v
    (P₂.trans (P₂.refl' (lemma-[⇑]=[⇑]' w))
      (P₂.trans eq (P₂.refl' (Eq.sym (lemma-[⇑]=[⇑]' v)))))

------------------------------------------------------------------------
-- With sem-↑-inj proved above, ↑-faithfulness needs only Faithful n.

module Injectivity! (n : ℕ) (faithful : Faithful n) =
  Injectivity n (sem-↑-inj n) faithful
