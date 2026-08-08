------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset half of srel-wd, for every axiom at once, by semantics
--
-- srel-wd asks, for an axiom u === t, that the threaded coset action
-- agrees: (ract ᵗ) c u ≋ (ract ᵗ) c t, which is an ≈ on the residual
-- word and an ≡ on the coset reached.  The ≡ half has been ground out
-- one axiom at a time.  It need not be: it follows for EVERY pair of
-- congruent words at once, from facts that are already proved.
--
-- The argument.  Threading a word past a coset satisfies the section
-- law [ c ]ᶜ • w ≈ w′ ↑ • [ c′ ]ᶜ (ract-sound-word below, the word
-- level of Normalization.ract-sound).  Applying the semantics to it,
-- for congruent u and t,
--
--   ⟦ u′ ↑ ⟧ ∙ ⟦ [ cᵤ ]ᶜ ⟧  ≈  ⟦ [ c ]ᶜ ⟧ ∙ ⟦ u ⟧
--                           ≈  ⟦ [ c ]ᶜ ⟧ ∙ ⟦ t ⟧
--                           ≈  ⟦ t′ ↑ ⟧ ∙ ⟦ [ cₜ ]ᶜ ⟧ .
--
-- Now act on a state.  The residuals are LIFTED circuits, and a lifted
-- circuit cannot disturb the head of a state, so the heads of the two
-- sides are the heads of ⟦ [ cᵤ ]ᶜ ⟧ and ⟦ [ cₜ ]ᶜ ⟧ acting alone.
-- They agree on every state, so lemma-lm-head-inj gives cᵤ ≡ cₜ.
--
-- Nothing here is circular: ract-sound, soundness, head-fix and
-- lemma-lm-head-inj are all proved outright, and no normalizer and no
-- Faithful is involved.  The RESIDUAL half is a different matter — it
-- needs ↑-injectivity, hence completeness one width down, which is
-- what the width induction is for.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSem
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (_∷_ ; head ; tail)
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise-≡⇒≡)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; inspect) renaming ([_] to [_]ₑ)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (_≈ˢ_ ; module Interpretation) renaming (Symplectic to Sym)
open Sym using (ap)
open Interpretation using (⟦_⟧)
  using ([_]ᵐˡ)
-- ract / ract-sound / [_]ᶜ are taken from PushML rather than from
-- Normalization, which aliases them: Normalization still has open
-- holes, so a --safe module cannot import it.
open import Examples.Groups.Symplectic.Normalization.Pushing.PushML
  p-2 p-prime using (ract ; ract-sound ; [_]ᶜ)
open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime
  using (ML)
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli)
open import Examples.Groups.Symplectic.Normalization.NF-Inj p-2 p-prime
  using (lemma-lm-head-inj)
open import Examples.Groups.Symplectic.Normalization.Uniqueness
  p-2 p-prime using (Ob ; head-fix ; sound)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (_≋_)
open import
  Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction
  p-2 p-prime using (act ; resid ; step)
import Examples.Groups.Symplectic.Normalization.Pushing.RhoExAbstract
  p-2 p-prime as RhoEx

private variable n : ℕ

open VecEq Ob using () renaming (_≋_ to _≋ᵥ_)


------------------------------------------------------------------------
-- The section law, at the level of words

-- Normalization.ract-sound says one letter slides past a coset,
-- emitting a lifted residual.  A whole word does too, the residuals
-- concatenating, since _↑_ distributes over _•_.

ract-sound-word : (c : ML (₁₊ n)) (w : Circuit (₁₊ n)) →
  let open PB ((₁₊ n) QRel,_===_)
      (w′ , c′) = (ract {n} ᵗ) c w
  in [ c ]ᶜ • w ≈ w′ ↑ • [ c′ ]ᶜ
ract-sound-word c [ g ]ʷ = ract-sound c g
ract-sound-word {n} c ε =
  PB.trans PB.right-unit (PB.sym PB.left-unit)
ract-sound-word {n} c (w • v)
  with (ract {n} ᵗ) c w | inspect ((ract {n} ᵗ) c) w
... | (w′ , c₁) | [ ew ]ₑ
  with (ract {n} ᵗ) c₁ v | inspect ((ract {n} ᵗ) c₁) v
... | (v′ , c₂) | [ ev ]ₑ =
  PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong step-w PB.refl)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl step-v) (PB.sym PB.assoc))))
  where
  -- The recursive calls, with the threaded pair substituted in.
  step-w : PB._≈_ ((₁₊ n) QRel,_===_) ([ c ]ᶜ • w) (w′ ↑ • [ c₁ ]ᶜ)
  step-w = Eq.subst
    (λ z → PB._≈_ ((₁₊ n) QRel,_===_) ([ c ]ᶜ • w)
                  (z .proj₁ ↑ • [ z .proj₂ ]ᶜ))
    ew (ract-sound-word c w)

  step-v : PB._≈_ ((₁₊ n) QRel,_===_) ([ c₁ ]ᶜ • v) (v′ ↑ • [ c₂ ]ᶜ)
  step-v = Eq.subst
    (λ z → PB._≈_ ((₁₊ n) QRel,_===_) ([ c₁ ]ᶜ • v)
                  (z .proj₁ ↑ • [ z .proj₂ ]ᶜ))
    ev (ract-sound-word c₁ v)


------------------------------------------------------------------------
-- The coset half, for every congruent pair

-- Congruent words drive a coset to the same place.  In particular
-- this covers every axiom, so it discharges the ≡ component of every
-- srel-wd obligation, at every width, in one go.

coset-wd : (c : ML (₁₊ n)) {u t : Circuit (₁₊ n)} →
           PB._≈_ ((₁₊ n) QRel,_===_) u t →
           ((ract {n} ᵗ) c u) .proj₂ ≡ ((ract {n} ᵗ) c t) .proj₂
private
  vec-eta : ∀ {m} (xs : Pauli (₁₊ m)) → xs ≡ head xs ∷ tail xs
  vec-eta (x ∷ xs) = Eq.refl

  -- A lifted residual cannot disturb the head of a state, so it can be
  -- dropped from a head computation.
  peel : ∀ {n} (w : Circuit n) (c′ : ML (₁₊ n)) (qs : Pauli (₁₊ n)) →
         head (ap ⟦ w ↑ • [ c′ ]ᶜ ⟧ qs) ≡ head (ap ⟦ [ c′ ]ᶜ ⟧ qs)
  peel w c′ qs =
    Eq.trans (Eq.cong (λ v → head (ap ⟦ w ↑ ⟧ v)) (vec-eta rs))
             (Eq.cong head
               (Pointwise-≡⇒≡ (head-fix (head rs) (tail rs) w)))
    where rs = ap ⟦ [ c′ ]ᶜ ⟧ qs

coset-wd {n} c {u} {t} u≈t = lemma-lm-head-inj cᵤ cₜ heads
  where
  uu = (ract {n} ᵗ) c u
  tt = (ract {n} ᵗ) c t
  cᵤ = uu .proj₂
  cₜ = tt .proj₂

  -- The two sides denote the same transformation: run the section law
  -- backwards on u, across the congruence, and forwards on t.
  sem : ∀ q → ap ⟦ uu .proj₁ ↑ • [ cᵤ ]ᶜ ⟧ q ≡
              ap ⟦ tt .proj₁ ↑ • [ cₜ ]ᶜ ⟧ q
  -- Named so that the reflexivity step's endpoint is pinned.
  c•u≈c•t : PB._≈_ ((₁₊ n) QRel,_===_) ([ c ]ᶜ • u) ([ c ]ᶜ • t)
  c•u≈c•t = PB.cong PB.refl u≈t

  sem q = Eq.trans (Eq.sym (sound (ract-sound-word c u) q))
            (Eq.trans (sound c•u≈c•t q)
                      (sound (ract-sound-word c t) q))

  -- Acting on a state, the lifted residuals pass through the head, so
  -- the heads are those of the coset representatives alone.
  heads : ∀ ps → head (ap ⟦ [ cᵤ ]ᶜ ⟧ ps) ≡ head (ap ⟦ [ cₜ ]ᶜ ⟧ ps)
  heads ps = Eq.trans (Eq.sym (peel (uu .proj₁) cᵤ ps))
               (Eq.trans (Eq.cong head (sem ps))
                         (peel (tt .proj₁) cₜ ps))


------------------------------------------------------------------------
-- The whole obligation, from ↑-injectivity alone

-- RhoExAbstract's Strategy-B derives the residual (≈) half from the
-- word equation plus the coset half, by cancelling [ c′ ]ᶜ — which is
-- legitimate because the presentation is Grouplike — and then
-- descending through the lift, which is where ↑-inj is needed.  Its
-- coset-half argument used to be supplied one axiom at a time; coset-wd
-- supplies it for every congruent pair at once.
--
-- So srel-wd, both halves, at every width, now rests on ↑-inj and
-- nothing else.  It cannot rest on less: RhoExAbstract's Converse
-- shows ↑-inj is derivable FROM srel-wd at the same level, so the two
-- are equivalent and no amount of further work on this route will
-- remove the hypothesis.  ↑-inj has to come from outside — from
-- Faithful one width down, which is the width induction.

module Full (n : ℕ)
  (↑-inj : ∀ (w v : Circuit n) →
     PB._≈_ ((₁₊ n) QRel,_===_) (w ↑) (v ↑) →
     PB._≈_ (n QRel,_===_) w v)
  where

  private module SB = RhoEx.Strategy-B n ↑-inj

  -- Congruent words act identically on cosets, residual and all.
  srel-wd-all : (c : ML (₁₊ n)) {u t : Circuit (₁₊ n)} →
                PB._≈_ ((₁₊ n) QRel,_===_) u t → act n c u ≋ act n c t
  srel-wd-all c eq = SB.resid-half c eq (coset-wd c eq) , coset-wd c eq
