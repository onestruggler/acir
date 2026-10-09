------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness, reduced to edges level by level.
--
-- The normal word of an orthogonal matrix M is the output of Algorithm
-- 1, so ⟦ nw M ⟧ M = I.  Completeness follows from
--
--   Path w M :  nw (w·M) • w ≈ nw M       for every word w,
--
-- since two words u, v with ⟦ u ⟧ = ⟦ v ⟧ are then both paths from I
-- to the same matrix, and cancel.  Path reduces to the edges of single
-- generators, proved by well-founded induction on the level of the
-- source: given all edges out of states below L, one must give all
-- edges out of states at level L (EdgeStep).
--
-- Unlike the paper (Lemmas A.6–A.9), every generator is an edge here,
-- not only the basic ones: a word acts as a path once each of its
-- letters leaves from a state below L (BelowSrc), whatever the level
-- of the state it reaches.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n : ℕ} where

open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Induction.WellFounded using (Acc ; acc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics hiding (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Soundness using (sound-axiom)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Lvl ; level ; _<ₗ_ ; <ₗ-wellFounded)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Synthesis using (synth)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

------------------------------------------------------------------------
-- Soundness, for the congruence: related words act alike

sound-act : {w v : Word (Gen n)} → w ≈ v → ∀ (M : Matrix n n D) → actMʷ w M ≡ actMʷ v M
sound-act refl M = ≡.refl
sound-act (sym h) M = ≡.sym (sound-act h M)
sound-act (trans h k) M = ≡.trans (sound-act h M) (sound-act k M)
sound-act (cong {w} {w′} {v} {v′} h k) M =
  ≡.trans (≡.cong (actMʷ w) (sound-act k M)) (sound-act h (actMʷ v′ M))
sound-act assoc M = ≡.refl
sound-act left-unit M = ≡.refl
sound-act right-unit M = ≡.refl
sound-act (axiom {w} {v} a) M =
  ≡.trans (actMʷ≡ w M) (≡.trans (·*·-congˡ ⟦ w ⟧ᵐ ⟦ v ⟧ᵐ M (sound-axiom a)) (≡.sym (actMʷ≡ v M)))
  where
  -- Congruence with explicit endpoints (cong would leave them as metas
  -- under the matrix product, which the conversion checker unfolds).
  ·*·-congˡ : (A B M : Matrix n n D) → A ≡ B → A ·*· M ≡ B ·*· M
  ·*·-congˡ A B M ≡.refl = ≡.refl

------------------------------------------------------------------------
-- Normal words and paths

nw : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n)
nw = synth

-- The normal word depends on the matrix alone.  (The equation comes
-- first: it determines the matrices, which the irrelevant proofs do
-- not, and leaving them to be inferred from those is intractable.)
nw-cong : {M M′ : Matrix n n D} → M ≡ M′ → .(o : ColOrth M) .(o′ : ColOrth M′) → nw M o ≡ nw M′ o′
nw-cong ≡.refl o o′ = ≡.refl

-- w leads from M to w·M: the normal word of M is that of w·M, then w.
Path : (w : Word (Gen n)) (M : Matrix n n D) → .(ColOrth M) → Set
Path w M o = nw (actMʷ w M) (ColOrth-actMʷ w o) • w ≈ nw M o

path-ε : (M : Matrix n n D) .(o : ColOrth M) → Path ε M o
path-ε M o = right-unit

path-• : (u v : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) →
         Path u (actMʷ v M) (ColOrth-actMʷ v o) → Path v M o → Path (u • v) M o
path-• u v M o pu pv = begin
  nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ (u • v) o) • (u • v)    ≈⟨ sym assoc ⟩
  (nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ (u • v) o) • u) • v    ≈⟨ cleft pu ⟩
  nw (actMʷ v M) (ColOrth-actMʷ v o) • v                          ≈⟨ pv ⟩
  nw M o                                                          ∎

------------------------------------------------------------------------
-- Levels along a path

-- Every state along w from M that some letter leaves lies below L.
BelowSrc : Lvl → Word (Gen n) → Matrix n n D → Set
BelowSrc L [ g ]ʷ M = level M <ₗ L
BelowSrc L ε M = ⊤
BelowSrc L (u • v) M = BelowSrc L v M × BelowSrc L u (actMʷ v M)

-- The edges out of the states below L, and at L.
EdgesBelow : Lvl → Set
EdgesBelow L = ∀ (g : Gen n) M .(o : ColOrth M) → level M <ₗ L → Path [ g ]ʷ M o

EdgesAt : Lvl → Set
EdgesAt L = ∀ (g : Gen n) M .(o : ColOrth M) → level M ≡ L → Path [ g ]ʷ M o

-- A word whose letters all leave from states below L is a path.
path-below : ∀ {L} → EdgesBelow L → (w : Word (Gen n)) → ∀ M .(o : ColOrth M) → BelowSrc L w M → Path w M o
path-below ih [ g ]ʷ M o lt = ih g M o lt
path-below ih ε M o _ = path-ε M o
path-below ih (u • v) M o (bv , bu) =
  path-• u v M o (path-below ih u (actMʷ v M) (ColOrth-actMʷ v o) bu) (path-below ih v M o bv)

------------------------------------------------------------------------
-- The reduction

-- One step of the induction on levels.
EdgeStep : Set
EdgeStep = ∀ L → EdgesBelow L → EdgesAt L

module _ (edge-step : EdgeStep) where

  private
    edge-acc : ∀ L → Acc _<ₗ_ L → ∀ (g : Gen n) M .(o : ColOrth M) → level M ≡ L → Path [ g ]ʷ M o
    edge-acc L (acc rs) g M o eq = edge-step L ih g M o eq
      where
      ih : EdgesBelow L
      ih g′ M′ o′ lt = edge-acc (level M′) (rs lt) g′ M′ o′ ≡.refl

  -- Every edge.
  edge : ∀ (g : Gen n) M .(o : ColOrth M) → Path [ g ]ʷ M o
  edge g M o = edge-acc (level M) (<ₗ-wellFounded (level M)) g M o ≡.refl

  -- Every word.
  path : (w : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) → Path w M o
  path [ g ]ʷ M o = edge g M o
  path ε M o = path-ε M o
  path (u • v) M o = path-• u v M o (path u (actMʷ v M) (ColOrth-actMʷ v o)) (path v M o)

  -- Words with the same normal word for their matrix: the relations are
  -- complete, given cancellation (which the involutions give).
  module _ (•-cancelˡ : {x u v : Word (Gen n)} → x • u ≈ x • v → u ≈ v) where

    completeness : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
    completeness {u} {v} eq = •-cancelˡ (begin
      nw ⟦ u ⟧ᵐ ou • u         ≈⟨ path u 𝕀 ColOrth-𝕀 ⟩
      nw 𝕀 ColOrth-𝕀           ≈⟨ sym (path v 𝕀 ColOrth-𝕀) ⟩
      nw ⟦ v ⟧ᵐ ov • v         ≈⟨ cleft refl′ (nw-cong (≡.sym eq) ov ou) ⟩
      nw ⟦ u ⟧ᵐ ou • v         ∎)
      where
      refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
      refl′ ≡.refl = refl
      ou : ColOrth ⟦ u ⟧ᵐ
      ou = ColOrth-actMʷ u ColOrth-𝕀
      ov : ColOrth ⟦ v ⟧ᵐ
      ov = ColOrth-actMʷ v ColOrth-𝕀
