------------------------------------------------------------------------
-- Presentations of groups
--
-- The state graph (Definition 4.2), and completeness (Theorem 4.1)
-- reduced to edges, level by level.
--
-- The states are the orthogonal matrices; a normal edge M ⇒ syl M · M
-- follows the algorithm, and a simple edge M → g · M is any generator.
-- The normal word nw M of M is the output of the algorithm, so that
-- ⟦ nw M ⟧ M = I, and a word w leads from M to w · M along a path
-- when
--
--   Path w M :  nw (w · M) • w ≈ nw M.
--
-- Completeness follows once every word is a path from I.  Paths
-- compose, and the generators are involutions, so an edge is a path
-- both ways (back).  As in RCCH's Reduction, the level of an edge is
-- the higher of its ends', and edges are proved by well-founded
-- induction on it: given those with both ends below L, one gives those
-- out of the states at L that do not go up (EdgeStep).  Clément states
-- the induction step for basic edges only (Lemma 4.4) and leaves the
-- induction itself implicit; here it is for every generator.
--
-- Below L, two words with the same ends are related as soon as all
-- their letters join states below L (low-complete).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n : ℕ} where

open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Induction.WellFounded using (Acc ; acc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics hiding (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; Lvl ; _<ₗ_ ; <ₗ-wellFounded)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act ; act-gg ; _≤ₗ_ ; cmpₗ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (gen-gen ; •-cancelˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (levelᶜ ; sylᶜ ; synthᶜ ; synthᶜ-step)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- Normal words and paths

nw : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n)
nw = synthᶜ

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

-- Related words are paths together.
path-cong : {w w′ : Word (Gen n)} → w ≈ w′ → (M : Matrix n n D) .(o : ColOrth M) → Path w M o → Path w′ M o
path-cong {w} {w′} e M o p = begin
  nw (actMʷ w′ M) (ColOrth-actMʷ w′ o) • w′    ≈⟨ cleft refl′ (nw-cong (≡.sym (sound-act e M)) _ _) ⟩
  nw (actMʷ w M) (ColOrth-actMʷ w o) • w′      ≈⟨ cright sym e ⟩
  nw (actMʷ w M) (ColOrth-actMʷ w o) • w       ≈⟨ p ⟩
  nw M o                                       ∎

-- A normal edge is a path.
path-normal : (M : Matrix n n D) .(o : ColOrth M) {p : Fin n} → pivot M ≡ just p → Path (sylᶜ M) M o
path-normal M o pv = sym (refl′ (synthᶜ-step M o pv))

------------------------------------------------------------------------
-- Edges are paths both ways

-- An edge g out of g·M gives the edge g out of M.
back : (g : Gen n) (M : Matrix n n D) .(o : ColOrth M) →
       Path [ g ]ʷ (actM g M) (ColOrth-actMʷ [ g ]ʷ o) → Path [ g ]ʷ M o
back g M o p = begin
  nw (actM g M) (ColOrth-actMʷ [ g ]ʷ o) • [ g ]ʷ
    ≈⟨ cleft sym p ⟩
  (nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o)) • [ g ]ʷ) • [ g ]ʷ
    ≈⟨ assoc ⟩
  nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o)) • ([ g ]ʷ • [ g ]ʷ)
    ≈⟨ cright gen-gen g ⟩
  nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o)) • ε
    ≈⟨ right-unit ⟩
  nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o))
    ≈⟨ refl′ (nw-cong (act-gg g M) _ o) ⟩
  nw M o ∎

------------------------------------------------------------------------
-- Levels along a path

-- Every letter of w, from M on, joins two states below L.
Low : Lvl → Word (Gen n) → Matrix n n D → Set
Low L [ g ]ʷ M = levelᶜ M <ₗ L × levelᶜ (actM g M) <ₗ L
Low L ε M = ⊤
Low L (u • v) M = Low L v M × Low L u (actMʷ v M)

-- The edges with both ends below L, and those out of the states at L
-- that do not go up.
EdgesBelow : Lvl → Set
EdgesBelow L = ∀ (g : Gen n) M .(o : ColOrth M) → levelᶜ M <ₗ L → levelᶜ (actM g M) <ₗ L → Path [ g ]ʷ M o

EdgesAt : Lvl → Set
EdgesAt L = ∀ (g : Gen n) M .(o : ColOrth M) → levelᶜ M ≡ L → levelᶜ (actM g M) ≤ₗ L → Path [ g ]ʷ M o

-- A word whose letters all join states below L is a path.
path-below : ∀ {L} → EdgesBelow L → (w : Word (Gen n)) → ∀ M .(o : ColOrth M) → Low L w M → Path w M o
path-below ih [ g ]ʷ M o (l₁ , l₂) = ih g M o l₁ l₂
path-below ih ε M o _ = path-ε M o
path-below ih (u • v) M o (bv , bu) =
  path-• u v M o (path-below ih u (actMʷ v M) (ColOrth-actMʷ v o) bu) (path-below ih v M o bv)

-- Below L, words with the same ends are related.
low-complete : ∀ {L} → EdgesBelow L → (u v : Word (Gen n)) → ∀ M .(o : ColOrth M) →
               Low L u M → Low L v M → actMʷ u M ≡ actMʷ v M → u ≈ v
low-complete ih u v M o lu lv eq = •-cancelˡ (begin
  nw (actMʷ u M) (ColOrth-actMʷ u o) • u     ≈⟨ path-below ih u M o lu ⟩
  nw M o                                     ≈⟨ sym (path-below ih v M o lv) ⟩
  nw (actMʷ v M) (ColOrth-actMʷ v o) • v     ≈⟨ cleft refl′ (nw-cong (≡.sym eq) _ _) ⟩
  nw (actMʷ u M) (ColOrth-actMʷ u o) • v     ∎)

------------------------------------------------------------------------
-- The reduction

-- One step of the induction on levels.
EdgeStep : Set
EdgeStep = ∀ L → EdgesBelow L → EdgesAt L

module _ (edge-step : EdgeStep) where

  private
    mutual
      edge-acc : ∀ L → Acc _<ₗ_ L → ∀ (g : Gen n) M .(o : ColOrth M) → levelᶜ M ≡ L → levelᶜ (actM g M) ≤ₗ L →
                 Path [ g ]ʷ M o
      edge-acc L (acc rs) g M o eq le = edge-step L ih g M o eq le
        where
        ih : EdgesBelow L
        ih g′ M′ o′ lt₁ lt₂ = edge-with g′ M′ o′ (rs lt₁) (rs lt₂)

      -- The edge g out of M, at the higher of the levels of its ends.
      edge-with : ∀ (g : Gen n) M .(o : ColOrth M) → Acc _<ₗ_ (levelᶜ M) → Acc _<ₗ_ (levelᶜ (actM g M)) →
                  Path [ g ]ʷ M o
      edge-with g M o aM agM = by (cmpₗ (levelᶜ M) (levelᶜ (actM g M)))
        where
        by : levelᶜ M <ₗ levelᶜ (actM g M) ⊎ levelᶜ (actM g M) ≤ₗ levelᶜ M → Path [ g ]ʷ M o
        by (inj₂ le) = edge-acc (levelᶜ M) aM g M o ≡.refl le
        by (inj₁ lt) =
          back g M o (edge-acc (levelᶜ (actM g M)) agM g (actM g M) (ColOrth-actMʷ [ g ]ʷ o) ≡.refl
                        (inj₁ (≡.subst (_<ₗ levelᶜ (actM g M)) (≡.sym (≡.cong levelᶜ (act-gg g M))) lt)))

  -- Every edge.
  edge : ∀ (g : Gen n) M .(o : ColOrth M) → Path [ g ]ʷ M o
  edge g M o = edge-with g M o (<ₗ-wellFounded (levelᶜ M)) (<ₗ-wellFounded (levelᶜ (actM g M)))

  -- Every word.
  path : (w : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) → Path w M o
  path [ g ]ʷ M o = edge g M o
  path ε M o = path-ε M o
  path (u • v) M o = path-• u v M o (path u (actMʷ v M) (ColOrth-actMʷ v o)) (path v M o)

  -- Theorem 4.1: words with the same matrix are related.
  completeness : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
  completeness {u} {v} eq = •-cancelˡ (begin
    nw ⟦ u ⟧ᵐ ou • u         ≈⟨ path u 𝕀 ColOrth-𝕀 ⟩
    nw 𝕀 ColOrth-𝕀           ≈⟨ sym (path v 𝕀 ColOrth-𝕀) ⟩
    nw ⟦ v ⟧ᵐ ov • v         ≈⟨ cleft refl′ (nw-cong (≡.sym eq) ov ou) ⟩
    nw ⟦ u ⟧ᵐ ou • v         ∎)
    where
    ou : ColOrth ⟦ u ⟧ᵐ
    ou = ColOrth-actMʷ u ColOrth-𝕀
    ov : ColOrth ⟦ v ⟧ᵐ
    ov = ColOrth-actMʷ v ColOrth-𝕀
