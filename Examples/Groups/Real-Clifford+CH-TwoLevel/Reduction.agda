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
-- generators.  The generators are involutions, so an edge is a path in
-- both directions (back), and, as in the paper (Lemmas A.6–A.9, after
-- Greylyn), the level of an edge is the higher of the levels of its
-- ends.  Edges are proved by well-founded induction on it: given all
-- edges with both ends below L, one must give the edges out of the
-- states at level L that do not go up (EdgeStep); an edge that goes up
-- is an edge that comes down from the other end.
--
-- Unlike the paper, every generator is an edge here, not only the
-- basic ones: a word is a path once each of its letters joins two
-- states below L (Low).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n : ℕ} where

open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Induction.WellFounded using (Acc ; acc)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
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
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (gen-gen)

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
    ≈⟨ refl′ (nw-cong (sound-act (gen-gen g) M) _ o) ⟩
  nw M o ∎
  where
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

-- g·(g·M) = M.
act-gg : (g : Gen n) (M : Matrix n n D) → actM g (actM g M) ≡ M
act-gg g M = sound-act (gen-gen g) M

------------------------------------------------------------------------
-- Levels

infix 4 _≤ₗ_

_≤ₗ_ : Lvl → Lvl → Set
x ≤ₗ y = x <ₗ y ⊎ x ≡ y

-- Levels are totally ordered.
cmpₗ : (x y : Lvl) → x <ₗ y ⊎ y ≤ₗ x
cmpₗ (a , b , c) (a′ , b′ , c′) = one (ℕP.<-cmp a a′)
  where
  three : Tri (c ℕ.< c′) (c ≡ c′) (c′ ℕ.< c) → (a , b , c) <ₗ (a , b , c′) ⊎ (a , b , c′) ≤ₗ (a , b , c)
  three (tri< lt _ _) = inj₁ (inj₂ (≡.refl , inj₂ (≡.refl , lt)))
  three (tri≈ _ ≡.refl _) = inj₂ (inj₂ ≡.refl)
  three (tri> _ _ gt) = inj₂ (inj₁ (inj₂ (≡.refl , inj₂ (≡.refl , gt))))
  two : Tri (b ℕ.< b′) (b ≡ b′) (b′ ℕ.< b) → (a , b , c) <ₗ (a , b′ , c′) ⊎ (a , b′ , c′) ≤ₗ (a , b , c)
  two (tri< lt _ _) = inj₁ (inj₂ (≡.refl , inj₁ lt))
  two (tri≈ _ ≡.refl _) = three (ℕP.<-cmp c c′)
  two (tri> _ _ gt) = inj₂ (inj₁ (inj₂ (≡.refl , inj₁ gt)))
  one : Tri (a ℕ.< a′) (a ≡ a′) (a′ ℕ.< a) → (a , b , c) <ₗ (a′ , b′ , c′) ⊎ (a′ , b′ , c′) ≤ₗ (a , b , c)
  one (tri< lt _ _) = inj₁ (inj₁ lt)
  one (tri≈ _ ≡.refl _) = two (ℕP.<-cmp b b′)
  one (tri> _ _ gt) = inj₂ (inj₁ (inj₁ gt))

------------------------------------------------------------------------
-- Levels along a path

-- Every letter of w, from M on, joins two states below L.
Low : Lvl → Word (Gen n) → Matrix n n D → Set
Low L [ g ]ʷ M = level M <ₗ L × level (actM g M) <ₗ L
Low L ε M = ⊤
Low L (u • v) M = Low L v M × Low L u (actMʷ v M)

-- The edges with both ends below L, and those out of the states at L
-- that do not go up.
EdgesBelow : Lvl → Set
EdgesBelow L = ∀ (g : Gen n) M .(o : ColOrth M) → level M <ₗ L → level (actM g M) <ₗ L → Path [ g ]ʷ M o

EdgesAt : Lvl → Set
EdgesAt L = ∀ (g : Gen n) M .(o : ColOrth M) → level M ≡ L → level (actM g M) ≤ₗ L → Path [ g ]ʷ M o

-- A word whose letters all join states below L is a path.
path-below : ∀ {L} → EdgesBelow L → (w : Word (Gen n)) → ∀ M .(o : ColOrth M) → Low L w M → Path w M o
path-below ih [ g ]ʷ M o (l₁ , l₂) = ih g M o l₁ l₂
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
    mutual
      edge-acc : ∀ L → Acc _<ₗ_ L → ∀ (g : Gen n) M .(o : ColOrth M) → level M ≡ L → level (actM g M) ≤ₗ L →
                 Path [ g ]ʷ M o
      edge-acc L (acc rs) g M o eq le = edge-step L ih g M o eq le
        where
        ih : EdgesBelow L
        ih g′ M′ o′ lt₁ lt₂ = edge-with g′ M′ o′ (rs lt₁) (rs lt₂)

      -- The edge g out of M, at the higher of the levels of its ends.
      edge-with : ∀ (g : Gen n) M .(o : ColOrth M) → Acc _<ₗ_ (level M) → Acc _<ₗ_ (level (actM g M)) →
                  Path [ g ]ʷ M o
      edge-with g M o aM agM = by (cmpₗ (level M) (level (actM g M)))
        where
        by : level M <ₗ level (actM g M) ⊎ level (actM g M) ≤ₗ level M → Path [ g ]ʷ M o
        by (inj₂ le) = edge-acc (level M) aM g M o ≡.refl le
        by (inj₁ lt) =
          back g M o (edge-acc (level (actM g M)) agM g (actM g M) (ColOrth-actMʷ [ g ]ʷ o) ≡.refl
                        (inj₁ (≡.subst (_<ₗ level (actM g M)) (≡.sym (≡.cong level (act-gg g M))) lt)))

  -- Every edge.
  edge : ∀ (g : Gen n) M .(o : ColOrth M) → Path [ g ]ʷ M o
  edge g M o = edge-with g M o (<ₗ-wellFounded (level M)) (<ₗ-wellFounded (level (actM g M)))

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
