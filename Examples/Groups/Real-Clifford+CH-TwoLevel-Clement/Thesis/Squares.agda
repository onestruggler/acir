------------------------------------------------------------------------
-- Presentations of groups
--
-- Completing diagrams (Section 5.1): prograde and retrograde edges
-- (Definition 5.5, Remark 5.6), and the squares of Lemma 4.4.
--
-- An edge s → g·s is prograde when g is the syllable of s, retrograde
-- when it is the syllable of g·s; either way it is a path.  Otherwise,
-- with N the syllable of s and N′ a path out of r = g·s (the syllable
-- of r when r is at the level L of s), a word W from N′·r whose letters
-- stay below L, with
--
--   W • N′ • g ≈ N,
--
-- completes the diagram: the normal word of r is that of N′·r, then
-- N′; the edges of W are given (EdgesBelow L), so that of N′·r is that
-- of W·N′·r = N·s, then W; and N·s comes from s by N (close).  When g
-- and N have disjoint indices, W = g and N′ = N (commute, Lemma 5.2).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Squares {n : ℕ} where

open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics hiding (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; Lvl ; _<ₗ_ ; _<ₗ?_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (<ₗ-trans)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act ; _≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (gen-gen ; Apart ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (levelᶜ ; sylᶜ ; stepᶜ ; step-ltᶜ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- Prograde and retrograde edges

prograde : (g : Gen n) (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} → pivot s ≡ just p →
           sylᶜ s ≡ [ g ]ʷ → Path [ g ]ʷ s o
prograde g s o pv e = ≡.subst (λ w → Path w s o) e (path-normal s o pv)

retrograde : (g : Gen n) (s : Matrix n n D) .(o : ColOrth s) {q : Fin n} → pivot (actM g s) ≡ just q →
             sylᶜ (actM g s) ≡ [ g ]ʷ → Path [ g ]ʷ s o
retrograde g s o pv e = back g s o (prograde g (actM g s) (ColOrth-actMʷ [ g ]ʷ o) pv e)

------------------------------------------------------------------------
-- The level of a normal step

-- The level drops.  (The proof is recomputed from the decision, so
-- that that of column-orthonormality may be irrelevant.)
step-lt′ : (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} → pivot s ≡ just p → levelᶜ (stepᶜ s) <ₗ levelᶜ s
step-lt′ s o pv = recompute (levelᶜ (stepᶜ s) <ₗ? levelᶜ s) (proj₂ (step-ltᶜ o pv))

-- A normal step out of a state at or below L lands below L.
normal-below : ∀ {L} (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} → pivot s ≡ just p →
               levelᶜ s ≤ₗ L → levelᶜ (stepᶜ s) <ₗ L
normal-below {L} s o pv (inj₁ lt) = <ₗ-trans (step-lt′ s o pv) lt
normal-below s o pv (inj₂ ≡.refl) = step-lt′ s o pv

------------------------------------------------------------------------
-- Squares

module Close {L : Lvl} (ih : EdgesBelow L) where

  close : (g : Gen n) (s : Matrix n n D) .(o : ColOrth s) (N N′ W : Word (Gen n)) →
          Path N s o → Path N′ (actM g s) (ColOrth-actMʷ [ g ]ʷ o) →
          Low L W (actMʷ N′ (actM g s)) → W • N′ • [ g ]ʷ ≈ N → Path [ g ]ʷ s o
  close g s o N N′ W pN pN′ low rel = begin
    nw (actM g s) (ColOrth-actMʷ [ g ]ʷ o) • [ g ]ʷ
      ≈⟨ cleft sym pN′ ⟩
    (nw (actMʷ N′ (actM g s)) (ColOrth-actMʷ (N′ • [ g ]ʷ) o) • N′) • [ g ]ʷ
      ≈⟨ cleft cleft sym (path-below ih W (actMʷ N′ (actM g s)) (ColOrth-actMʷ (N′ • [ g ]ʷ) o) low) ⟩
    ((nw (actMʷ (W • N′ • [ g ]ʷ) s) (ColOrth-actMʷ (W • N′ • [ g ]ʷ) o) • W) • N′) • [ g ]ʷ
      ≈⟨ trans assoc assoc ⟩
    nw (actMʷ (W • N′ • [ g ]ʷ) s) (ColOrth-actMʷ (W • N′ • [ g ]ʷ) o) • (W • N′ • [ g ]ʷ)
      ≈⟨ cright rel ⟩
    nw (actMʷ (W • N′ • [ g ]ʷ) s) (ColOrth-actMʷ (W • N′ • [ g ]ʷ) o) • N
      ≈⟨ cleft refl′ (nw-cong (sound-act rel s) (ColOrth-actMʷ (W • N′ • [ g ]ʷ) o) (ColOrth-actMʷ N o)) ⟩
    nw (actMʷ N s) (ColOrth-actMʷ N o) • N
      ≈⟨ pN ⟩
    nw s o ∎

  -- Lemma 5.2: an edge g apart from the normal edge h, which is also
  -- the normal edge of g·s.
  commute : (g h : Gen n) → Apart h g → (s : Matrix n n D) .(o : ColOrth s) →
            Path [ h ]ʷ s o → Path [ h ]ʷ (actM g s) (ColOrth-actMʷ [ g ]ʷ o) →
            levelᶜ (actM h (actM g s)) <ₗ L → levelᶜ (actM h s) <ₗ L → Path [ g ]ʷ s o
  commute g h ap s o ph ph′ l₁ l₂ =
    close g s o [ h ]ʷ [ h ]ʷ [ g ]ʷ ph ph′ (l₁ , ≡.subst (λ M → levelᶜ M <ₗ L) (≡.sym (sound-act rel s)) l₂) rel
    where
    rel : [ g ]ʷ • [ h ]ʷ • [ g ]ʷ ≈ [ h ]ʷ
    rel = begin
      [ g ]ʷ • [ h ]ʷ • [ g ]ʷ      ≈⟨ cright comm-gen h g ap ⟩
      [ g ]ʷ • [ g ]ʷ • [ h ]ʷ      ≈⟨ sym assoc ⟩
      ([ g ]ʷ • [ g ]ʷ) • [ h ]ʷ    ≈⟨ cleft gen-gen g ⟩
      ε • [ h ]ʷ                    ≈⟨ left-unit ⟩
      [ h ]ʷ                        ∎
