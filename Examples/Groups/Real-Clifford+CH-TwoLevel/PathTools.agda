------------------------------------------------------------------------
-- Presentations of groups
--
-- Tools for the edges at a level L, given the edges below it.
--
-- * path-cong: a path may be replaced by an equal word;
-- * back: an edge into a state below L is an edge back out of it, the
--   generators being involutions;
-- * via: the edge g out of M follows from a path N′ out of g·M and a
--   path U out of M with N′ g ≈ U (the normal syllable N′ of g·M often
--   undoes g up to such a U);
-- * bridge: the edge g out of M follows from paths w₁ out of M and w₂
--   out of g·M, and a word V from w₁·M to w₂·g·M whose letters leave
--   states below L, with V w₁ ≈ w₂ g (the commuting squares of the
--   Main Lemma, Lemma A.7).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n : ℕ} where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics hiding (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Lvl ; level ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (gen-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n}

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

-- Equal words are paths together.
path-cong : {w w′ : Word (Gen n)} → w ≈ w′ → (M : Matrix n n D) .(o : ColOrth M) → Path w M o → Path w′ M o
path-cong {w} {w′} eq M o p = begin
  nw (actMʷ w′ M) (ColOrth-actMʷ w′ o) • w′    ≈⟨ cleft refl′ (nw-cong (sound-act (sym eq) M) (ColOrth-actMʷ w′ o) (ColOrth-actMʷ w o)) ⟩
  nw (actMʷ w M) (ColOrth-actMʷ w o) • w′      ≈⟨ cright sym eq ⟩
  nw (actMʷ w M) (ColOrth-actMʷ w o) • w       ≈⟨ p ⟩
  nw M o                                       ∎

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

-- The edge g out of M, from a path N′ out of g·M and a path U out of M
-- with N′ g ≈ U.
via : (g : Gen n) (M : Matrix n n D) .(o : ColOrth M) (N′ U : Word (Gen n)) →
      Path N′ (actM g M) (ColOrth-actMʷ [ g ]ʷ o) → N′ • [ g ]ʷ ≈ U → Path U M o → Path [ g ]ʷ M o
via g M o N′ U pN rel pU = begin
  nw (actM g M) (ColOrth-actMʷ [ g ]ʷ o) • [ g ]ʷ
    ≈⟨ cleft sym pN ⟩
  (nw (actMʷ N′ (actM g M)) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ g ]ʷ o)) • N′) • [ g ]ʷ
    ≈⟨ assoc ⟩
  nw (actMʷ N′ (actM g M)) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ g ]ʷ o)) • (N′ • [ g ]ʷ)
    ≈⟨ cright rel ⟩
  nw (actMʷ N′ (actM g M)) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ g ]ʷ o)) • U
    ≈⟨ cleft refl′ (nw-cong (sound-act rel M) _ (ColOrth-actMʷ U o)) ⟩
  nw (actMʷ U M) (ColOrth-actMʷ U o) • U
    ≈⟨ pU ⟩
  nw M o ∎

-- Peeling a path: from Path (u • v) and Path u after v, Path v.
peel : (u v : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) →
       Path (u • v) M o → Path u (actMʷ v M) (ColOrth-actMʷ v o) → Path v M o
peel u v M o puv pu = begin
  nw (actMʷ v M) (ColOrth-actMʷ v o) • v
    ≈⟨ cleft sym pu ⟩
  (nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ u (ColOrth-actMʷ v o)) • u) • v
    ≈⟨ assoc ⟩
  nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ u (ColOrth-actMʷ v o)) • (u • v)
    ≈⟨ cleft refl′ (nw-cong ≡.refl _ (ColOrth-actMʷ (u • v) o)) ⟩
  nw (actMʷ (u • v) M) (ColOrth-actMʷ (u • v) o) • (u • v)
    ≈⟨ puv ⟩
  nw M o ∎

module Below {L : Lvl} (ih : EdgesBelow L) where

  -- The commuting square.
  bridge : (g : Gen n) (M : Matrix n n D) .(o : ColOrth M) (w₁ w₂ V : Word (Gen n)) →
           Path w₁ M o → Path w₂ (actM g M) (ColOrth-actMʷ [ g ]ʷ o) →
           BelowSrc L V (actMʷ w₁ M) → V • w₁ ≈ w₂ • [ g ]ʷ → Path [ g ]ʷ M o
  bridge g M o w₁ w₂ V p₁ p₂ low rel =
    via g M o w₂ (V • w₁) p₂ (sym rel)
      (path-• V w₁ M o (path-below ih V (actMʷ w₁ M) (ColOrth-actMʷ w₁ o) low) p₁)

  -- An edge into a state below L.
  back-below : (g : Gen n) (M : Matrix n n D) .(o : ColOrth M) → level (actM g M) <ₗ L → Path [ g ]ʷ M o
  back-below g M o lt = back g M o (ih g (actM g M) (ColOrth-actMʷ [ g ]ʷ o) lt)
