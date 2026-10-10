------------------------------------------------------------------------
-- Presentations of groups
--
-- The states at a level L = (p + 1, k, ℓ) with k > 0, and their
-- valid pairs: two odd entries of the pivot column's numerator in the
-- same residue class.  H on a valid pair keeps the scale and makes
-- both entries even, so it goes down.
--
-- * The odd entries of each class are evenly many (Norm), so every
--   odd entry has a partner in its class; the canonical pair is the
--   first odd entry and the next one in its class, which Algorithm 1
--   removes (its syllable is H_[0,i₂] X_[0,i₁] = X_[0,i₁] H_[i₁,i₂]).
-- The facts about levels and columns are in PairLevels; here:
--
-- * canonical: the edge H on the canonical pair, from the normal
--   syllable and the edge X_[0,i₁] below L.
-- * square: the edges H on two disjoint valid pairs commute, so one
--   gives the other (a commuting square below L).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false ; recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ ; oddℕ-+)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; lde ; num ; lde-char ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-one ; count-lt ; first-cong)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (count-split ; search)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (evenodd ; evenclass ; 2ᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-just ; Beyond ; Lvl ; lvlAt ; level ; level-just ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (syl ; top ; Beyond-actM ; eᶻ ; col𝕀≡)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (same-class ; pairW ; H-action ; pairW-j ; pairW-ℓ ; pairW-≢)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (Mono ; mono-col ; mono-level ; Bℓ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (flip-X ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; Low)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (path-cong ; peel ; module Below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (path-normal ; syl-of ; level-le ; bℓ-below ; pivot-stay)
import Examples.Groups.Real-Clifford+CH-TwoLevel.PivotColumn as PC

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Below {L = suc (toℕ p) , suc k′ , ℓ} ih using (bridge)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairLevels p k′ ℓ public hiding (module State)
import Examples.Groups.Real-Clifford+CH-TwoLevel.PairLevels p k′ ℓ as PL

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- A state at level L, and its edges

module State (M : Matrix n n D) .(o : ColOrth M) (eq : level M ≡ L) where

  open PL.State M o eq public

  ----------------------------------------------------------------------
  -- The canonical edge

  canonical : Path [ H-gen i₁ i₂ i₁<i₂ ]ʷ M o
  canonical = by (toℕ i₁ ℕP.≟ 0)
    where
    pN : Path (syl M) M o
    pN = path-normal M o pv
    by : Dec (toℕ i₁ ≡ 0) → Path [ H-gen i₁ i₂ i₁<i₂ ]ʷ M o
    by (yes z) = ≡.subst (λ w → Path w M o) (≡.trans sylM (pairSyl-0 i₁ i₂ i₁<i₂ z)) pN
    by (no nz) = peel (X z₀ i₁ 0<i₁) (H i₁ i₂ i₁<i₂) M o pXH pX
      where
      pos : 0 ℕ.< toℕ i₁
      pos = ℕP.n≢0⇒n>0 nz
      z₀ = zeroOf i₁
      0<i₁ : z₀ < i₁
      0<i₁ = zeroOf-< i₁ pos
      0<i₂ = ℕP.<-trans 0<i₁ i₁<i₂
      c4′ : H z₀ i₂ 0<i₂ • X z₀ i₁ 0<i₁ ≈ X z₀ i₁ 0<i₁ • H i₁ i₂ i₁<i₂
      c4′ = flip-X 0<i₁ (axiom (c4 0<i₁ i₁<i₂))
      pXH : Path (X z₀ i₁ 0<i₁ • H i₁ i₂ i₁<i₂) M o
      pXH = path-cong (trans (refl′ (≡.trans sylM (pairSyl-s i₁ i₂ i₁<i₂ pos))) c4′) M o pN
      HM = actM (H-gen i₁ i₂ i₁<i₂) M
      l₁ : level HM <ₗ L
      l₁ = below i₁ i₂ i₁<i₂ valid₁₂
      pX : Path (X z₀ i₁ 0<i₁) HM (ColOrth-actMʷ [ H-gen i₁ i₂ i₁<i₂ ]ʷ o)
      pX = ih (X-gen z₀ i₁ 0<i₁) HM (ColOrth-actMʷ [ H-gen i₁ i₂ i₁<i₂ ]ʷ o) l₁ (X-low 0<i₁ (odd≤ oi₁) HM l₁)

  -- The canonical edge, at indices known to be the canonical pair.
  canonical-at : ∀ {a b : Fin n} .(ab : a < b) → firstOdd W ≡ just a → nextSame a W ≡ just b →
                 Path [ H-gen a b ab ]ʷ M o
  canonical-at {a} {b} ab fa nb = H-transport i₁<i₂ ab i₁≡a i₂≡b canonical
    where
    i₁≡a : i₁ ≡ a
    i₁≡a = just-injective (≡.trans (≡.sym fo) fa)
    i₂≡b : i₂ ≡ b
    i₂≡b = just-injective (≡.trans (≡.sym nx) (≡.trans (≡.cong (λ x → nextSame x W) i₁≡a) nb))

  ----------------------------------------------------------------------
  -- Squares

  square : ∀ i j .(ij : i < j) i′ j′ .(ij′ : i′ < j′) → Valid W i j → Valid W i′ j′ →
           i′ ≢ i → i′ ≢ j → j′ ≢ i → j′ ≢ j → Path [ H-gen i j ij ]ʷ M o → Path [ H-gen i′ j′ ij′ ]ʷ M o
  square i j ij i′ j′ ij′ vl vl′ a b c d pP =
    bridge (H-gen i′ j′ ij′) M o (H i j ij) (H i j ij) (H i′ j′ ij′) pP pP′ lowV rel
    where
    sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
    sym≢ ne e = ne (≡.sym e)
    H′M = actM (H-gen i′ j′ ij′) M
    pP′ : Path (H i j ij) H′M (ColOrth-actMʷ [ H-gen i′ j′ ij′ ]ʷ o)
    pP′ = ih (H-gen i j ij) H′M (ColOrth-actMʷ [ H-gen i′ j′ ij′ ]ʷ o) (below i′ j′ ij′ vl′)
             (below₂ i′ j′ ij′ i j ij vl′ vl (sym≢ a) (sym≢ c) (sym≢ b) (sym≢ d))
    lowV : Low L (H i′ j′ ij′) (actMʷ (H i j ij) M)
    lowV = below i j ij vl , below₂ i j ij i′ j′ ij′ vl vl′ a b c d
    rel : H i′ j′ ij′ • H i j ij ≈ H i j ij • H i′ j′ ij′
    rel = comm-gen (H-gen i′ j′ ij′) (H-gen i j ij) ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])
