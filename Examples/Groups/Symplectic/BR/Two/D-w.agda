------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a top-H-free word through a D box.
--
-- D.agda shows how to push a single gate g (with g ≢ H-gen ↥) through a
-- D box: [ d ]ᵈ • [ g ]ʷ ≈ S^ e ↓ • dir ↑ • [ d' ]ᵈ, i.e. the gate
-- emerges as a bottom-wire phase S^ e and a top-wire residual dir, and
-- the box updates to d'.  This file iterates that over a whole word with
-- no top-wire H, gathering the bottom phases (additively) and the top
-- residuals (by concatenation).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary.Decidable using (yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _≟_)
open import Data.Fin using (toℕ ; _≟_)
open import Data.Vec using ([] ; _∷_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Primality

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

module Examples.Groups.Symplectic.BR.Two.D-w (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime

open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Lemmas-Sym
open Symplectic-GroupLike
open Group-Lemmas ((₂₊ n) QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)
import Examples.Groups.Symplectic.BR.Two.L-CZ p-2 p-prime as LCZ
import Examples.Groups.Symplectic.BR.Two.L2-CZ p-2 p-prime as LCZ2

infixr 7 _•ⁿ_

------------------------------------------------------------------------
-- Words with no top-wire H

-- A Gen-2 word none of whose letters is the top-wire H (H-gen ↥) — the
-- words to which the single-gate push lemma-D-br applies letter by
-- letter (its hypothesis g ≢ H-gen ↥ is supplied at each singleton).
data No-Top-H : Word (Gen 2) → Set where
  sgⁿ  : ∀ {g} → g ≢ H-gen ↥ → No-Top-H [ g ]ʷ
  εⁿ   : No-Top-H ε
  _•ⁿ_ : ∀ {w v} → No-Top-H w → No-Top-H v → No-Top-H (w • v)

------------------------------------------------------------------------
-- The accumulated push data

-- push-D-w d w nth = (E , DIR , d'): pushing the top-H-free word w
-- through the box d leaves the bottom phase S^ E, the top residual DIR
-- and the updated box d'.  Phases add, residuals concatenate, and the
-- box is threaded left to right.
push-D-w : (d : D) (w : Word (Gen 2)) → No-Top-H w → ℤ ₚ × Word (Gen 1) × D
push-D-w d [ g ]ʷ (sgⁿ neq) =
  dir-of d g neq .proj₁ , dir-of d g neq .proj₂ , d'-of d g neq
push-D-w d ε       εⁿ        = ₀ , ε , d
push-D-w d (w • v) (nw •ⁿ nv) =
  let (e₁ , dir₁ , d₁) = push-D-w d  w nw
      (e₂ , dir₂ , d₂) = push-D-w d₁ v nv
  in e₁ + e₂ , dir₁ • dir₂ , d₂

------------------------------------------------------------------------
-- The word-level push

-- [ d ]ᵈ • w ≈ S^ E ↓ • DIR ↑ • [ d' ]ᵈ, the word analogue of
-- lemma-D-br.  Singletons are lemma-D-br; a concatenation runs the two
-- sub-pushes and gathers the pieces: the middle top residual dir₁ ↑
-- commutes past the bottom phase S^ e₂ ↓ (lemma-comm-Sᵏ-w↑), the phases
-- combine (lemma-S^k+l) and the residuals fuse under ↑.
lemma-D-w-br : (d : D) (w : Word (Gen 2)) (nth : No-Top-H w) →
  let (e , dir , d') = push-D-w d w nth in
  [ d ]ᵈ • w ≈ S^ e ↓ • dir ↑ • [ d' ]ᵈ
lemma-D-w-br d [ g ]ʷ (sgⁿ neq) = lemma-D-br d g neq
lemma-D-w-br d ε       εⁿ        = trans right-unit (sym (trans left-unit left-unit))
lemma-D-w-br d (w • v) (nw •ⁿ nv) = begin
  [ d ]ᵈ • (w • v)                                    ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • w) • v                                    ≈⟨ cleft (lemma-D-w-br d w nw) ⟩
  (S^ e₁ ↓ • dir₁ ↑ • [ d₁ ]ᵈ) • v                    ≈⟨ assoc ⟩
  S^ e₁ ↓ • (dir₁ ↑ • [ d₁ ]ᵈ) • v                    ≈⟨ cright assoc ⟩
  S^ e₁ ↓ • dir₁ ↑ • ([ d₁ ]ᵈ • v)                    ≈⟨ cright (cright (lemma-D-w-br d₁ v nv)) ⟩
  S^ e₁ ↓ • dir₁ ↑ • (S^ e₂ ↓ • dir₂ ↑ • [ d₂ ]ᵈ)     ≈⟨ cright (sym assoc) ⟩
  S^ e₁ ↓ • (dir₁ ↑ • S^ e₂ ↓) • (dir₂ ↑ • [ d₂ ]ᵈ)   ≈⟨ cright (cleft (sym (lemma-comm-Sᵏ-w↑ (toℕ e₂) dir₁))) ⟩
  S^ e₁ ↓ • (S^ e₂ ↓ • dir₁ ↑) • (dir₂ ↑ • [ d₂ ]ᵈ)   ≈⟨ cright assoc ⟩
  S^ e₁ ↓ • S^ e₂ ↓ • (dir₁ ↑ • dir₂ ↑ • [ d₂ ]ᵈ)     ≈⟨ sym assoc ⟩
  (S^ e₁ ↓ • S^ e₂ ↓) • (dir₁ ↑ • dir₂ ↑ • [ d₂ ]ᵈ)   ≈⟨ cleft (L01.lemma-S^k+l e₁ e₂) ⟩
  S^ (e₁ + e₂) ↓ • (dir₁ ↑ • dir₂ ↑ • [ d₂ ]ᵈ)        ≈⟨ cright (sym assoc) ⟩
  S^ (e₁ + e₂) ↓ • (dir₁ ↑ • dir₂ ↑) • [ d₂ ]ᵈ        ∎
  where
  r₁   = push-D-w d  w nw
  e₁   = r₁ .proj₁
  dir₁ = r₁ .proj₂ .proj₁
  d₁   = r₁ .proj₂ .proj₂
  r₂   = push-D-w d₁ v nv
  e₂   = r₂ .proj₁
  dir₂ = r₂ .proj₂ .proj₁
  d₂   = r₂ .proj₂ .proj₂

------------------------------------------------------------------------
-- No-Top-H is closed under the box-word vocabulary

-- Atomic non-top-H gates: each differs from H-gen ↥ by a head
-- constructor (gate₁/gate₂ vs ↥, or S-gate vs H-gate under ↥).
ntH-H : No-Top-H H
ntH-H = sgⁿ (λ ())

ntH-S : No-Top-H S
ntH-S = sgⁿ (λ ())

ntH-CZ : No-Top-H CZ
ntH-CZ = sgⁿ (λ ())

ntH-S↑ : No-Top-H (S ↑)
ntH-S↑ = sgⁿ (λ ())

-- Closure under powers.
ntH-^ : ∀ {w} → No-Top-H w → (k : ℕ) → No-Top-H (w ^ k)
ntH-^ nw zero      = εⁿ
ntH-^ nw (₁₊ zero) = nw
ntH-^ nw (₂₊ k)    = nw •ⁿ ntH-^ nw (₁₊ k)

-- (S ^ k) shifted up: only top-wire S letters, never a top H.
ntH-Sᵏ↑ : (k : ℕ) → No-Top-H ((S ^ k) ↑)
ntH-Sᵏ↑ zero      = εⁿ
ntH-Sᵏ↑ (₁₊ zero) = ntH-S↑
ntH-Sᵏ↑ (₂₊ k)    = ntH-S↑ •ⁿ ntH-Sᵏ↑ (₁₊ k)

-- The group-like inverse of any non-top-H generator is top-H-free.
ntH-gen-inv : (g : Gen 2) → g ≢ H-gen ↥ → No-Top-H (proj₁ (grouplike g))
ntH-gen-inv H-gen     neq = ntH-^ ntH-H _
ntH-gen-inv S-gen     neq = ntH-^ ntH-S _
ntH-gen-inv CZ-gen    neq = ntH-^ ntH-CZ _
ntH-gen-inv (S-gen ↥) neq = ntH-Sᵏ↑ _
ntH-gen-inv (H-gen ↥) neq = ⊥-elim (neq auto)
ntH-gen-inv (gate₀ () ↥ ↥) neq

-- Closure under the group-like word inverse (matching L-CZ's _⁻¹ʷ).
ntH-⁻¹ʷ : ∀ {w} → No-Top-H w → No-Top-H (w ⁻¹ʷ)
ntH-⁻¹ʷ (sgⁿ {g} neq) = ntH-gen-inv g neq
ntH-⁻¹ʷ εⁿ            = εⁿ
ntH-⁻¹ʷ (nu •ⁿ nv)    = ntH-⁻¹ʷ nv •ⁿ ntH-⁻¹ʷ nu

-- Derived box-word gadgets.
ntH-S^ : (k : ℤ ₚ) → No-Top-H (S^ k)
ntH-S^ k = ntH-^ ntH-S (toℕ k)

ntH-CZ^ : (k : ℤ ₚ) → No-Top-H (CZ^ k)
ntH-CZ^ k = ntH-^ ntH-CZ (toℕ k)

ntH-HH : No-Top-H HH
ntH-HH = ntH-^ ntH-H 2

ntH-ZM : (x : ℤ* ₚ) → No-Top-H (ZM x)
ntH-ZM x = ntH-S^ _ •ⁿ ntH-H •ⁿ ntH-S^ _ •ⁿ ntH-H •ⁿ ntH-S^ _ •ⁿ ntH-H

------------------------------------------------------------------------
-- The output of L-CZ's dir-of is top-H-free


------------------------------------------------------------------------
-- The output of L2-CZ's dir-of is top-H-free

-- L2-CZ.dir-of pushes CZ through the L' 2 ⊎ L' 1 collapse; its residual
-- uses the same bottom-wire vocabulary as L-CZ.dir-of.
dir-of₂-No-Top-H : (l : L' 2 ⊎ L' 1) → No-Top-H (LCZ2.dir-of l)
dir-of₂-No-Top-H (inj₁ (((c@₀ , d@₀) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz))) with b ≟ c
... | yes ()
... | no neq = ntH-CZ^ _
dir-of₂-No-Top-H (inj₁ (((c@₀ , d@(₁₊ _)) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz))) with b ≟ c
... | yes ()
... | no neq = ntH-S^ _ •ⁿ ntH-CZ^ _
dir-of₂-No-Top-H (inj₁ (((c@(₁₊ _) , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz))) with b ≟ c
... | yes eq = ntH-⁻¹ʷ (ntH-H •ⁿ ntH-CZ^ (((b , λ ()) ⁻¹) .proj₁) •ⁿ ntH-^ ntH-H 3) •ⁿ ntH-HH
... | no neq = ntH-ZM ((b + - c , λ eq → neq (b-c=0⇒b=c b c eq)) *' ((b , λ ()) ⁻¹))
                 •ⁿ ntH-H •ⁿ ntH-CZ^ _ •ⁿ ntH-^ ntH-H _
dir-of₂-No-Top-H (inj₁ (((c@₀ , d@₀) ∷ []) , ((a@(₁₊ _) , b) , nz)))          = εⁿ
dir-of₂-No-Top-H (inj₁ (((c@₀ , d@(₁₊ _)) ∷ []) , ((a@(₁₊ _) , b) , nz)))     = εⁿ
dir-of₂-No-Top-H (inj₁ (((c@(₁₊ _) , d) ∷ []) , ((a@(₁₊ _) , b) , nz)))       = ntH-^ ntH-H _ •ⁿ ntH-S^ _ •ⁿ ntH-H
dir-of₂-No-Top-H (inj₁ (((c , d) ∷ []) , ((a@₀ , b@₀) , nzx)))                = ⊥-elim (nzx auto)
dir-of₂-No-Top-H (inj₂ ([] , (a@₀ , b@(₁₊ _)) , nzx))                         = ntH-CZ^ _
dir-of₂-No-Top-H (inj₂ ([] , (a@(₁₊ _) , b) , nzx))                          = ntH-H •ⁿ ntH-CZ^ _ •ⁿ ntH-^ ntH-H _
dir-of₂-No-Top-H (inj₂ ([] , (a@₀ , b@₀) , nzx))                             = ⊥-elim (nzx auto)
