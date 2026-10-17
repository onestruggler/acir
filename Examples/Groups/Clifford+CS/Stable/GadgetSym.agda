------------------------------------------------------------------------
-- Presentations of groups
--
-- The symmetry of two white controls for the decoding's gadgets, at
-- every width, from the doubly controlled S
--
-- Five.Facts4's gadgets — the phase pair, the rotation and the hybrid,
-- with their inverses — carried to 4 + m wires by λ⁰ (`gad`, `gad⁻`)
-- keep their inverses and their decompositions: the inverse phase pair
-- and the twisted part of the inverse hybrid are twisted commutators
-- with S on wire 0, which survive λ⁰ with S uncontrolled
-- (Stable.SwapSym.tw-step), and the rotation is a conjugate of the
-- phase pair by the hybrid.  So Stable.Gadget's SwapSym holds for every
-- gadget on every width from six on (`ss-gad`) once it holds for the
-- doubly controlled S, white (`sS`) or black (`ss-gad¹`, through
-- SwapSym.ss-λ⁰λ⁰): the twisted commutators by SwapSym.swapsym-tw, the
-- rest by products and inverses — Five.Gadget5's proof of (F6), one
-- width up.  The doubly controlled S itself is Stable.SwapSymS, from
-- completeness on five wires (`ss-gad₅`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.GadgetSym
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics using (S)
open import Examples.Groups.Clifford+CS.Completeness using (complete₁)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki)
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW
import Examples.Groups.Clifford+CS.Stable.SwapSym as SwapSym
import Examples.Groups.Clifford+CS.Stable.SwapSymS as SwapSymS
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

open Facts4 F

module CW (m : ℕ) = CalcW m (f4 m) (f5 m) (tr m)
module SY (m : ℕ) = SwapSym m (f4 m) (f5 m) (tr m) (f4 (suc m)) (f5 (suc m)) (tr (suc m))

private
  module S₁ = Below 1 complete₁

------------------------------------------------------------------------
-- The gadgets on every width

gad gad⁻ : Kind → ∀ m → Circuit (₄₊ m)
gad  V zero    = G V
gad  V (suc m) = λ⁰ʷ (gad V m)
gad⁻ V zero    = G⁻ V
gad⁻ V (suc m) = λ⁰ʷ (gad⁻ V m)

-- S³, the inverse of S on wire 0.
S³ : ∀ {n} → Circuit (₁₊ n)
S³ = S • S • S

private
  S-inv : ∀ m → (₄₊ m) ⊢ᵧ S • S³ ≈ ε
  S-inv m = embed (S₁.by-sem (S • S • S • S) ε Eq.refl)

  S-inv′ : ∀ m → (₄₊ m) ⊢ᵧ S³ • S ≈ ε
  S-inv′ m = embed (S₁.by-sem ((S • S • S) • S) ε Eq.refl)

inv-gad : ∀ V m → (₄₊ m) ⊢ᵧ gad V m • gad⁻ V m ≈ ε
inv-gad V zero    = embed (inv V)
inv-gad V (suc m) = CW.transport⁰ m (inv-gad V m)

inv-gad′ : ∀ V m → (₄₊ m) ⊢ᵧ gad⁻ V m • gad V m ≈ ε
inv-gad′ V zero    = embed (inv′ V)
inv-gad′ V (suc m) = CW.transport⁰ m (inv-gad′ V m)

-- The decompositions, on every width.
dec-ppW : ∀ m → (₄₊ m) ⊢ᵧ gad⁻ kpp m ≈ gad⁻ krot m • S³ • gad krot m • S
dec-ppW zero    = embed dec-pp⁻
dec-ppW (suc m) = SY.tw-step m (gad⁻ kpp m) (gad⁻ krot m) (gad krot m) S S³ (dec-ppW m) (S-inv m) (S-inv′ m)

dec-kiW : ∀ m → (₄₊ m) ⊢ᵧ gad⁻ kki m ≈ (gad kki m • S³ • gad⁻ kki m • S) • gad⁻ kpp m
dec-kiW zero    = embed dec-ki⁻
dec-kiW (suc m) =
  PB.trans (CW.transport⁰ m (dec-kiW m))
           (PB.cong (CW.tw-top′ m (gad⁻ kki m) (gad kki m) S S³ (S-inv m) (S-inv′ m)) PB.refl)

dec-rotW : ∀ m → (₄₊ m) ⊢ᵧ gad krot m ≈ gad⁻ kki m • gad kpp m • gad kki m
dec-rotW zero    = embed dec-rot
dec-rotW (suc m) = CW.transport⁰ m (dec-rotW m)

------------------------------------------------------------------------
-- The symmetry of the two top controls

private
  λλ : ∀ {m} → Circuit (₄₊ m) → Circuit (suc (suc (₄₊ m)))
  λλ x = λ⁰ʷ (λ⁰ʷ x)

  tr2 : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (suc (₄₊ m))) ⊢ᵧ λλ u ≈ λλ v
  tr2 m e = CW.transport⁰ (suc m) (CW.transport⁰ m e)

  ss-≈ : ∀ m {x y} → (suc (suc (₄₊ m))) ⊢ᵧ x ≈ y → SY.SS m x → SY.SS m y
  ss-≈ m e s = PB.trans (PB.cong PB.refl (PB.cong (PB.sym e) PB.refl)) (PB.trans s e)

module _ (sS : ∀ m → SY.SS m (λ⁰ʷ (λ⁰ʷ (S {₃₊ m})))) where

  private
    ss-S³ : ∀ m → SY.SS m (λλ (S³ {₃₊ m}))
    ss-S³ m = SY.ss-• m (sS m) (SY.ss-• m (sS m) (sS m))

    ss-pp⁻ : ∀ m → SY.SS m (λλ (gad⁻ kpp m))
    ss-pp⁻ m = SY.swapsym-tw m (gad⁻ kpp m) (gad⁻ krot m) (gad krot m) S S³
                 (dec-ppW m) (inv-gad krot m) (inv-gad′ krot m) (sS m) (ss-S³ m)

    ss-pp : ∀ m → SY.SS m (λλ (gad kpp m))
    ss-pp m = SY.ss-inv m (ss-pp⁻ m) (tr2 m (inv-gad′ kpp m)) (tr2 m (inv-gad kpp m))

    ss-ki⁻ : ∀ m → SY.SS m (λλ (gad⁻ kki m))
    ss-ki⁻ m =
      ss-≈ m (PB.sym (tr2 m (dec-kiW m)))
        (SY.ss-• m (SY.swapsym-tw m T (gad kki m) (gad⁻ kki m) S S³ PB.refl
                      (inv-gad′ kki m) (inv-gad kki m) (sS m) (ss-S³ m))
                   (ss-pp⁻ m))
      where
      T : Circuit (₄₊ m)
      T = gad kki m • S³ • gad⁻ kki m • S

    ss-ki : ∀ m → SY.SS m (λλ (gad kki m))
    ss-ki m = SY.ss-inv m (ss-ki⁻ m) (tr2 m (inv-gad′ kki m)) (tr2 m (inv-gad kki m))

    ss-rot : ∀ m → SY.SS m (λλ (gad krot m))
    ss-rot m = ss-≈ m (PB.sym (tr2 m (dec-rotW m))) (SY.ss-• m (ss-ki⁻ m) (SY.ss-• m (ss-pp m) (ss-ki m)))

  -- Every gadget, on every width from six on.
  ss-gad : ∀ V m → SY.SS m (λ⁰ʷ (λ⁰ʷ (gad V m)))
  ss-gad kpp  m = ss-pp m
  ss-gad krot m = ss-rot m
  ss-gad kki  m = ss-ki m

-- The same from the black doubly controlled S.
ss-gad¹ : (∀ m → SY.SS m (λ¹ʷ (λ¹ʷ (S {₃₊ m})))) → ∀ V m → SY.SS m (λ⁰ʷ (λ⁰ʷ (gad V m)))
ss-gad¹ h = ss-gad (λ m → SY.ss-λ⁰λ⁰ m S (h m))

-- And so from completeness on five wires (Stable.SwapSymS).
ss-gad₅ : Completeᵧ 5 → ∀ V m → SY.SS m (λ⁰ʷ (λ⁰ʷ (gad V m)))
ss-gad₅ c₅ = ss-gad¹ (λ m → SwapSymS.ss-S¹ m (f4 (suc m)) (f5 (suc m)) (tr (suc m)) c₅)
