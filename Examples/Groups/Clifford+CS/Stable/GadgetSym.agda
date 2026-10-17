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
-- completeness on five wires (`ss-gad₅`).  The λ-calculus is given
-- under the bound of Stable.Inputs: a lemma at index m takes `Bnd m`,
-- the symmetry at index m (six wires and more) `Bnd (suc m)`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.GadgetSym
  (I : Inputs)
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
open Inputs I

module CW (m : ℕ) (b : Bnd m) = CalcW m (f4 m b) (f5 m) (tr m b)
module SY (m : ℕ) (b : Bnd (suc m)) =
  SwapSym m (f4 m (down b)) (f5 m) (tr m (down b)) (f4 (suc m) b) (f5 (suc m)) (tr (suc m) b)

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

inv-gad : ∀ V m → Bnd m → (₄₊ m) ⊢ᵧ gad V m • gad⁻ V m ≈ ε
inv-gad V zero    _ = embed (inv V)
inv-gad V (suc m) b = CW.transport⁰ m (down b) (inv-gad V m (down b))

inv-gad′ : ∀ V m → Bnd m → (₄₊ m) ⊢ᵧ gad⁻ V m • gad V m ≈ ε
inv-gad′ V zero    _ = embed (inv′ V)
inv-gad′ V (suc m) b = CW.transport⁰ m (down b) (inv-gad′ V m (down b))

-- The decompositions, on every width.
dec-ppW : ∀ m → Bnd m → (₄₊ m) ⊢ᵧ gad⁻ kpp m ≈ gad⁻ krot m • S³ • gad krot m • S
dec-ppW zero    _ = embed dec-pp⁻
dec-ppW (suc m) b =
  SY.tw-step m b (gad⁻ kpp m) (gad⁻ krot m) (gad krot m) S S³ (dec-ppW m (down b)) (S-inv m) (S-inv′ m)

dec-kiW : ∀ m → Bnd m → (₄₊ m) ⊢ᵧ gad⁻ kki m ≈ (gad kki m • S³ • gad⁻ kki m • S) • gad⁻ kpp m
dec-kiW zero    _ = embed dec-ki⁻
dec-kiW (suc m) b =
  PB.trans (CW.transport⁰ m (down b) (dec-kiW m (down b)))
           (PB.cong (CW.tw-top′ m (down b) (gad⁻ kki m) (gad kki m) S S³ (S-inv m) (S-inv′ m)) PB.refl)

dec-rotW : ∀ m → Bnd m → (₄₊ m) ⊢ᵧ gad krot m ≈ gad⁻ kki m • gad kpp m • gad kki m
dec-rotW zero    _ = embed dec-rot
dec-rotW (suc m) b = CW.transport⁰ m (down b) (dec-rotW m (down b))

------------------------------------------------------------------------
-- The symmetry of the two top controls

private
  λλ : ∀ {m} → Circuit (₄₊ m) → Circuit (suc (suc (₄₊ m)))
  λλ x = λ⁰ʷ (λ⁰ʷ x)

  tr2 : ∀ m → Bnd (suc m) → ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (suc (₄₊ m))) ⊢ᵧ λλ u ≈ λλ v
  tr2 m b e = CW.transport⁰ (suc m) b (CW.transport⁰ m (down b) e)

  ss-≈ : ∀ m (b : Bnd (suc m)) {x y} → (suc (suc (₄₊ m))) ⊢ᵧ x ≈ y → SY.SS m b x → SY.SS m b y
  ss-≈ m b e s = PB.trans (PB.cong PB.refl (PB.cong (PB.sym e) PB.refl)) (PB.trans s e)

module _ (sS : ∀ m (b : Bnd (suc m)) → SY.SS m b (λ⁰ʷ (λ⁰ʷ (S {₃₊ m})))) where

  private
    module _ (m : ℕ) (b : Bnd (suc m)) where
      b′ : Bnd m
      b′ = down b

      ss-S³ : SY.SS m b (λλ (S³ {₃₊ m}))
      ss-S³ = SY.ss-• m b (sS m b) (SY.ss-• m b (sS m b) (sS m b))

      ss-pp⁻ : SY.SS m b (λλ (gad⁻ kpp m))
      ss-pp⁻ = SY.swapsym-tw m b (gad⁻ kpp m) (gad⁻ krot m) (gad krot m) S S³
                 (dec-ppW m b′) (inv-gad krot m b′) (inv-gad′ krot m b′) (sS m b) ss-S³

      ss-pp : SY.SS m b (λλ (gad kpp m))
      ss-pp = SY.ss-inv m b ss-pp⁻ (tr2 m b (inv-gad′ kpp m b′)) (tr2 m b (inv-gad kpp m b′))

      ss-ki⁻ : SY.SS m b (λλ (gad⁻ kki m))
      ss-ki⁻ =
        ss-≈ m b (PB.sym (tr2 m b (dec-kiW m b′)))
          (SY.ss-• m b (SY.swapsym-tw m b T (gad kki m) (gad⁻ kki m) S S³ PB.refl
                          (inv-gad′ kki m b′) (inv-gad kki m b′) (sS m b) ss-S³)
                       ss-pp⁻)
        where
        T : Circuit (₄₊ m)
        T = gad kki m • S³ • gad⁻ kki m • S

      ss-ki : SY.SS m b (λλ (gad kki m))
      ss-ki = SY.ss-inv m b ss-ki⁻ (tr2 m b (inv-gad′ kki m b′)) (tr2 m b (inv-gad kki m b′))

      ss-rot : SY.SS m b (λλ (gad krot m))
      ss-rot = ss-≈ m b (PB.sym (tr2 m b (dec-rotW m b′))) (SY.ss-• m b ss-ki⁻ (SY.ss-• m b ss-pp ss-ki))

  -- Every gadget, on every width from six on.
  ss-gad : ∀ V m (b : Bnd (suc m)) → SY.SS m b (λ⁰ʷ (λ⁰ʷ (gad V m)))
  ss-gad kpp  m b = ss-pp m b
  ss-gad krot m b = ss-rot m b
  ss-gad kki  m b = ss-ki m b

-- The same from the black doubly controlled S.
ss-gad¹ : (∀ m (b : Bnd (suc m)) → SY.SS m b (λ¹ʷ (λ¹ʷ (S {₃₊ m})))) →
          ∀ V m (b : Bnd (suc m)) → SY.SS m b (λ⁰ʷ (λ⁰ʷ (gad V m)))
ss-gad¹ h = ss-gad (λ m b → SY.ss-λ⁰λ⁰ m b S (h m b))

-- And so from completeness on five wires (Stable.SwapSymS).
ss-gad₅ : Completeᵧ 5 → ∀ V m (b : Bnd (suc m)) → SY.SS m b (λ⁰ʷ (λ⁰ʷ (gad V m)))
ss-gad₅ c₅ = ss-gad¹ (λ m b → SwapSymS.ss-S¹ m (f4 (suc m) b) (f5 (suc m)) (tr (suc m) b) c₅)
