------------------------------------------------------------------------
-- Presentations of groups
--
-- The proof engine at {X, CX, CCX}: letters, and the rules as equations
--
-- Examples.Independence.Engine instantiated at our gates.  The letters
-- are Xₗ, CXₗ, CCXₗ and σₗ, shifted by _↥.  Each rule of the theory and
-- each swap rule is an equation between letter lists on the bottom
-- wires of a circuit of any width (ax-at, Circuit.Prop's pad), and
-- lift⁼ moves it up.  A derivation is `derive l r steps refl`, its
-- steps `perm ys` (the same word up to letters on disjoint wires) and
-- `rw i e` (rewrite at position i by the equation e).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.XCXCCX-4bit.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ public using (ax-at ; lift)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq X-gate   X-gate   = true
  gate-eq CX-gate  CX-gate  = true
  gate-eq CCX-gate CCX-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound X-gate   X-gate   _ = refl
  gate-eq-sound CX-gate  CX-gate  _ = refl
  gate-eq-sound CCX-gate CCX-gate _ = refl

  code : Gate k → ℕ
  code X-gate   = 0
  code CX-gate  = 0
  code CCX-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one () _

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit _SRel,_===_ public

------------------------------------------------------------------------
-- Letters

pattern Xₗ   = gate₁ ⌈ X-gate ⌉
pattern CXₗ  = gate₂ ⌈ CX-gate ⌉
pattern CCXₗ = gate₃ ⌈ CCX-gate ⌉
pattern σₗ   = gate₂ swap

------------------------------------------------------------------------
-- The rules, on the bottom wires of a circuit of any width

r1⁼ : Eqn (₁₊ n)
r1⁼ {n} = eqnʷ (Xₗ ∷ Xₗ ∷ []) [] (ax-at r1 n) refl refl

r2⁼ : Eqn (₂₊ n)
r2⁼ {n} = eqnʷ (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ []) (Xₗ ∷ []) (ax-at r2 n) refl refl

r3⁼ : Eqn (₂₊ n)
r3⁼ {n} = eqnʷ (CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ []) (σₗ ∷ []) (ax-at r3 n) refl refl

r4⁼ : Eqn (₃₊ n)
r4⁼ {n} = eqnʷ (CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ []) (CXₗ ∷ []) (ax-at r4 n) refl refl

r5⁼ : Eqn (₃₊ n)
r5⁼ {n} = eqnʷ (σₗ ↥ ∷ CCXₗ ∷ σₗ ↥ ∷ []) (CCXₗ ∷ []) (ax-at r5 n) refl refl

r6⁼ : Eqn (₃₊ n)
r6⁼ {n} = eqnʷ (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
               (σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ []) (ax-at r6 n) refl refl

r7⁼ : Eqn (₄₊ n)
r7⁼ {n} = eqnʷ (CCXₗ ↥ ∷ CXₗ ∷ CCXₗ ↥ ∷ []) (σₗ ∷ CCXₗ ↥ ∷ σₗ ∷ CXₗ ∷ []) (ax-at r7 n) refl refl

------------------------------------------------------------------------
-- The swap rules

σσ⁼ : Eqn (₂₊ n)
σσ⁼ = eqnʷ (σₗ ∷ σₗ ∷ []) [] (sym-rule σ-inv) refl refl

-- A gate followed by the cycle σ[ k ] is the cycle followed by the gate
-- one wire up.
σX⁼ : Eqn (₂₊ n)
σX⁼ = eqnʷ (Xₗ ∷ σₗ ∷ []) (σₗ ∷ Xₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ X-gate ⌉)) refl refl

σCX⁼ σσσ⁼ : Eqn (₃₊ n)
σCX⁼ = eqnʷ (CXₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ CXₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ ⌈ CX-gate ⌉)) refl refl
σσσ⁼ = eqnʷ (σₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ σₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ swap)) refl refl

σCCX⁼ : Eqn (₄₊ n)
σCCX⁼ = eqnʷ (CCXₗ ∷ σₗ ↥ ↥ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ↥ ∷ σₗ ↥ ∷ σₗ ∷ CCXₗ ↥ ∷ [])
             (sym-rule (σ-nat₃ ⌈ CCX-gate ⌉)) refl refl
