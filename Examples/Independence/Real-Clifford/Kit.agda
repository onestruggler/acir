------------------------------------------------------------------------
-- Presentations of groups
--
-- The proof engine at RCliff₂: letters, and the axioms as equations
--
-- Examples.Independence.Engine instantiated at the gates of RCliff₂.
-- The letters are mₗ (the scalar −1), Hₗ, Zₗ, CXₗ and σₗ, shifted by
-- _↥; a scalar is never shifted.  Each axiom of RCliff₂ and each
-- symmetry rule is an equation between letter lists on the bottom
-- wires of a circuit of any width, and lift⁼ moves it up.  The letter
-- lists are the ones Examples/Independence/gen/rcliff.py spells.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Real-Clifford.Kit where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Independence.Real-Clifford.Syntactics
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (ax-at)

private
  variable
    k n : ℕ

  gate-eq : Gate k → Gate k → Bool
  gate-eq m-gate  m-gate  = true
  gate-eq H-gate  H-gate  = true
  gate-eq H-gate  Z-gate  = false
  gate-eq Z-gate  H-gate  = false
  gate-eq Z-gate  Z-gate  = true
  gate-eq CX-gate CX-gate = true

  gate-eq-sound : (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
  gate-eq-sound m-gate  m-gate  _ = refl
  gate-eq-sound H-gate  H-gate  _ = refl
  gate-eq-sound Z-gate  Z-gate  _ = refl
  gate-eq-sound CX-gate CX-gate _ = refl
  gate-eq-sound H-gate  Z-gate  ()
  gate-eq-sound Z-gate  H-gate  ()

  code : Gate k → ℕ
  code m-gate  = 0
  code H-gate  = 0
  code Z-gate  = 1
  code CX-gate = 0

  one : (h h' : Gate 0) → h ≡ h'
  one m-gate m-gate = refl

open import Examples.Independence.Engine Gate gate-eq gate-eq-sound code one public
open Kit _SRel,_===_ public

------------------------------------------------------------------------
-- Letters

pattern mₗ  = gate₀ ⌈ m-gate ⌉
pattern Hₗ  = gate₁ ⌈ H-gate ⌉
pattern Zₗ  = gate₁ ⌈ Z-gate ⌉
pattern CXₗ = gate₂ ⌈ CX-gate ⌉
pattern σₗ  = gate₂ swap

------------------------------------------------------------------------
-- The axioms

−²⁼ : Eqn n
−²⁼ {n} = eqnʷ (mₗ ∷ mₗ ∷ []) [] (ax-at −² n) refl refl

H²⁼ : Eqn (₁₊ n)
H²⁼ {n} = eqnʷ (Hₗ ∷ Hₗ ∷ []) [] (ax-at H² n) refl refl

Z²⁼ : Eqn (₁₊ n)
Z²⁼ {n} = eqnʷ (Zₗ ∷ Zₗ ∷ []) [] (ax-at Z² n) refl refl

F⁼ : Eqn (₁₊ n)
F⁼ {n} = eqnʷ (Zₗ ∷ Hₗ ∷ Zₗ ∷ Hₗ ∷ [])
              (mₗ ∷ Hₗ ∷ Zₗ ∷ Hₗ ∷ Zₗ ∷ []) (ax-at F n) refl refl

CX²⁼ : Eqn (₂₊ n)
CX²⁼ {n} = eqnʷ (CXₗ ∷ CXₗ ∷ []) [] (ax-at CX² n) refl refl

B⁼ : Eqn (₂₊ n)
B⁼ {n} = eqnʷ (CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) (σₗ ∷ CXₗ ∷ []) (ax-at B n) refl refl

ZC⁼ : Eqn (₂₊ n)
ZC⁼ {n} = eqnʷ (Zₗ ∷ CXₗ ∷ Zₗ ∷ []) (CXₗ ∷ Zₗ ↥ ∷ []) (ax-at ZC n) refl refl

CZr⁼ : Eqn (₂₊ n)
CZr⁼ {n} = eqnʷ (Hₗ ↥ ∷ Hₗ ∷ CXₗ ∷ Hₗ ↥ ∷ Hₗ ∷ []) (σₗ ∷ CXₗ ∷ σₗ ∷ [])
                (ax-at CZr n) refl refl

CF⁼ : Eqn (₂₊ n)
CF⁼ {n} = eqnʷ (CXₗ ∷ Hₗ ∷ CXₗ ∷ Zₗ ∷ Hₗ ∷ [])
               (Hₗ ∷ Zₗ ∷ CXₗ ∷ Hₗ ∷ CXₗ ∷ []) (ax-at CF n) refl refl

I⁼ : Eqn (₃₊ n)
I⁼ {n} = eqnʷ (CXₗ ∷ CXₗ ↥ ∷ σₗ ∷ CXₗ ↥ ∷ σₗ ∷ []) (CXₗ ↥ ∷ CXₗ ∷ []) (ax-at I n) refl refl

------------------------------------------------------------------------
-- The symmetry rules

σσ⁼ : Eqn (₂₊ n)
σσ⁼ = eqnʷ (σₗ ∷ σₗ ∷ []) [] (sym-rule σ-inv) refl refl

σH⁼ σZ⁼ : Eqn (₂₊ n)
σH⁼ = eqnʷ (Hₗ ∷ σₗ ∷ []) (σₗ ∷ Hₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ H-gate ⌉)) refl refl
σZ⁼ = eqnʷ (Zₗ ∷ σₗ ∷ []) (σₗ ∷ Zₗ ↥ ∷ []) (sym-rule (σ-nat₁ ⌈ Z-gate ⌉)) refl refl

σCX⁼ σσσ⁼ : Eqn (₃₊ n)
σCX⁼ = eqnʷ (CXₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ CXₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ ⌈ CX-gate ⌉)) refl refl
σσσ⁼ = eqnʷ (σₗ ∷ σₗ ↥ ∷ σₗ ∷ []) (σₗ ↥ ∷ σₗ ∷ σₗ ↥ ∷ [])
            (sym-rule (σ-nat₂ swap)) refl refl
