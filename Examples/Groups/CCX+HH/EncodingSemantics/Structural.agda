------------------------------------------------------------------------
-- Presentations of groups
--
-- Symbolic-width correctness of the recursive encoder.  The physical
-- gate actions are the Boolean swaps and the four Hadamard rows, lifted
-- to further wires by independent direct sums on vectors.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH.EncodingSemantics.Structural
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Nat.Base using (ℕ ; zero ; suc)
  renaming (_^_ to _^ℕ_)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tabulate)
open import Relation.Binary.PropositionalEquality
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; _·*·_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction

open Action isCR adjI h
open EmbedAction isCR adjI h using (same-action)
open Blocks isCR adjI h

private variable n : ℕ

State : ℕ → Set
State n = Vec A (2 ^ℕ n)

x₀ : State 1 → State 1
x₀ (a ∷ b ∷ []) = b ∷ a ∷ []

cx₀ : State 2 → State 2
cx₀ (a ∷ b ∷ c ∷ d ∷ []) = a ∷ b ∷ d ∷ c ∷ []

ccx₀ : State 3 → State 3
ccx₀ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ j ∷ []) =
  a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ j ∷ g ∷ []

hh₀ : State 2 → State 2
hh₀ (a ∷ b ∷ c ∷ d ∷ []) =
  rowA a b c d ∷ rowB a b c d ∷ rowC a b c d ∷ rowD a b c d ∷ []

top bottom : (State n → State n) → State (suc n) → State (suc n)
top {n} f = parallel (contiguous (2 ^ℕ n)) f f
bottom {n} f = parallel (alternating (2 ^ℕ n)) f f

x : (n : ℕ) → State (suc n) → State (suc n)
x zero = x₀
x (suc n) = top {suc n} (x n)

cx hh : (n : ℕ) → State (suc (suc n)) → State (suc (suc n))
cx zero = cx₀
cx (suc n) = top {suc (suc n)} (cx n)
hh zero = hh₀
hh (suc n) = top {suc (suc n)} (hh n)

ccx : (n : ℕ) → State (suc (suc (suc n))) → State (suc (suc (suc n)))
ccx zero = ccx₀
ccx (suc n) = top {suc (suc (suc n))} (ccx n)

gate-action : Gen n → State n → State n
gate-action (gate₀ ())
gate-action (gate₁ {n} X-gate) = x n
gate-action (gate₂ {n} CX-gate) = cx n
gate-action (gate₂ {n} HH-gate) = hh n
gate-action (gate₃ {n} CCX-gate) = ccx n
gate-action (_↥ {n} g) = bottom {n} (gate-action g)

private
  copy-correct : ∀ {m n} (p : Partition m n) w f →
    (∀ v → actVʷ w v ≡ f v) → ∀ v →
    actVʷ (E.copy p w) v ≡ parallel p f f v
  copy-correct p w f eq v = trans (encode-parallel-correct p w w v)
    (parallel-cong p eq eq v)

  opaque
    unfolding actV set₁ set₂

    x₀-correct : ∀ v → actVʷ (E.X-block 0) v ≡ x₀ v
    x₀-correct (a ∷ b ∷ []) = refl

    cx₀-correct : ∀ v → actVʷ (E.CX-block 0) v ≡ cx₀ v
    cx₀-correct (a ∷ b ∷ c ∷ d ∷ []) = refl

    ccx₀-correct : ∀ v → actVʷ (E.CCX-block 0) v ≡ ccx₀ v
    ccx₀-correct (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ j ∷ []) = refl

    hh₀-correct : ∀ v → actVʷ (E.HH-block 0) v ≡ hh₀ v
    hh₀-correct (a ∷ b ∷ c ∷ d ∷ []) = refl

  x-correct : ∀ n v → actVʷ (E.X-block n) v ≡ x n v
  x-correct zero = x₀-correct
  x-correct (suc n) = copy-correct (contiguous _) (E.X-block n) (x n) (x-correct n)

  cx-correct : ∀ n v → actVʷ (E.CX-block n) v ≡ cx n v
  cx-correct zero = cx₀-correct
  cx-correct (suc n) = copy-correct (contiguous _) (E.CX-block n) (cx n) (cx-correct n)

  ccx-correct : ∀ n v → actVʷ (E.CCX-block n) v ≡ ccx n v
  ccx-correct zero = ccx₀-correct
  ccx-correct (suc n) = copy-correct (contiguous _) (E.CCX-block n) (ccx n) (ccx-correct n)

  hh-correct : ∀ n v → actVʷ (E.HH-block n) v ≡ hh n v
  hh-correct zero = hh₀-correct
  hh-correct (suc n) = copy-correct (contiguous _) (E.HH-block n) (hh n) (hh-correct n)

encoding-correct-action : (g : Gen n) → ∀ v → actVʷ (E.e g) v ≡ gate-action g v
encoding-correct-action (gate₀ ())
encoding-correct-action (gate₁ {n} X-gate) = x-correct n
encoding-correct-action (gate₂ {n} CX-gate) = cx-correct n
encoding-correct-action (gate₂ {n} HH-gate) = hh-correct n
encoding-correct-action (gate₃ {n} CCX-gate) = ccx-correct n
encoding-correct-action (_↥ {n} g) = copy-correct (alternating (2 ^ℕ n))
  (E.e g) (gate-action g) (encoding-correct-action g)

-- The columns are the images of the computational basis vectors.
gate-matrix : Gen n → Matrix (2 ^ℕ n) (2 ^ℕ n) A
gate-matrix g = Matrix' (tabulate λ j → gate-action g (col 𝕀 j))

interpret : Circuit n → Matrix (2 ^ℕ n) (2 ^ℕ n) A
interpret [ g ]ʷ = gate-matrix g
interpret ε = 𝕀
interpret (u • v) = interpret u ·*· interpret v

encoding-correct-gate : (g : Gen n) → ⟦ E.e g ⟧ᵐ ≡ gate-matrix g
encoding-correct-gate g = col-ext λ j →
  trans (col-actMʷ (E.e g) 𝕀 j)
    (trans (encoding-correct-action g (col 𝕀 j))
      (sym (!-tabulate (λ k → gate-action g (col 𝕀 k)) j)))

encoding-correct : (w : Circuit n) → ⟦ E.encode w ⟧ᵐ ≡ interpret w
encoding-correct [ g ]ʷ = encoding-correct-gate g
encoding-correct ε = refl
encoding-correct (u • v) = trans (⟦•⟧ᵐ (E.encode u) (E.encode v))
  (cong₂ _·*·_ (encoding-correct u) (encoding-correct v))
