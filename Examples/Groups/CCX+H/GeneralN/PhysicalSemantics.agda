------------------------------------------------------------------------
-- Presentations of groups
--
-- Ordinary 2^n by 2^n matrices from independent Boolean and Hadamard
-- tensor actions.  The bridge to the even-size source representation
-- transports only a natural-number equality, with no basis permutation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.PhysicalSemantics where

open import Data.Nat.Base using (ℕ ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Vec.Base using (Vec ; tabulate)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; _·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; RingD)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M

gate-matrix : ∀ {n} → Gen n → Matrix (2 ^ℕ n) (2 ^ℕ n) D
gate-matrix g = Matrix' (tabulate λ j → S.gate-action g (M.col M.𝕀 j))

interpret : ∀ {n} → Circuit n → Matrix (2 ^ℕ n) (2 ^ℕ n) D
interpret [ g ]ʷ = gate-matrix g
interpret ε = M.𝕀
interpret (u • v) = interpret u ·*· interpret v

cast-matrix : ∀ {j l} → j ≡ l → Matrix j j D → Matrix l l D
cast-matrix refl A = A

cast-injective : ∀ {j l} (p : j ≡ l) {A B : Matrix j j D} →
  cast-matrix p A ≡ cast-matrix p B → A ≡ B
cast-injective refl eq = eq

private
  cast-identity : ∀ {j l} (p : j ≡ l) → cast-matrix p M.𝕀 ≡ M.𝕀
  cast-identity refl = refl

  cast-product : ∀ {j l} (p : j ≡ l) (A B : Matrix j j D) →
    cast-matrix p (A ·*· B) ≡ cast-matrix p A ·*· cast-matrix p B
  cast-product refl A B = refl

  cast-action : ∀ {j l} (p : j ≡ l) (f : Vec D j → Vec D j) →
    cast-matrix (sym p) (Matrix' (tabulate λ i →
      S.cast-vector p (f (S.cast-vector (sym p) (M.col M.𝕀 i))))) ≡
    Matrix' (tabulate λ i → f (M.col M.𝕀 i))
  cast-action refl f = refl

module At (n : ℕ) where
  private
    k = 2 ^ℕ n
    dimension : 2 ^ℕ suc n ≡ k * 2
    dimension = NP.*-comm 2 k
    module C = S.At n

  gate-correct : ∀ (g : Gen (suc n)) →
    cast-matrix (sym dimension) (C.gate-matrix g) ≡ gate-matrix g
  gate-correct g = cast-action dimension (S.gate-action g)

  correct : ∀ w → cast-matrix (sym dimension) (C.interpret w) ≡ interpret w
  correct [ g ]ʷ = gate-correct g
  correct ε = cast-identity (sym dimension)
  correct (u • v) = trans (cast-product (sym dimension) (C.interpret u) (C.interpret v))
    (cong₂ _·*·_ (correct u) (correct v))

  forward : ∀ {u v} → C.interpret u ≡ C.interpret v → interpret u ≡ interpret v
  forward {u} {v} eq = trans (sym (correct u))
    (trans (cong (cast-matrix (sym dimension)) eq) (correct v))

  backward : ∀ {u v} → interpret u ≡ interpret v → C.interpret u ≡ C.interpret v
  backward {u} {v} eq = cast-injective (sym dimension)
    (trans (correct u) (trans eq (sym (correct v))))
