------------------------------------------------------------------------
-- Presentations of groups
--
-- Equations of Natural on three wires for the generated derivations.
--
-- `free01 u v` and `free12 u v` are the equation between two two-wire
-- words with one matrix, on the wires 0, 1 and on the wires 1, 2
-- (completeness on two wires, Widen); `comm⁼ a b` swaps two gates on
-- disjoint wires.  The rules, involutions and lifts are Natural.Axioms'
-- and Natural.Engine's.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit where

open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.Natural.Syntactics public
open import Examples.Groups.CCX+HH.Syntactics using (_↓ᵏ_ ; _↧ᵏ_)
open import Examples.Groups.CCX+HH.Natural.Engine public
  using (Eqn ; eqn ; lhs ; rhs ; prf ; ⟪_⟫ ; Step ; perm ; rw ; derive ; sym⁼ ; lift⁼)
open import Examples.Groups.CCX+HH.Natural.Axioms public
import Examples.Groups.CCX+HH.Semantics as Sem
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Widen using (two₀₁ ; two₁₂)

private
  ⟪map⟫ : ∀ {m k} (f : Gen m → Gen k) (u : List (Gen m)) → ⟪ map f u ⟫ ≡ wmap f ⟪ u ⟫
  ⟪map⟫ f []       = Eq.refl
  ⟪map⟫ f (x ∷ xs) = Eq.cong ([ f x ]ʷ •_) (⟪map⟫ f xs)

  ≡→≈ : ∀ {u v : Circuit 3} → u ≡ v → 3 ⊢ u ≈ v
  ≡→≈ Eq.refl = PB.refl

down : Gen 2 → Gen 3
down g = g ↧ᵏ 1

up : Gen 2 → Gen 3
up g = g ↥

free01 : (u v : List (Gen 2)) → Sem.interpret ⟪ u ⟫ ≡ Sem.interpret ⟪ v ⟫ → Eqn 3
free01 u v h = eqn (map down u) (map down v)
  (PB.trans (≡→≈ (⟪map⟫ down u)) (PB.trans (two₀₁ {⟪ u ⟫} {⟪ v ⟫} h)
    (≡→≈ (Eq.sym (⟪map⟫ down v)))))

free12 : (u v : List (Gen 2)) → Sem.interpret ⟪ u ⟫ ≡ Sem.interpret ⟪ v ⟫ → Eqn 3
free12 u v h = eqn (map up u) (map up v)
  (PB.trans (≡→≈ (⟪map⟫ up u)) (PB.trans (two₁₂ {⟪ u ⟫} {⟪ v ⟫} h)
    (≡→≈ (Eq.sym (⟪map⟫ up v)))))

-- Two-wire words, for the statements of the matrix checks.
⟪_⟫₂ : List (Gen 2) → Circuit 2
⟪_⟫₂ = ⟪_⟫
