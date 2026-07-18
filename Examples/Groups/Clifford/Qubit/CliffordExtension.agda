------------------------------------------------------------------------
-- Presentations of groups
--
-- The projection Clifford-group ↠ Sp(2n,2) of the qubit Clifford
-- extension (p = 2).
--
-- proj [w] = ⟦ w ⟧ (the symplectic map act w).  Well-defined on the
-- Clifford group's equality (equal P4-action ⇒ equal Pauli component ⇒
-- equal symplectic map), a group homomorphism, and surjective (from the
-- repo's Symplectic.Surjectivity).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Clifford.Qubit.CliffordExtension where

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
  using (module Symplectic-Derived-Gen)
open Symplectic-Derived-Gen using (Gen)
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Properties p-2 p-prime using (act)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; _∘ˢ_ ; εˢ ; Sp-group)
open import Examples.Groups.Symplectic.ExtendedGate.Surjectivity p-2 p-prime using (⟦_⟧)

open import Examples.Groups.Clifford.Qubit.SignedPauli using (P4Carrier)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (cact)
open import Examples.Groups.Clifford.Qubit.CliffordGroup using (_≈ᶜ_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The Pauli component of the P4-action is the symplectic action

cact-proj₂ : (w : Word (Gen n)) (x : P4Carrier n) →
             proj₂ (cact w x) ≡ act w (proj₂ x)
cact-proj₂ [ g ]ʷ  (s , P) = Eq.refl
cact-proj₂ ε       (s , P) = Eq.refl
cact-proj₂ (w • v) x =
  Eq.trans (cact-proj₂ w (cact v x)) (Eq.cong (act w) (cact-proj₂ v x))

------------------------------------------------------------------------
-- The projection to Sp(2n,2)

proj : Word (Gen n) → Symplectic n
proj = ⟦_⟧

-- Well-defined: equal P4-action ⇒ equal symplectic map.
proj-cong : {w v : Word (Gen n)} → w ≈ᶜ v → proj w ≈ˢ proj v
proj-cong {w = w} {v} w≈v P =
  Eq.trans (Eq.sym (cact-proj₂ w (₀ , P)))
    (Eq.trans (Eq.cong proj₂ (w≈v (₀ , P))) (cact-proj₂ v (₀ , P)))

-- Homomorphism: act (w • v) = act w ∘ act v holds definitionally.
proj-∙ : (w v : Word (Gen n)) → proj (w • v) ≈ˢ (proj w ∘ˢ proj v)
proj-∙ w v P = Eq.refl

proj-ε : proj {n} ε ≈ˢ εˢ
proj-ε P = Eq.refl
