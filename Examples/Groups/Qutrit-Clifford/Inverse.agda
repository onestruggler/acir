------------------------------------------------------------------------
-- Presentations of groups
--
-- The inverse of a qutrit Clifford circuit, as a circuit
--
-- H⁻¹ = H³, S⁻¹ = S², CZ⁻¹ = CZ² and (−ω)⁻¹ = (−ω)⁵, by C₂, C₃, C₆
-- and C₁; the inverse of a word is the inverses of its letters in
-- reverse.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Inverse where

open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Reasoning using (module Width ; lift)

private
  variable
    n : ℕ

invL : Gen n → Circuit n
invL (gate₀ ν-gate)  = ν ^ 5
invL (gate₁ H-gate)  = H • H • H
invL (gate₁ S-gate)  = S • S
invL (gate₂ CZ-gate) = CZ • CZ
invL (g ↥)           = invL g ↑

inv : Circuit n → Circuit n
inv [ g ]ʷ  = invL g
inv ε       = ε
inv (w • v) = inv v • inv w

invL-r : (g : Gen n) → n ⊢ [ g ]ʷ • invL g ≈ ε
invL-r (gate₀ ν-gate)  = PB.axiom (srel C₁)
invL-r (gate₁ H-gate)  = PB.axiom (srel C₂)
invL-r (gate₁ S-gate)  = PB.axiom (srel C₃)
invL-r (gate₂ CZ-gate) = PB.axiom (srel C₆)
invL-r (g ↥)           = lift (invL-r g)

invL-l : (g : Gen n) → n ⊢ invL g • [ g ]ʷ ≈ ε
invL-l {n} (gate₀ ν-gate)  = PB.trans (Width.by-assoc n Eq.refl) (PB.axiom (srel C₁))
invL-l {n} (gate₁ H-gate)  = PB.trans (Width.by-assoc n Eq.refl) (PB.axiom (srel C₂))
invL-l {n} (gate₁ S-gate)  = PB.trans (Width.by-assoc n Eq.refl) (PB.axiom (srel C₃))
invL-l {n} (gate₂ CZ-gate) = PB.trans (Width.by-assoc n Eq.refl) (PB.axiom (srel C₆))
invL-l (g ↥)               = lift (invL-l g)

-- A circuit followed by its inverse, or preceded by it, is the identity.
inv-r : (w : Circuit n) → n ⊢ w • inv w ≈ ε
inv-r [ g ]ʷ      = invL-r g
inv-r {n} ε       = Width.left-unit
inv-r {n} (w • v) = begin
  (w • v) • (inv v • inv w)   ≈⟨ assoc ⟩
  w • v • inv v • inv w       ≈⟨ back w (sym assoc) ⟩
  w • (v • inv v) • inv w     ≈⟨ back w (front (inv w) (inv-r v)) ⟩
  w • ε • inv w               ≈⟨ back w left-unit ⟩
  w • inv w                   ≈⟨ inv-r w ⟩
  ε                           ∎
  where open Width n

inv-l : (w : Circuit n) → n ⊢ inv w • w ≈ ε
inv-l [ g ]ʷ      = invL-l g
inv-l {n} ε       = Width.left-unit
inv-l {n} (w • v) = begin
  (inv v • inv w) • (w • v)   ≈⟨ assoc ⟩
  inv v • inv w • w • v       ≈⟨ back (inv v) (sym assoc) ⟩
  inv v • (inv w • w) • v     ≈⟨ back (inv v) (front v (inv-l w)) ⟩
  inv v • ε • v               ≈⟨ back (inv v) left-unit ⟩
  inv v • v                   ≈⟨ inv-l v ⟩
  ε                           ∎
  where open Width n
