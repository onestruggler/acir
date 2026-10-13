------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the rules of Figure 1 for the matrix semantics
--
-- Each rule is checked by evaluation on its own wires, and holds on the
-- bottom wires of every wider circuit by Evaluation.by-fast; the
-- structural rules are the tensor calculus of Semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Soundness where

open import Algebra.Bundles using (Monoid)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics
open import Examples.Groups.Qutrit-Clifford.Soundness.Checks

private
  variable
    n : ℕ
    w v : Circuit n

  ≈-trans' : {s₁ s₂ s₃ : Sc n} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
  ≈-trans' {s₁ = s₁} {s₂} {s₃} = ≈-trans {s₁ = s₁} {s₂} {s₃}

  ≈-sym' : {s s' : Sc n} → s ≈ s' → s' ≈ s
  ≈-sym' {s = s} {s'} = ≈-sym {s = s} {s'}

------------------------------------------------------------------------
-- The rules of Figure 1, by evaluation on their own wires

-- Semantics.lift at a fixed number of wires, its target width written
-- suc (suc …) as the rules' widths are: with k + n there, Agda compares
-- the semantics of the rule's words at two spellings of one width by
-- unfolding them, which costs minutes for the three-qutrit rules.
lift₁ : (l r : Circuit 1) {n : ℕ} {w v : Circuit (₁₊ n)} →
        l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → ⟦ l ⟧ ≈ ⟦ r ⟧ → ⟦ w ⟧ ≈ ⟦ v ⟧
lift₁ = lift

lift₂ : (l r : Circuit 2) {n : ℕ} {w v : Circuit (₂₊ n)} →
        l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → ⟦ l ⟧ ≈ ⟦ r ⟧ → ⟦ w ⟧ ≈ ⟦ v ⟧
lift₂ = lift

lift₃ : (l r : Circuit 3) {n : ℕ} {w v : Circuit (₃₊ n)} →
        l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → ⟦ l ⟧ ≈ ⟦ r ⟧ → ⟦ w ⟧ ≈ ⟦ v ⟧
lift₃ = lift

rule-sound : n QRel, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
rule-sound {w = w} {v} C₁  = lift l₁ r₁ {_} {w} {v} refl refl sound₁
rule-sound {w = w} {v} C₂  = lift₁ l₂ r₂ {_} {w} {v} refl refl sound₂
rule-sound {w = w} {v} C₃  = lift₁ l₃ r₃ {_} {w} {v} refl refl sound₃
rule-sound {w = w} {v} C₄  = lift₁ l₄ r₄ {_} {w} {v} refl refl sound₄
rule-sound {w = w} {v} C₅  = lift₁ l₅ r₅ {_} {w} {v} refl refl sound₅
rule-sound {w = w} {v} C₆  = lift₂ l₆ r₆ {_} {w} {v} refl refl sound₆
rule-sound {w = w} {v} C₇  = lift₂ l₇ r₇ {_} {w} {v} refl refl sound₇
rule-sound {w = w} {v} C₈  = lift₂ l₈ r₈ {_} {w} {v} refl refl sound₈
rule-sound {w = w} {v} C₉  = lift₂ l₉ r₉ {_} {w} {v} refl refl sound₉
rule-sound {w = w} {v} C₁₀ = lift₂ l₁₀ r₁₀ {_} {w} {v} refl refl sound₁₀
rule-sound {w = w} {v} C₁₁ = lift₂ l₁₁ r₁₁ {_} {w} {v} refl refl sound₁₁
rule-sound {w = w} {v} C₁₂ = lift₂ l₁₂ r₁₂ {_} {w} {v} refl refl sound₁₂
rule-sound {w = w} {v} C₁₃ = lift₂ l₁₃ r₁₃ {_} {w} {v} refl refl sound₁₃
rule-sound {w = w} {v} C₁₄ = lift₂ l₁₄ r₁₄ {_} {w} {v} refl refl sound₁₄
rule-sound {w = w} {v} C₁₅ = lift₃ l₁₅ r₁₅ {_} {w} {v} refl refl sound₁₅
rule-sound {w = w} {v} C₁₆ = lift₃ l₁₆ r₁₆ {_} {w} {v} refl refl sound₁₆
rule-sound {w = w} {v} C₁₇ = lift₃ l₁₇ r₁₇ {_} {w} {v} refl refl sound₁₇
rule-sound {w = w} {v} C₁₈ = lift₃ l₁₈ r₁₈ {_} {w} {v} refl refl sound₁₈

------------------------------------------------------------------------
-- Soundness

vrel-sound : n VRel, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
vrel-sound (srel r)                  = rule-sound r
vrel-sound (cong↑ {w = w} {v = v} a) = cong↑-sound {w = w} {v} (vrel-sound a)
vrel-sound (comm₁ h g)               = ≈-sym' {s = ⟦ [ gate₁ h ]ʷ • [ g ↥ ]ʷ ⟧}
                                         {⟦ [ g ↥ ]ʷ • [ gate₁ h ]ʷ ⟧} (comm₁-sound h g)
vrel-sound (comm₂ h g)               = ≈-sym' {s = ⟦ [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ ⟧}
                                         {⟦ [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ⟧} (comm₂-sound h g)
vrel-sound (ω↑=ω h)                  = ω↑=ω-sound h

-- Every derivable equation holds.
sound : n ⊢ w ≈ v → ⟦ w ⟧ ≈ ⟦ v ⟧
sound {w = w} PB.refl          = ≈-refl {s = ⟦ w ⟧}
sound {w = w} {v} (PB.sym e)   = ≈-sym' {s = ⟦ v ⟧} {⟦ w ⟧} (sound e)
sound {w = w} {v} (PB.trans {v = u} e f) =
  ≈-trans' {s₁ = ⟦ w ⟧} {⟦ u ⟧} {⟦ v ⟧} (sound e) (sound f)
sound (PB.cong {w = w} {w' = w'} {v = v} {v' = v'} e f) =
  ∙-cong {s₁ = ⟦ v ⟧} {⟦ v' ⟧} {⟦ w ⟧} {⟦ w' ⟧} (sound f) (sound e)
sound (PB.assoc {w = w} {v = v} {u = u}) =
  ≈-sym' {s = (⟦ u ⟧ ∙ ⟦ v ⟧) ∙ ⟦ w ⟧} {⟦ u ⟧ ∙ (⟦ v ⟧ ∙ ⟦ w ⟧)}
    (Monoid.assoc (monoid _) ⟦ u ⟧ ⟦ v ⟧ ⟦ w ⟧)
sound (PB.left-unit {w = w})  = proj₂ (Monoid.identity (monoid _)) ⟦ w ⟧
sound (PB.right-unit {w = w}) = proj₁ (Monoid.identity (monoid _)) ⟦ w ⟧
sound (PB.axiom a)            = vrel-sound a
