------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the rules on five wires and more
--
-- The rules of Syntactics are sound (Soundness); AX is one evaluation on
-- five wires; and a controlled version of a sound equation is sound,
-- the functor denoting the controlled matrix (Lambda.Semantics), so the
-- control schema is sound at every width.  The congruence is then sound
-- step by step.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Soundness where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

import Data.Nat.Properties as NP
import Presentation.Base as PB
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; by-relator)
open import Examples.Groups.Clifford+CS.SemanticSteps using (same-≡)
open import Examples.Groups.Clifford+CS.Soundness
  using (axiom-sound ; cong↑-sound ; comm₁-sound ; comm₂-sound ; ω↑=ω-sound)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ¹ᵏ-~ ; ⟦•⟧ ; ⟦ε⟧)
open import Examples.Groups.Clifford+CS.Five.Rules

private
  variable
    n : ℕ

  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

------------------------------------------------------------------------
-- The rules

ax-sound : ⟦ AX.l {n} ⟧ ~ ⟦ AX.r {n} ⟧
ax-sound = by-relator (AX.l {0}) (AX.r {0}) Eq.refl Eq.refl (same-≡ (AX.l {0}) (AX.r {0}) Eq.refl)

axiom-soundₓ : {w v : Circuit n} → n XVRel, w === v → ⟦ w ⟧ ~ ⟦ v ⟧
axiom-soundₓ (srelₓ (old a))     = axiom-sound (srel a)
axiom-soundₓ (srelₓ ax)          = ax-sound
axiom-soundₓ (srelₓ (ctl-ax k))  = λ¹ᵏ-~ (suc k) ax-sound
axiom-soundₓ (srelₓ (ctl-lf k))  = λ¹ᵏ-~ (suc k) (axiom-sound (srel lf))
axiom-soundₓ (srelₓ (ctl-hsq k)) = λ¹ᵏ-~ (suc k) (axiom-sound (srel hyb-sq))
axiom-soundₓ (srelₓ (ctl-hyb k)) = λ¹ᵏ-~ (suc k) (axiom-sound (srel hyb-yb))
axiom-soundₓ (cong↑ₓ r)          = cong↑-sound (axiom-soundₓ r)
axiom-soundₓ (comm₁ₓ h g)        = comm₁-sound h g
axiom-soundₓ (comm₂ₓ h g)        = comm₂-sound h g
axiom-soundₓ (ω↑=ωₓ h)           = ω↑=ω-sound h

------------------------------------------------------------------------
-- The congruence

soundₓ : {w v : Circuit n} → n ⊢ₓ w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
soundₓ {w = w} PB.refl = ~-refl ⟦ w ⟧
soundₓ {w = w} {v} (PB.sym e) = ~-sym {s = ⟦ v ⟧} {⟦ w ⟧} (soundₓ e)
soundₓ {w = w} {u} (PB.trans {v = v} e f) = ~-trans {s = ⟦ w ⟧} {⟦ v ⟧} {⟦ u ⟧} (soundₓ e) (soundₓ f)
soundₓ {n} (PB.cong {w = w} {w' = w′} {v = v} {v' = v′} e f) = begin
  ⟦ w • v ⟧          ≈⟨ ⟦•⟧ w v ⟩
  ⟦ w ⟧ ∙ ⟦ v ⟧      ≈⟨ ∙-cong {s = ⟦ w ⟧} {⟦ w′ ⟧} {⟦ v ⟧} {⟦ v′ ⟧} (soundₓ e) (soundₓ f) ⟩
  ⟦ w′ ⟧ ∙ ⟦ v′ ⟧    ≈⟨ ~-sym {s = ⟦ w′ • v′ ⟧} {⟦ w′ ⟧ ∙ ⟦ v′ ⟧} (⟦•⟧ w′ v′) ⟩
  ⟦ w′ • v′ ⟧        ∎
  where open R n
soundₓ {n} (PB.assoc {w = w} {v = v} {u = u}) = begin
  ⟦ (w • v) • u ⟧            ≈⟨ ⟦•⟧ (w • v) u ⟩
  ⟦ w • v ⟧ ∙ ⟦ u ⟧          ≈⟨ ∙-cong {s = ⟦ w • v ⟧} {⟦ w ⟧ ∙ ⟦ v ⟧} {⟦ u ⟧} {⟦ u ⟧} (⟦•⟧ w v) (~-refl ⟦ u ⟧) ⟩
  (⟦ w ⟧ ∙ ⟦ v ⟧) ∙ ⟦ u ⟧    ≈⟨ ∙-assoc ⟦ w ⟧ ⟦ v ⟧ ⟦ u ⟧ ⟩
  ⟦ w ⟧ ∙ (⟦ v ⟧ ∙ ⟦ u ⟧)    ≈⟨ ∙-cong {s = ⟦ w ⟧} {⟦ w ⟧} {⟦ v ⟧ ∙ ⟦ u ⟧} {⟦ v • u ⟧}
                                  (~-refl ⟦ w ⟧) (~-sym {s = ⟦ v • u ⟧} {⟦ v ⟧ ∙ ⟦ u ⟧} (⟦•⟧ v u)) ⟩
  ⟦ w ⟧ ∙ ⟦ v • u ⟧          ≈⟨ ~-sym {s = ⟦ w • (v • u) ⟧} {⟦ w ⟧ ∙ ⟦ v • u ⟧} (⟦•⟧ w (v • u)) ⟩
  ⟦ w • (v • u) ⟧            ∎
  where open R n
soundₓ {n} (PB.left-unit {w = w}) = begin
  ⟦ ε • w ⟧          ≈⟨ ⟦•⟧ ε w ⟩
  ⟦ ε ⟧ ∙ ⟦ w ⟧      ≈⟨ ∙-cong {s = ⟦ ε ⟧} {ε∙} {⟦ w ⟧} {⟦ w ⟧} ⟦ε⟧ (~-refl ⟦ w ⟧) ⟩
  ε∙ ∙ ⟦ w ⟧         ≈⟨ ∙-identityˡ ⟦ w ⟧ ⟩
  ⟦ w ⟧              ∎
  where open R n
soundₓ {n} (PB.right-unit {w = w}) = begin
  ⟦ w • ε ⟧          ≈⟨ ⟦•⟧ w ε ⟩
  ⟦ w ⟧ ∙ ⟦ ε ⟧      ≈⟨ ∙-cong {s = ⟦ w ⟧} {⟦ w ⟧} {⟦ ε ⟧} {ε∙} (~-refl ⟦ w ⟧) ⟦ε⟧ ⟩
  ⟦ w ⟧ ∙ ε∙         ≈⟨ ∙-identityʳ ⟦ w ⟧ ⟩
  ⟦ w ⟧              ∎
  where open R n
soundₓ (PB.axiom a) = axiom-soundₓ a
