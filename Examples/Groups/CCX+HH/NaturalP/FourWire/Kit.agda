------------------------------------------------------------------------
-- Presentations of groups
--
-- Tools for derivations on four wires.
--
-- `fast₃` decides an equation on three wires by its matrix, through
-- the completeness of the rules on three wires, the matrices compared
-- by integer row actions (Natural.ThreeWire.Fast).  Every generator is
-- an involution (`gen-invol`), so the reverse of a word is an inverse
-- (`inv-right`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.FourWire.Kit where

open import Data.Bool.Base using (true)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

import Examples.Groups.CCX+HH.NaturalP.Syntactics as NP
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Three using (complete₃)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fast using (fastCheck ; fast-sound)

-- Three wires, decided by integer row actions.
fast₃ : (u v : S.Circuit 3) → fastCheck (τ u) (τ v) ≡ true → 3 S.⊢ u ≈ v
fast₃ u v h = complete₃ (fast-sound (τ u) (τ v) h)

------------------------------------------------------------------------
-- Inverses

gen-invol : ∀ {n} (g : S.Gen n) → n S.⊢ [ g ]ʷ • [ g ]ʷ ≈ ε
gen-invol (S.gate₀ ())
gen-invol (S.gate₁ S.X-gate)   = PB.axiom (S.srel (S.srel (S.np NP.X²)))
gen-invol (S.gate₂ S.CX-gate)  = PB.axiom (S.srel (S.srel (S.np NP.CX²)))
gen-invol (S.gate₂ S.HH-gate)  = PB.axiom (S.srel (S.srel (S.np NP.HH²)))
gen-invol (S.gate₂ S.SW-gate)  = PB.axiom (S.srel (S.σrel S.σ-inv))
gen-invol (S.gate₃ S.CCX-gate) = PB.axiom (S.srel (S.srel (S.np NP.CCX²)))
gen-invol (g S.↥)              = S.lemma-cong↑ _ _ (gen-invol g)

-- The reverse of a word.
inv : ∀ {n} → S.Circuit n → S.Circuit n
inv [ g ]ʷ  = [ g ]ʷ
inv ε       = ε
inv (u • v) = inv v • inv u

inv-inv : ∀ {n} (w : S.Circuit n) → inv (inv w) ≡ w
inv-inv [ g ]ʷ  = Eq.refl
inv-inv ε       = Eq.refl
inv-inv (u • v) = Eq.cong₂ _•_ (inv-inv u) (inv-inv v)

inv-right : ∀ {n} (w : S.Circuit n) → n S.⊢ w • inv w ≈ ε
inv-right [ g ]ʷ  = gen-invol g
inv-right ε       = PB.left-unit
inv-right (u • v) =
  PB.trans PB.assoc (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (inv-right v) PB.refl) PB.left-unit))) (inv-right u))

inv-left : ∀ {n} (w : S.Circuit n) → n S.⊢ inv w • w ≈ ε
inv-left w = Eq.subst (λ x → _ S.⊢ inv w • x ≈ ε) (inv-inv w) (inv-right (inv w))

------------------------------------------------------------------------
-- Closing relators

module _ {n : ℕ} where

  open PB (n S.VRel,_===_) using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  -- Two commuting words close a commutator.
  comm-close : ∀ (a b : S.Circuit n) → n S.⊢ a • b ≈ b • a →
               n S.⊢ (a • b) • (inv a • inv b) ≈ ε
  comm-close a b ab =
    trans (cong ab refl) (trans assoc (trans (cong refl (trans (sym assoc)
      (trans (cong (inv-right a) refl) left-unit))) (inv-right b)))

  -- A conjugation closes: s⁻¹ a s = b.
  conj-close : ∀ (a s b : S.Circuit n) → n S.⊢ a • s ≈ s • b →
               n S.⊢ inv s • ((a • s) • inv b) ≈ ε
  conj-close a s b eq =
    trans (cong refl (trans (cong eq refl) (trans assoc
      (trans (cong refl (inv-right b)) right-unit)))) (inv-left s)

  -- Commutation with a product.
  comm-• : ∀ {u v b : S.Circuit n} → n S.⊢ u • b ≈ b • u → n S.⊢ v • b ≈ b • v →
           n S.⊢ (u • v) • b ≈ b • (u • v)
  comm-• ub vb =
    trans assoc (trans (cong refl vb) (trans (sym assoc)
      (trans (cong ub refl) assoc)))
