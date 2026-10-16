------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits: Blake's presentation of the affine group at p = 2
--
-- Blake's Aff_d (Qupit-Phase-Affine, level 0) at p = 2 has the gates X,
-- the multipliers (only the trivial one, as F* = {1}), CX (wire 1 added
-- into wire 0) and SWAP, and rules on at most three wires; it is
-- complete at every width (Qupit-Phase-Affine.Completeness.Aff).  `τ`
-- reads its circuits as ours (X, ε, CX₁₀, Swap), and every rule
-- instance becomes a derivation here: a rule is one evaluation on its
-- (at most three) wires with completeness there (SemanticSteps.Below),
-- the structural rules are Five.Low's commutations.  So two affine
-- circuits with the same affine map are equal in our theory, at every
-- width (`affine-complete`) — what the independence of the decoding on
-- five wires and more rests on.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Affine where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Empty using (⊥)
import Data.Empty as E
open import Data.Fin.Base using (zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≤_)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Completeness using (complete₁ ; complete₂ ; complete₃)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; module Below)
open import Examples.Groups.Clifford+CS.Place using (↑ᵏ-↑)
open import Examples.Groups.Clifford+CS.Five.Low using (lowᵏ)

import Examples.Groups.Qupit-Phase-Affine.Field 0 prime[2] as BF
import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
import Examples.Groups.Qupit-Phase-Affine.Interpretation 0 prime[2] 0 as BI
import Examples.Groups.Qupit-Phase-Affine.Semantics 0 prime[2] as BS
import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] as BC

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The translation

τg : B.Gen n → Circuit n
τg (B.gate₀ _)               = ε
τg (B.gate₁ B.X-gate)        = X
τg (B.gate₁ (B.M-gate _ _))  = ε
τg (B.gate₁ (B.Z-gate _))    = ε
τg (B.gate₁ (B.S-gate _))    = ε
τg (B.gate₁ (B.T-gate _))    = ε
τg (B.gate₂ B.CX-gate)       = CX₁₀
τg (B.gate₂ B.SWAP-gate)     = Swap
τg (g B.↥)                   = τg g ↑

τ : B.Circuit n → Circuit n
τ [ g ]ʷ  = τg g
τ ε       = ε
τ (u • v) = τ u • τ v

private
  τ-↑ : (w : B.Circuit n) → τ (w B.↑) ≡ τ w ↑
  τ-↑ [ g ]ʷ  = Eq.refl
  τ-↑ ε       = Eq.refl
  τ-↑ (u • v) = Eq.cong₂ _•_ (τ-↑ u) (τ-↑ v)

------------------------------------------------------------------------
-- Arithmetic at p = 2

private
  opaque
    unfolding BF.-_
    neg1 : BF.- BF.1F ≡ BF.1F
    neg1 = Eq.refl

------------------------------------------------------------------------
-- The rules

private
  no-lv : ∀ {k} → suc k ≤ 0 → ⊥
  no-lv ()

  closed₁ : (u v : Circuit 1) → Same u v → (₁₊ n) ⊢ u ↓ᵏ n ≈ v ↓ᵏ n
  closed₁ u v e = Below.by-sem 1 complete₁ u v e
  closed₂ : (u v : Circuit 2) → Same u v → (₂₊ n) ⊢ u ↓ᵏ n ≈ v ↓ᵏ n
  closed₂ u v e = Below.by-sem 2 complete₂ u v e
  closed₃ : (u v : Circuit 3) → Same u v → (₃₊ n) ⊢ u ↓ᵏ n ≈ v ↓ᵏ n
  closed₃ u v e = Below.by-sem 3 complete₃ u v e

  ax3-τ : (x : BF.F*) (m : BF.F) → m ≡ BF.1F →
          (₁₊ n) ⊢ τ (B.X B.^ᶠ proj₁ x • B.M⟨ x ⟩ • B.X B.^ᶠ m) ≈ τ (B.M⟨ x ⟩)
  ax3-τ (zero , nz) _ _ = E.⊥-elim (nz Eq.refl)
  ax3-τ (suc zero , _) .BF.1F Eq.refl = closed₁ (X • (ε • X)) ε Eq.refl

  ax4-τ : (x : BF.F*) → (₂₊ n) ⊢ τ (B.CX • B.M⟨ x ⟩ B.↑) ≈ τ (B.M⟨ x ⟩ B.↑ • B.CX B.^ᶠ proj₁ x)
  ax4-τ (zero , nz) = E.⊥-elim (nz Eq.refl)
  ax4-τ (suc zero , _) = closed₂ (CX₁₀ • ε) (ε • CX₁₀) Eq.refl

  ax5-τ : (x : BF.F*) (m : BF.F) → m ≡ BF.1F → proj₁ x ≡ BF.1F →
          (₂₊ n) ⊢ τ (B.CX B.^ᶠ m • B.M⟨ x ⟩ • B.CX) ≈ τ (B.M⟨ x ⟩)
  ax5-τ (zero , nz) _ _ _ = E.⊥-elim (nz Eq.refl)
  ax5-τ (suc zero , _) .BF.1F Eq.refl _ = closed₂ (CX₁₀ • (ε • CX₁₀)) ε Eq.refl

  ax7-τ : (m : BF.F) → m ≡ BF.1F →
          (₂₊ n) ⊢ τ B.SWAP ≈
          τ (B.M⟨ BF.-1* ⟩ B.↑ • (B.SWAP • B.CX B.^ᶠ m • B.SWAP) • B.CX • (B.SWAP • B.CX B.^ᶠ m • B.SWAP))
  ax7-τ .BF.1F Eq.refl =
    closed₂ Swap (ε • (Swap • CX₁₀ • Swap) • CX₁₀ • (Swap • CX₁₀ • Swap)) Eq.refl

  unit-x : (x : BF.F*) → proj₁ x ≡ BF.1F
  unit-x (zero , nz)     = E.⊥-elim (nz Eq.refl)
  unit-x (suc zero , _)  = Eq.refl

  neg-x : (x : BF.F*) → BF.- proj₁ x ≡ BF.1F
  neg-x x = Eq.trans (Eq.cong BF.-_ (unit-x x)) neg1

aff-rule : ∀ {w v} → n B.SRel, w === v → n ⊢ τ w ≈ τ v
aff-rule B.ax1           = PB.refl
aff-rule (B.ax2 x y)     = PB.left-unit
aff-rule (B.ax3 x)       = ax3-τ x (BF.- BF.1F) neg1
aff-rule (B.ax4 x)       = ax4-τ x
aff-rule (B.ax5 x)       = ax5-τ x (BF.- proj₁ x) (neg-x x) (unit-x x)
aff-rule B.ax6           = closed₂ (CX₁₀ • X ↑) (X • X ↑ • CX₁₀) Eq.refl
aff-rule B.ax7           = ax7-τ (BF.- BF.1F) neg1
aff-rule B.ax8           = closed₃ (CX₁₀ ↑ • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) (CX₁₀ • CX₁₀ ↑) Eq.refl
aff-rule B.swap-order    = closed₂ (Swap • Swap) ε Eq.refl
aff-rule B.swap-braid    = closed₃ (Swap • Swap ↑ • Swap) (Swap ↑ • Swap • Swap ↑) Eq.refl
aff-rule B.swap-X        = closed₂ (X • Swap) (Swap • X ↑) Eq.refl
aff-rule (B.swap-M a nz) = closed₂ (ε • Swap) (Swap • ε) Eq.refl
aff-rule (B.swap-Z h)    = closed₂ (ε • Swap) (Swap • ε) Eq.refl
aff-rule (B.swap-S h)    = closed₂ (ε • Swap) (Swap • ε) Eq.refl
aff-rule (B.swap-T h)    = closed₂ (ε • Swap) (Swap • ε) Eq.refl
aff-rule B.swap-CX       = closed₃ (CX₁₀ • Swap ↑ • Swap) (Swap ↑ • Swap • CX₁₀ ↑) Eq.refl
aff-rule (B.ax19 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax20 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax21 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax22 h _)    = ⊥-elim (no-lv h)
aff-rule (B.ax23 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax24 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax25 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax26 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax27 h _)    = ⊥-elim (no-lv h)
aff-rule (B.ax28 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax29 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax30 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax31 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax32 h _)    = ⊥-elim (no-lv h)
aff-rule (B.ax33 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax34 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax35 h _)    = ⊥-elim (no-lv h)
aff-rule (B.ax36 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax37 h _)    = ⊥-elim (no-lv h)
aff-rule (B.ax38 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax39 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax40 h _)    = ⊥-elim (no-lv h)
aff-rule (B.ax41 h)      = ⊥-elim (no-lv h)
aff-rule (B.ax42 h)      = ⊥-elim (no-lv h)

------------------------------------------------------------------------
-- Derivations

aff-ax : ∀ {w v} → n B.VRel, w === v → n ⊢ τ w ≈ τ v
aff-ax (B.srel r) = aff-rule r
aff-ax (B.cong↑ {w = w} {v = v} a) =
  Eq.subst₂ (_ ⊢_≈_) (Eq.sym (τ-↑ w)) (Eq.sym (τ-↑ v)) (lemma-cong↑ (τ w) (τ v) (aff-ax a))
aff-ax (B.comm₁ B.X-gate g)       = PB.sym (lowᵏ 1 X (τg g))
aff-ax (B.comm₁ (B.M-gate _ _) g) = PB.sym (lowᵏ 1 ε (τg g))
aff-ax (B.comm₁ (B.Z-gate _) g)   = PB.sym (lowᵏ 1 ε (τg g))
aff-ax (B.comm₁ (B.S-gate _) g)   = PB.sym (lowᵏ 1 ε (τg g))
aff-ax (B.comm₁ (B.T-gate _) g)   = PB.sym (lowᵏ 1 ε (τg g))
aff-ax {₂₊ n} (B.comm₂ B.CX-gate g) =
  Eq.subst (λ x → (₂₊ n) ⊢ x • CX₁₀ ≈ CX₁₀ • x) (Eq.sym (↑ᵏ-↑ (τg g) 1)) (PB.sym (lowᵏ 2 CX₁₀ (τg g)))
aff-ax {₂₊ n} (B.comm₂ B.SWAP-gate g) =
  Eq.subst (λ x → (₂₊ n) ⊢ x • Swap ≈ Swap • x) (Eq.sym (↑ᵏ-↑ (τg g) 1)) (PB.sym (lowᵏ 2 Swap (τg g)))
aff-ax (B.ω↑=ω h) = PB.refl

aff⇒ : ∀ {w v : B.Circuit n} → n B.⊢ w ≈ v → n ⊢ τ w ≈ τ v
aff⇒ PB.refl         = PB.refl
aff⇒ (PB.sym e)      = PB.sym (aff⇒ e)
aff⇒ (PB.trans e f)  = PB.trans (aff⇒ e) (aff⇒ f)
aff⇒ (PB.cong e f)   = PB.cong (aff⇒ e) (aff⇒ f)
aff⇒ PB.assoc        = PB.assoc
aff⇒ PB.left-unit    = PB.left-unit
aff⇒ PB.right-unit   = PB.right-unit
aff⇒ (PB.axiom a)    = aff-ax a

-- Two affine circuits with the same affine map are equal.
affine-complete : ∀ {w v : B.Circuit n} → BI.⟦ w ⟧ BS.≐ BI.⟦ v ⟧ → n ⊢ τ w ≈ τ v
affine-complete {n} e = aff⇒ (BC.completeness n e)
