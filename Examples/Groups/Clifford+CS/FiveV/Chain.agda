------------------------------------------------------------------------
-- Presentations of groups
--
-- Five-wire derivations as chains of segment replacements over macro
-- letters
--
-- A derivation of the joint paper (scratchpad/joint), lowered to
-- primitive steps (scratchpad/five/lower5.py), is a chain of segment
-- replacements over the letters of Five.Letters (Five.Lines).  The
-- segments' equations: windows (Five.Lits.lwᵢ, Five.Resps.pwᵢ: one
-- evaluation at width four, given completeness there), the structural
-- commutation of letters on the bottom i wires and the top 5 − i (`cᵢ`,
-- from `lowᵏ`, at any split), a scalar passing a letter (`zc`), a scalar
-- respelled at another lift (`uₛ`), a re-bracketing (`by-assoc`, or
-- `refl` for a box and its unfolding), the rule AX at its canonical
-- placement (`axAX`), and earlier lemmas; `scratchpad/five/emit5.py`
-- writes them.  Everything is in the theory of Five.Rules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Chain where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Canonical using (can ; can-≈)
open import Examples.Groups.Clifford+CS.FiveV.Rules

open import Examples.Groups.Clifford+CS.FiveV.Letters public
open import Examples.Groups.Clifford+CS.FiveV.Lines 5 Mac ⟪_⟫ public
private
  variable
    n : ℕ

-- As Place.↑ᵏ-↑; proved here so that the derivations, which import this
-- module, do not load Place and with it the development below four
-- wires.
private
  ↑ᵏ-↑ : (v : Circuit n) (k : ℕ) → (v ↑ᵏ k) ↑ ≡ v ↑ᵏ (suc k)
  ↑ᵏ-↑ [ g ]ʷ  k = Eq.refl
  ↑ᵏ-↑ ε       k = Eq.refl
  ↑ᵏ-↑ (u • v) k = Eq.cong₂ _•_ (↑ᵏ-↑ u k) (↑ᵏ-↑ v k)

------------------------------------------------------------------------
-- The structural commutation at any split, in the old theory

private
  lowᵍ : ∀ k (g : Gen k) (v : Circuit n) →
         (k + n) ⊢ [ g ↧ᵏ n ]ʷ • (v ↑ᵏ k) ≈ (v ↑ᵏ k) • [ g ↧ᵏ n ]ʷ
  lowᵍ k (gate₀ h) v = PB.sym (comm-gate₀-w h (v ↑ᵏ k))
  lowᵍ {n} (suc m) (gate₁ h) v =
    Eq.subst (λ x → (suc (m + n)) ⊢ [ gate₁ h ]ʷ • x ≈ x • [ gate₁ h ]ʷ) (↑ᵏ-↑ v m)
      (PB.sym (comm-gate₁-w↑ h (v ↑ᵏ m)))
  lowᵍ {n} (suc (suc m)) (gate₂ h) v =
    Eq.subst (λ x → (suc (suc (m + n))) ⊢ [ gate₂ h ]ʷ • x ≈ x • [ gate₂ h ]ʷ)
      (Eq.trans (Eq.cong _↑ (↑ᵏ-↑ v m)) (↑ᵏ-↑ v (suc m)))
      (PB.sym (comm-gate₂-w↑↑ h (v ↑ᵏ m)))
  lowᵍ {n} (suc m) (g ↥) v =
    Eq.subst (λ x → (suc (m + n)) ⊢ [ (g ↧ᵏ n) ↥ ]ʷ • x ≈ x • [ (g ↧ᵏ n) ↥ ]ʷ) (↑ᵏ-↑ v m)
      (lemma-cong↑ ([ g ↧ᵏ n ]ʷ • (v ↑ᵏ m)) ((v ↑ᵏ m) • [ g ↧ᵏ n ]ʷ) (lowᵍ m g v))

lowᵏ : ∀ k (u : Circuit k) (v : Circuit n) → (k + n) ⊢ (u ↓ᵏ n) • (v ↑ᵏ k) ≈ (v ↑ᵏ k) • (u ↓ᵏ n)
lowᵏ k [ g ]ʷ v = lowᵍ k g v
lowᵏ {n} k ε v = PB.trans PB.left-unit (PB.sym PB.right-unit)
lowᵏ {n} k (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • (v ↑ᵏ k)   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • (v ↑ᵏ k))   ≈⟨ back _ (lowᵏ k t v) ⟩
  (u ↓ᵏ n) • ((v ↑ᵏ k) • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • (v ↑ᵏ k)) • (t ↓ᵏ n)   ≈⟨ front _ (lowᵏ k u v) ⟩
  ((v ↑ᵏ k) • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  (v ↑ᵏ k) • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools (_VRel,_===_ (k + n))

------------------------------------------------------------------------
-- In the new theory

open Tools (_XVRel,_===_ 5) public

c₁ : (u : Circuit 1) (v : Circuit 4) → (u ↓ᵏ 4) • (v ↑ᵏ 1) ≈ (v ↑ᵏ 1) • (u ↓ᵏ 4)
c₁ u v = embed (lowᵏ 1 u v)

c₂ : (u : Circuit 2) (v : Circuit 3) → (u ↓ᵏ 3) • (v ↑ᵏ 2) ≈ (v ↑ᵏ 2) • (u ↓ᵏ 3)
c₂ u v = embed (lowᵏ 2 u v)

c₃ : (u : Circuit 3) (v : Circuit 2) → (u ↓ᵏ 2) • (v ↑ᵏ 3) ≈ (v ↑ᵏ 3) • (u ↓ᵏ 2)
c₃ u v = embed (lowᵏ 3 u v)

c₄ : (u : Circuit 4) (v : Circuit 1) → (u ↓ᵏ 1) • (v ↑ᵏ 4) ≈ (v ↑ᵏ 4) • (u ↓ᵏ 1)
c₄ u v = embed (lowᵏ 4 u v)

------------------------------------------------------------------------
-- Scalars

zc : ∀ {w : Circuit 5} → w • iI ≈ iI • w
zc {w} = comm-gate₀-wₓ I-gate w

zc⁻ : ∀ {w : Circuit 5} → w • (iI • iI • iI) ≈ (iI • iI • iI) • w
zc⁻ {w} = begin
  w • (iI • iI • iI)     ≈⟨ sym assoc ⟩
  (w • iI) • (iI • iI)   ≈⟨ sym assoc ⟩
  ((w • iI) • iI) • iI   ≈⟨ front iI (front iI zc) ⟩
  ((iI • w) • iI) • iI   ≈⟨ front iI assoc ⟩
  (iI • (w • iI)) • iI   ≈⟨ front iI (back iI zc) ⟩
  (iI • (iI • w)) • iI   ≈⟨ assoc ⟩
  iI • ((iI • w) • iI)   ≈⟨ back iI assoc ⟩
  iI • (iI • (w • iI))   ≈⟨ back iI (back iI zc) ⟩
  iI • (iI • (iI • w))   ≈⟨ back iI (sym assoc) ⟩
  iI • ((iI • iI) • w)   ≈⟨ sym assoc ⟩
  (iI • iI • iI) • w ∎

-- A scalar at another lift (both spell the same canonical word).
uₛ : (w v : Circuit 5) → can w ≡ can v → w ≈ v
uₛ w v e = embed (PB.trans (can-≈ w) (Eq.subst (λ x → 5 ⊢ x ≈ v) (Eq.sym e) (PB.sym (can-≈ v))))

------------------------------------------------------------------------
-- AX at its canonical placement

axAX : ⟪ CS01 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [] ⟫ʷ ≈ ⟪ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS01 ∷ [] ⟫ʷ
axAX = trans (by-assoc Eq.refl) (trans (axiom (srelₓ ax)) (by-assoc Eq.refl))
