------------------------------------------------------------------------
-- Presentations of groups
--
-- A gate is its two controlled halves: g ≡ λ⁰(g) λ¹(g)
--
-- The joint paper's λ-calculus (ii), and on five wires its item (F5):
-- a gate g on the wires below the top one is the product of its
-- versions controlled white and black by the top wire.  Here it is
-- proved at every width from three equations on five wires — the CS
-- of a pair of the bottom four wires — by following the definition of
-- λ (Lambda): a letter one wire up is the letter one wire up (cong↑),
-- and a letter on the bottom wires is stretched from the width below,
-- stretching being a congruence (Five.Weakening) and a homomorphism
-- (the exchange of the top two wires is an involution) that fixes a gate
-- on the bottom wires and carries X on the top wire to X on the new top
-- wire.  The equations for S, K and the scalar come down to one and two
-- wires, where the rules are complete.  On five wires the three CS
-- equations are among the joint paper's derivations; from six on they
-- follow from completeness on five (`F5-from`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda.Split where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; CK₁₀)
open import Examples.Groups.Clifford+CS.Swaps using (Swap²)
open import Examples.Groups.Clifford+CS.Completeness using (complete₁ ; complete₂)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below ; same-sem)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3 ; b-Sb0-1-42-3 ; b-Sb0-2-43-1)
open import Examples.Groups.Clifford+CS.Five.Rules
open import Examples.Groups.Clifford+CS.Five.Weakening using (top-congₓ)

private
  variable
    k n : ℕ

  module S₁ = Below 1 complete₁
  module S₂ = Below 2 complete₂

------------------------------------------------------------------------
-- Stretching, in the old theory

-- The exchange of the top two wires is an involution.
Sw² : ∀ k → (₂₊ k) ⊢ Swᵗ k • Swᵗ k ≈ ε
Sw² zero    = Swap²
Sw² (suc k) = lemma-cong↑ (Swᵗ k • Swᵗ k) ε (Sw² k)

-- An idle wire on top commutes with the shift.
top-↑ : (w : Circuit n) → top (w ↑) ≡ top w ↑
top-↑ [ g ]ʷ  = Eq.refl
top-↑ ε       = Eq.refl
top-↑ (u • v) = Eq.cong₂ _•_ (top-↑ u) (top-↑ v)

stretch-• : (c c′ : Circuit (₂₊ k)) → (₃₊ k) ⊢ stretch (c • c′) ≈ stretch c • stretch c′
stretch-• {k} c c′ = begin
  Sw • (top c • top c′) • Sw
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (Sw • top c) • (top c′ • Sw)
    ≈⟨ back _ (sym left-unit) ⟩
  (Sw • top c) • (ε • top c′ • Sw)
    ≈⟨ back _ (front _ (sym (Sw² (suc k)))) ⟩
  (Sw • top c) • ((Sw • Sw) • top c′ • Sw)
    ≈⟨ by-passoc ((□ • □) • ((□ • □) • □ • □)) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (Sw • top c • Sw) • (Sw • top c′ • Sw) ∎
  where
  open Tools ((₃₊ k) VRel,_===_)
  Sw = Swᵗ (suc k)

-- A gate on the bottom wires is fixed.
private
  fix : ∀ {g : Circuit (₃₊ k)} → (₃₊ k) ⊢ g • Swᵗ (suc k) ≈ Swᵗ (suc k) • g →
        (₃₊ k) ⊢ Swᵗ (suc k) • g • Swᵗ (suc k) ≈ g
  fix {k} {g} e = begin
    Sw • g • Sw       ≈⟨ back _ e ⟩
    Sw • Sw • g       ≈⟨ sym assoc ⟩
    (Sw • Sw) • g     ≈⟨ front _ (Sw² (suc k)) ⟩
    ε • g             ≈⟨ left-unit ⟩
    g ∎
    where
    open Tools ((₃₊ k) VRel,_===_)
    Sw = Swᵗ (suc k)

stretch-fix₁ : (h : Gate 1) → (₃₊ k) ⊢ stretch {k} [ gate₁ h ]ʷ ≈ [ gate₁ h ]ʷ
stretch-fix₁ {k} h = fix (PB.sym (comm-gate₁-w↑ h (Swᵗ k)))

stretch-fix₂ : (h : Gate 2) → (₄₊ k) ⊢ stretch {₁₊ k} [ gate₂ h ]ʷ ≈ [ gate₂ h ]ʷ
stretch-fix₂ {k} h = fix (PB.sym (comm-gate₂-w↑↑ h (Swᵗ k)))

-- X on the top wire is carried to the new top wire.
stretch-X : ∀ k → (₃₊ k) ⊢ stretch (Xᵗ (₁₊ k)) ≈ Xᵗ (₂₊ k)
stretch-X zero    = lemma-cong↑ (Swap • X • Swap) (X ↑) (S₂.by-sem₀ (Swap • X • Swap) (X ↑) Eq.refl)
stretch-X (suc k) =
  Eq.subst (λ x → (₄₊ k) ⊢ Swᵗ (₂₊ k) • x • Swᵗ (₂₊ k) ≈ Xᵗ (₃₊ k))
           (Eq.sym (top-↑ (Xᵗ (₁₊ k))))
           (lemma-cong↑ (stretch (Xᵗ (₁₊ k))) (Xᵗ (₂₊ k)) (stretch-X k))

-- A gate and its two halves, stretched.
private
  stretch-halves : (c : Circuit (₂₊ k)) →
                   (₃₊ k) ⊢ stretch ((Xᵗ (₁₊ k) • c • Xᵗ (₁₊ k)) • c)
                          ≈ (Xᵗ (₂₊ k) • stretch c • Xᵗ (₂₊ k)) • stretch c
  stretch-halves {k} c = begin
    stretch ((Xt • c • Xt) • c)
      ≈⟨ stretch-• (Xt • c • Xt) c ⟩
    stretch (Xt • c • Xt) • stretch c
      ≈⟨ front _ (stretch-• Xt (c • Xt)) ⟩
    (stretch Xt • stretch (c • Xt)) • stretch c
      ≈⟨ front _ (back _ (stretch-• c Xt)) ⟩
    (stretch Xt • stretch c • stretch Xt) • stretch c
      ≈⟨ front _ (cong (stretch-X k) (back _ (stretch-X k))) ⟩
    (Xᵗ (₂₊ k) • stretch c • Xᵗ (₂₊ k)) • stretch c ∎
    where
    open Tools ((₃₊ k) VRel,_===_)
    Xt = Xᵗ (₁₊ k)

------------------------------------------------------------------------
-- The letters on the bottom wires, at every width

private
  -- A gate fixed by stretching, whose halves split at the width below,
  -- splits at the next width.
  step : ∀ {g : Circuit (₂₊ k)} {g′ : Circuit (₃₊ k)} (c : Circuit (₂₊ k)) →
         (₃₊ k) ⊢ stretch g ≈ g′ →
         (₂₊ k) ⊢ₓ g ≈ (Xᵗ (₁₊ k) • c • Xᵗ (₁₊ k)) • c →
         (₃₊ k) ⊢ₓ g′ ≈ (Xᵗ (₂₊ k) • stretch c • Xᵗ (₂₊ k)) • stretch c
  step {k} {g} {g′} c f e = begin
    g′                                            ≈⟨ sym (embed f) ⟩
    stretch g                                     ≈⟨ cong refl (cong (top-congₓ e) refl) ⟩
    stretch ((Xᵗ (₁₊ k) • c • Xᵗ (₁₊ k)) • c)     ≈⟨ embed (stretch-halves c) ⟩
    (Xᵗ (₂₊ k) • stretch c • Xᵗ (₂₊ k)) • stretch c ∎
    where open Tools ((₃₊ k) XVRel,_===_)

split-I : ∀ k → (₁₊ k) ⊢ₓ iI ≈ (Xᵗ k • Sᵗ k • Xᵗ k) • Sᵗ k
split-I zero    = embed (S₁.by-sem₀ iI ((X • S • X) • S) Eq.refl)
split-I (suc k) =
  PB.trans (embed (PB.sym (PB.axiom (ω↑=ω I-gate))))
           (lemma-cong↑ₓ iI ((Xᵗ k • Sᵗ k • Xᵗ k) • Sᵗ k) (split-I k))

split-S : ∀ k → (₂₊ k) ⊢ₓ S ≈ (Xᵗ (₁₊ k) • CSᵗ k • Xᵗ (₁₊ k)) • CSᵗ k
split-S zero    = embed (S₂.by-sem₀ S ((X ↑ • CS • X ↑) • CS) Eq.refl)
split-S (suc k) = step (CSᵗ k) (stretch-fix₁ S-gate) (split-S k)

split-K : ∀ k → (₂₊ k) ⊢ₓ K ≈ (Xᵗ (₁₊ k) • CKᵗ k • Xᵗ (₁₊ k)) • CKᵗ k
split-K zero    = embed (S₂.by-sem₀ K ((X ↑ • CK₁₀ • X ↑) • CK₁₀) Eq.refl)
split-K (suc k) = step (CKᵗ k) (stretch-fix₁ K-gate) (split-K k)

------------------------------------------------------------------------
-- The three equations on five wires

record F5 : Set where
  field
    cs₀₁ : 5 ⊢ₓ CS ≈ (Xᵗ ₄ • b-Sb2-0-41-3 • Xᵗ ₄) • b-Sb2-0-41-3
    cs₁₂ : 5 ⊢ₓ CS ↑ ≈ (Xᵗ ₄ • b-Sb0-1-42-3 • Xᵗ ₄) • b-Sb0-1-42-3
    cs₂₃ : 5 ⊢ₓ CS ↑ ↑ ≈ (Xᵗ ₄ • b-Sb0-2-43-1 • Xᵗ ₄) • b-Sb0-2-43-1

-- From completeness on five wires.
F5-from : (∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ₓ u ≈ v) → F5
F5-from c₅ = record
  { cs₀₁ = c₅ (same-sem CS ((Xᵗ ₄ • b-Sb2-0-41-3 • Xᵗ ₄) • b-Sb2-0-41-3) Eq.refl)
  ; cs₁₂ = c₅ (same-sem (CS ↑) ((Xᵗ ₄ • b-Sb0-1-42-3 • Xᵗ ₄) • b-Sb0-1-42-3) Eq.refl)
  ; cs₂₃ = c₅ (same-sem (CS ↑ ↑) ((Xᵗ ₄ • b-Sb0-2-43-1 • Xᵗ ₄) • b-Sb0-2-43-1) Eq.refl)
  }

------------------------------------------------------------------------
-- Every generator, at every width

module _ (f5 : F5) where
  open F5 f5

  split-CS : ∀ n → (suc (₄₊ n)) ⊢ₓ CS ≈ (Xᵗ (₄₊ n) • Σᵗ n • Xᵗ (₄₊ n)) • Σᵗ n
  split-CS zero    = cs₀₁
  split-CS (suc n) = step (Σᵗ n) (stretch-fix₂ CS-gate) (split-CS n)

  split : (g : Gen (₄₊ n)) → (suc (₄₊ n)) ⊢ₓ top [ g ]ʷ ≈ λ⁰ g • λ¹ g
  split {n} I-gen  = split-I (₄₊ n)
  split {n} S-gen  = split-S (₃₊ n)
  split {n} K-gen  = split-K (₃₊ n)
  split {n} CS-gen = split-CS n
  split {suc n} (g ↥) = lemma-cong↑ₓ (top [ g ]ʷ) (λ⁰ g • λ¹ g) (split g)
  -- A four-wire domain, the generators above wire 0.
  split {zero} (I-gen ↥)  = lemma-cong↑ₓ _ _ (split-I ₃)
  split {zero} (S-gen ↥)  = lemma-cong↑ₓ _ _ (split-S ₂)
  split {zero} (K-gen ↥)  = lemma-cong↑ₓ _ _ (split-K ₂)
  split {zero} (CS-gen ↥) = cs₁₂
  split {zero} (I-gen ↥ ↥)  = lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-I ₂))
  split {zero} (S-gen ↥ ↥)  = lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-S ₁))
  split {zero} (K-gen ↥ ↥)  = lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-K ₁))
  split {zero} (CS-gen ↥ ↥) = cs₂₃
  split {zero} (I-gen ↥ ↥ ↥) = lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-I ₁)))
  split {zero} (S-gen ↥ ↥ ↥) = lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-S ₀)))
  split {zero} (K-gen ↥ ↥ ↥) = lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-K ₀)))
  split {zero} (I-gen ↥ ↥ ↥ ↥) =
    lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (lemma-cong↑ₓ _ _ (split-I ₀))))
