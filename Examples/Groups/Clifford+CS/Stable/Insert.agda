------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor and an idle wire inserted above the bottom one
--
-- `place 1 u` (Place) is u with an idle wire inserted as wire 1.  A
-- one-wire letter on wire 0 has its controlled image there, CS or CK
-- between wire 0 and the control, spelled by stretching (Lambda); that
-- image one width up is the image one width down with wire 1 inserted
-- (`CSᵗ-place`, `CKᵗ-place`): on three wires by one evaluation, and from
-- there by stretching, which a placement at wire 1 passes
-- (`stretch-place`).  A letter one wire up has its image one wire up,
-- which wire 1 inserted carries one more wire up (`place₁-↑`).  So the
-- commutation of a gate on wire 0 with one far above it goes down a
-- width under λ¹ (Stable.Transport).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Insert where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; CK₁₀)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.TopWeakening using (top-cong ; low-comm)
open import Examples.Groups.Clifford+CS.Place using (place ; place-• ; place-high ; ↑ᵏ-↑)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Lambda.Split using (top-↑)
open import Examples.Groups.Clifford+CS.Stable.Rules

private
  variable
    k n : ℕ

  module S₃ = Below 3 complete₃

------------------------------------------------------------------------
-- Placing in the theory with the schema

place-congᵧ : ∀ i {r} {u v : Circuit (i +ℕ r)} → (i +ℕ r) ⊢ᵧ u ≈ v →
              (₁₊ (i +ℕ r)) ⊢ᵧ place i u ≈ place i v
place-congᵧ i {r} {u} {v} e = cong refl (cong (lemma-cong↑ᵧ u v e) refl)
  where open Tools ((₁₊ (i +ℕ r)) YVRel,_===_)

place-•ᵧ : ∀ i {r} (u v : Circuit (i +ℕ r)) →
           (₁₊ (i +ℕ r)) ⊢ᵧ place i (u • v) ≈ place i u • place i v
place-•ᵧ i u v = embed (place-• i u v)

------------------------------------------------------------------------
-- A circuit one wire up

private
  ↑ᵏ0 : (v : Circuit n) → v ↑ᵏ 0 ≡ v
  ↑ᵏ0 [ g ]ʷ  = Eq.refl
  ↑ᵏ0 ε       = Eq.refl
  ↑ᵏ0 (u • v) = Eq.cong₂ _•_ (↑ᵏ0 u) (↑ᵏ0 v)

  ↑ᵏ1 : (v : Circuit n) → v ↑ᵏ 1 ≡ v ↑
  ↑ᵏ1 v = Eq.trans (Eq.sym (↑ᵏ-↑ v 0)) (Eq.cong _↑ (↑ᵏ0 v))

  ↑ᵏ2 : (v : Circuit n) → v ↑ᵏ 2 ≡ v ↑ ↑
  ↑ᵏ2 v = Eq.trans (Eq.sym (↑ᵏ-↑ v 1)) (Eq.cong _↑ (↑ᵏ1 v))

place₁-↑ : (v : Circuit n) → (₂₊ n) ⊢ place 1 (v ↑) ≈ v ↑ ↑
place₁-↑ v = Eq.subst₂ (λ x y → _ ⊢ place 1 x ≈ y) (↑ᵏ1 v) (↑ᵏ2 v) (place-high 1 v)

------------------------------------------------------------------------
-- Stretching passes a placement at wire 1

private
  -- An idle wire on top of a placed circuit.
  top-place₁ : (u : Circuit (₂₊ k)) → top (place 1 u) ≡ place 1 (top u)
  top-place₁ u = Eq.cong (λ x → (ε • Swap) • x • (Swap • ε)) (top-↑ u)

  -- The exchange of the top two wires passes the cycle of wires 0 1.
  Sw-place : (x : Circuit (₃₊ k)) →
             (₄₊ k) ⊢ Swᵗ (₂₊ k) • place 1 x • Swᵗ (₂₊ k) ≈ place 1 (Swᵗ (suc k) • x • Swᵗ (suc k))
  Sw-place {k} x = begin
    T • (P • x ↑ • Q) • T
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (T • P) • x ↑ • (Q • T)
      ≈⟨ cong (sym cP) (back _ cQ) ⟩
    (P • T) • x ↑ • (T • Q)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    P • (T • x ↑ • T) • Q ∎
    where
    open Tools ((₄₊ k) VRel,_===_)
    T = Swᵗ (₂₊ k)
    P = ε • Swap
    Q = Swap • ε
    cP : (₄₊ k) ⊢ P • T ≈ T • P
    cP = low-comm (ε • Swap) (Swᵗ k)
    cQ : (₄₊ k) ⊢ Q • T ≈ T • Q
    cQ = low-comm (Swap • ε) (Swᵗ k)

stretch-place : (c : Circuit (₂₊ k)) → (₃₊ k) ⊢ stretch c ≈ place 1 c →
                (₄₊ k) ⊢ stretch (stretch c) ≈ place 1 (stretch c)
stretch-place {k} c e = begin
  Sw • top (stretch c) • Sw            ≈⟨ back _ (front _ (top-cong e)) ⟩
  Sw • top (place 1 c) • Sw            ≈⟨ refl≡ (Eq.cong (λ x → Sw • x • Sw) (top-place₁ c)) ⟩
  Sw • place 1 (top c) • Sw            ≈⟨ Sw-place (top c) ⟩
  place 1 (stretch c) ∎
  where
  open Tools ((₄₊ k) VRel,_===_)
  Sw = Swᵗ (₂₊ k)
  refl≡ : ∀ {a b : Circuit (₄₊ k)} → a ≡ b → (₄₊ k) ⊢ a ≈ b
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- The letters on wire 0

CSᵗ-place : ∀ k → (₃₊ k) ⊢ CSᵗ (suc k) ≈ place 1 (CSᵗ k)
CSᵗ-place zero    = S₃.by-sem₀ (stretch CS) (place 1 CS) Eq.refl
CSᵗ-place (suc k) = stretch-place (CSᵗ k) (CSᵗ-place k)

CKᵗ-place : ∀ k → (₃₊ k) ⊢ CKᵗ (suc k) ≈ place 1 (CKᵗ k)
CKᵗ-place zero    = S₃.by-sem₀ (stretch CK₁₀) (place 1 CK₁₀) Eq.refl
CKᵗ-place (suc k) = stretch-place (CKᵗ k) (CKᵗ-place k)

-- λ¹ of a one-wire letter on wire 0, one width up, is the same with
-- wire 1 inserted.
λ¹₁-place : ∀ n (h : Gate 1) → (₂₊ (₄₊ n)) ⊢ᵧ λ¹ {suc n} (gate₁ h) ≈ place 1 (λ¹ {n} (gate₁ h))
λ¹₁-place n S-gate = embed (CSᵗ-place (₃₊ n))
λ¹₁-place n K-gate = embed (CKᵗ-place (₃₊ n))
