------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of the controlled functor
--
-- At every width n ≥ 4, a circuit put under the controlled functor
-- denotes the circuit's matrix controlled by the new top wire:
--
--     ⟦ λ¹ʷ w ⟧ ~ ctrl ⟦ w ⟧,      ⟦ λ⁰ʷ w ⟧ ~ ctrl⁰ ⟦ w ⟧,
--
-- so controlled versions of sound equations are sound (`λ¹ᵏ-~`).  It is
-- enough to see it on generators, `ctrl` being a homomorphism
-- (Semantics.Control).  A letter one wire up is its image one wire up,
-- and `ctrl` commutes with the shift; the letters on the bottom wires
-- are stretched from their closed forms (Lambda.Checks) by `stretch`,
-- which inserts an idle wire under the control: `top` adds it on top
-- (both blocks get it, `top-sem`) and the exchange of the top two wires
-- puts it under the control (`blk-swapL`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda.Semantics where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Data.Nat.Properties as NP
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Lambda.Checks

private
  variable
    k m n : ℕ

  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

------------------------------------------------------------------------
-- The interpretation on scaled operators

⟦gen⟧ : (g : Gen n) → ⟦ [ g ]ʷ ⟧ ~ (1 , ⟦ g ⟧ᵍ)
⟦gen⟧ g = ~-reflexive {l = 1} {1} Eq.refl (⟦⟧ₒ-gen g)

⟦ε⟧ : ⟦ ε {X = Gen n} ⟧ ~ ε∙
⟦ε⟧ = ~-reflexive {l = 0} {0} Eq.refl ⟦⟧ₒ-ε

⟦•⟧ : (w v : Circuit n) → ⟦ w • v ⟧ ~ (⟦ w ⟧ ∙ ⟦ v ⟧)
⟦•⟧ w v = ~-reflexive {l = len w +ℕ len v} {len w +ℕ len v} Eq.refl (⟦⟧ₒ-• w v)

⟦↑⟧ : (w : Circuit n) → ⟦ w ↑ ⟧ ~ upS ⟦ w ⟧
⟦↑⟧ w = ~-reflexive {l = len (w ↑)} {len w} (len-↑ w) (up-word w)

-- ∙-cong with its four operands given.
∙-cong′ : (s s′ t t′ : Scaled n) → s ~ s′ → t ~ t′ → (s ∙ t) ~ (s′ ∙ t′)
∙-cong′ s s′ t t′ = ∙-cong {s = s} {s′} {t} {t′}

------------------------------------------------------------------------
-- An idle wire on top

private
  len-top : (w : Circuit n) → len (top w) ≡ len w
  len-top [ g ]ʷ  = Eq.refl
  len-top ε       = Eq.refl
  len-top (w • v) = Eq.cong₂ _+ℕ_ (len-top w) (len-top v)

  -- The one- and two-wire gates are Kronecker products, with the
  -- identity on the wires above.
  top-emb₁ : (A : Mat 1) → emb {1} {₁₊ n} A ≐ blk (emb {1} {n} A) (emb A)
  top-emb₁ A = ≐-sym (≐-trans (blk-tensor₁ (ix A) Idₒ Idₒ) (tensor-cong (≐-refl (ix A)) blk-Id))

  top-emb₂ : (A : Mat 2) → emb {2} {₁₊ n} A ≐ blk (emb {2} {n} A) (emb A)
  top-emb₂ A = ≐-sym (≐-trans (blk-tensor₂ (ix A) Idₒ Idₒ) (tensor-cong (≐-refl (ix A)) blk-Id))

  top-gen : (g : Gen n) → ⟦ g ↧ ⟧ᵍ ≐ blk ⟦ g ⟧ᵍ ⟦ g ⟧ᵍ
  top-gen (gate₀ I-gate) = ≐-sym (blk-scal γⅈ)
  top-gen (gate₁ S-gate) = top-emb₁ sM
  top-gen (gate₁ K-gate) = top-emb₁ kM
  top-gen (gate₂ CS-gate) = top-emb₂ csM
  top-gen (g ↥) = ≐-trans (up-cong (top-gen g)) (up-blk ⟦ g ⟧ᵍ ⟦ g ⟧ᵍ)

  top-sem : (w : Circuit n) → ⟦ top w ⟧ₒ ≐ blk ⟦ w ⟧ₒ ⟦ w ⟧ₒ
  top-sem [ g ]ʷ =
    ≐-trans (⟦⟧ₒ-gen (g ↧))
      (≐-trans (top-gen g) (blk-cong (≐-sym (⟦⟧ₒ-gen g)) (≐-sym (⟦⟧ₒ-gen g))))
  top-sem ε =
    ≐-trans ⟦⟧ₒ-ε (≐-trans (≐-sym blk-Id) (blk-cong (≐-sym ⟦⟧ₒ-ε) (≐-sym ⟦⟧ₒ-ε)))
  top-sem (w • v) =
    ≐-trans (⟦⟧ₒ-• (top w) (top v))
      (≐-trans (⊙-cong (top-sem w) (top-sem v))
        (≐-trans (blk-⊙ ⟦ w ⟧ₒ ⟦ w ⟧ₒ ⟦ v ⟧ₒ ⟦ v ⟧ₒ)
                 (blk-cong (≐-sym (⟦⟧ₒ-• w v)) (≐-sym (⟦⟧ₒ-• w v)))))

topS : Scaled n → Scaled (₁₊ n)
topS (l , M) = l , blk M M

⟦top⟧ : (w : Circuit n) → ⟦ top w ⟧ ~ topS ⟦ w ⟧
⟦top⟧ w = ~-reflexive {l = len (top w)} {len w} (len-top w) (top-sem w)

topS-~ : {s t : Scaled n} → s ~ t → topS s ~ topS t
topS-~ {s = l , M} {l′ , M′} e x y =
  Eq.trans (Eq.sym (blk-scale (γ^ l′) M M x y))
    (Eq.trans (blk-cong e e x y) (blk-scale (γ^ l) M′ M′ x y))

------------------------------------------------------------------------
-- The permutations of the top wires

Swᵗ-sem : ∀ k → ⟦ Swᵗ k ⟧ ~ (0 , permOp (swapL {k}))
Swᵗ-sem zero    = Swap-perm
Swᵗ-sem (suc k) = begin
  ⟦ Swᵗ k ↑ ⟧                    ≈⟨ ⟦↑⟧ (Swᵗ k) ⟩
  upS ⟦ Swᵗ k ⟧                  ≈⟨ upS-~ {s = ⟦ Swᵗ k ⟧} {0 , permOp swapL} (Swᵗ-sem k) ⟩
  (0 , up (permOp swapL))        ≈⟨ ~-reflexive {l = 0} {0} Eq.refl
                                      (up-perm swapL swapL (λ a x → Eq.refl)) ⟩
  (0 , permOp swapL)             ∎
  where open R (₃₊ k)

Xᵗ-sem : ∀ k → ⟦ Xᵗ k ⟧ ~ (0 , permOp (flipL {k}))
Xᵗ-sem zero    = X-perm
Xᵗ-sem (suc k) = begin
  ⟦ Xᵗ k ↑ ⟧                     ≈⟨ ⟦↑⟧ (Xᵗ k) ⟩
  upS ⟦ Xᵗ k ⟧                   ≈⟨ upS-~ {s = ⟦ Xᵗ k ⟧} {0 , permOp flipL} (Xᵗ-sem k) ⟩
  (0 , up (permOp flipL))        ≈⟨ ~-reflexive {l = 0} {0} Eq.refl
                                      (up-perm flipL flipL (λ a x → Eq.refl)) ⟩
  (0 , permOp flipL)             ∎
  where open R (₂₊ k)

------------------------------------------------------------------------
-- Stretching

-- Conjugating by the exchange of the top two wires.
private
  conj-swap : (l : ℕ) (P M : Op (₁₊ k)) →
              ((0 , permOp swapL) ∙ ((l , blk (blk P M) (blk P M)) ∙ (0 , permOp swapL)))
              ~ (l , blk (blk P P) (blk M M))
  conj-swap {k} l P M =
    ~-reflexive {l = 0 +ℕ (l +ℕ 0)} {l} (NP.+-identityʳ l)
      (λ x y → Eq.trans (perm-conj swapL swapL-δ (blk (blk P M) (blk P M)) x y)
                        (blk-swapL P M x y))

stretch-sem : (c : Circuit (₂₊ k)) (l : ℕ) (P M : Op (₁₊ k)) →
              ⟦ c ⟧ ~ (l , blk P M) → ⟦ stretch c ⟧ ~ (l , blk (blk P P) (blk M M))
stretch-sem {k} c l P M e = begin
  ⟦ Sw • top c • Sw ⟧                        ≈⟨ ⟦•⟧ Sw (top c • Sw) ⟩
  ⟦ Sw ⟧ ∙ ⟦ top c • Sw ⟧                    ≈⟨ ∙-cong′ ⟦ Sw ⟧ ⟦ Sw ⟧ ⟦ top c • Sw ⟧ (⟦ top c ⟧ ∙ ⟦ Sw ⟧) (~-refl ⟦ Sw ⟧) (⟦•⟧ (top c) Sw) ⟩
  ⟦ Sw ⟧ ∙ (⟦ top c ⟧ ∙ ⟦ Sw ⟧)              ≈⟨ ∙-cong′ ⟦ Sw ⟧ π (⟦ top c ⟧ ∙ ⟦ Sw ⟧) (topS (l , blk P M) ∙ π) (Swᵗ-sem (suc k))
                                                 (∙-cong′ ⟦ top c ⟧ (topS (l , blk P M)) ⟦ Sw ⟧ π
                                                    (~-trans {s = ⟦ top c ⟧} {topS ⟦ c ⟧} {topS (l , blk P M)}
                                                       (⟦top⟧ c) (topS-~ {s = ⟦ c ⟧} {l , blk P M} e))
                                                    (Swᵗ-sem (suc k))) ⟩
  π ∙ (topS (l , blk P M) ∙ π)               ≈⟨ conj-swap l P M ⟩
  (l , blk (blk P P) (blk M M))              ∎
  where
  open R (₃₊ k)
  Sw = Swᵗ (suc k)
  π  = (0 , permOp (swapL {suc k}))

private
  -- A stretched one- or two-wire gate under a top control.
  stretch₁ : (c : Circuit (₂₊ k)) (A : Mat 1) →
             ⟦ c ⟧ ~ ctrl (1 , emb {1} {k} A) → ⟦ stretch c ⟧ ~ ctrl (1 , emb {1} {₁₊ k} A)
  stretch₁ {k} c A e =
    ~-trans {s = ⟦ stretch c ⟧}
            {1 , blk (blk (scal (γ^ 1)) (scal (γ^ 1))) (blk (emb A) (emb A))}
            {ctrl (1 , emb {1} {₁₊ k} A)}
      (stretch-sem c 1 (scal (γ^ 1)) (emb A) e)
      (~-reflexive {l = 1} {1} Eq.refl (blk-cong (blk-scal (γ^ 1)) (≐-sym (top-emb₁ A))))

  stretch₂ : (c : Circuit (suc (₄₊ k))) (A : Mat 2) →
             ⟦ c ⟧ ~ ctrl (1 , emb {2} {₂₊ k} A) → ⟦ stretch c ⟧ ~ ctrl (1 , emb {2} {₃₊ k} A)
  stretch₂ {k} c A e =
    ~-trans {s = ⟦ stretch c ⟧}
            {1 , blk (blk (scal (γ^ 1)) (scal (γ^ 1))) (blk (emb A) (emb A))}
            {ctrl (1 , emb {2} {₃₊ k} A)}
      (stretch-sem c 1 (scal (γ^ 1)) (emb A) e)
      (~-reflexive {l = 1} {1} Eq.refl (blk-cong (blk-scal (γ^ 1)) (≐-sym (top-emb₂ A))))

------------------------------------------------------------------------
-- The letters on the bottom wires

CSᵗ-sem : ∀ k → ⟦ CSᵗ k ⟧ ~ ctrl (1 , emb {1} {k} sM)
CSᵗ-sem zero    = CS-ctrl
CSᵗ-sem (suc k) = stretch₁ (CSᵗ k) sM (CSᵗ-sem k)

CKᵗ-sem : ∀ k → ⟦ CKᵗ k ⟧ ~ ctrl (1 , emb {1} {k} kM)
CKᵗ-sem zero    = CK-ctrl
CKᵗ-sem (suc k) = stretch₁ (CKᵗ k) kM (CKᵗ-sem k)

Σᵗ-sem : ∀ k → ⟦ Σᵗ k ⟧ ~ ctrl (1 , emb {2} {₂₊ k} csM)
Σᵗ-sem zero    = Σ₀₁
Σᵗ-sem (suc k) = stretch₂ (Σᵗ k) csM (Σᵗ-sem k)

Sᵗ-sem : ∀ k → ⟦ Sᵗ k ⟧ ~ ctrl (1 , scal {k} γⅈ)
Sᵗ-sem zero    = S-ctrl
Sᵗ-sem (suc k) = begin
  ⟦ Sᵗ k ↑ ⟧                         ≈⟨ ⟦↑⟧ (Sᵗ k) ⟩
  upS ⟦ Sᵗ k ⟧                       ≈⟨ upS-~ {s = ⟦ Sᵗ k ⟧} {ctrl (1 , scal γⅈ)} (Sᵗ-sem k) ⟩
  upS (ctrl (1 , scal γⅈ))           ≈⟨ upS-ctrl (1 , scal γⅈ) ⟩
  ctrl (1 , up (scal γⅈ))            ≈⟨ ctrl-~ {s = 1 , up (scal γⅈ)} {1 , scal γⅈ}
                                          (~-reflexive {l = 1} {1} Eq.refl (up-scal γⅈ)) ⟩
  ctrl (1 , scal γⅈ)                 ∎
  where open R (₂₊ k)

------------------------------------------------------------------------
-- Generators

-- A letter one wire up.
up-case : (w : Circuit (₁₊ m)) (G : Op m) → ⟦ w ⟧ ~ ctrl (1 , G) → ⟦ w ↑ ⟧ ~ ctrl (1 , up G)
up-case {m} w G e = begin
  ⟦ w ↑ ⟧                  ≈⟨ ⟦↑⟧ w ⟩
  upS ⟦ w ⟧                ≈⟨ upS-~ {s = ⟦ w ⟧} {ctrl (1 , G)} e ⟩
  upS (ctrl (1 , G))       ≈⟨ upS-ctrl (1 , G) ⟩
  ctrl (1 , up G)          ∎
  where open R (₂₊ m)

λ¹-gen : (g : Gen (₄₊ n)) → ⟦ λ¹ g ⟧ ~ ctrl (1 , ⟦ g ⟧ᵍ)
λ¹-gen {n}     I-gen  = Sᵗ-sem (₄₊ n)
λ¹-gen {n}     S-gen  = CSᵗ-sem (₃₊ n)
λ¹-gen {n}     K-gen  = CKᵗ-sem (₃₊ n)
λ¹-gen {n}     CS-gen = Σᵗ-sem n
λ¹-gen {suc n} (g ↥)  = up-case (λ¹ g) ⟦ g ⟧ᵍ (λ¹-gen g)
-- A four-wire domain, the generators above wire 0.
λ¹-gen {zero} (I-gen ↥)  = up-case (Sᵗ ₃) (scal γⅈ) (Sᵗ-sem ₃)
λ¹-gen {zero} (S-gen ↥)  = up-case (CSᵗ ₂) (emb sM) (CSᵗ-sem ₂)
λ¹-gen {zero} (K-gen ↥)  = up-case (CKᵗ ₂) (emb kM) (CKᵗ-sem ₂)
λ¹-gen {zero} (CS-gen ↥) = Σ₁₂
λ¹-gen {zero} (I-gen ↥ ↥) =
  up-case (Sᵗ ₃) (up (scal γⅈ)) (up-case (Sᵗ ₂) (scal γⅈ) (Sᵗ-sem ₂))
λ¹-gen {zero} (S-gen ↥ ↥) =
  up-case (CSᵗ ₁ ↑) (up (emb sM)) (up-case (CSᵗ ₁) (emb sM) (CSᵗ-sem ₁))
λ¹-gen {zero} (K-gen ↥ ↥) =
  up-case (CKᵗ ₁ ↑) (up (emb kM)) (up-case (CKᵗ ₁) (emb kM) (CKᵗ-sem ₁))
λ¹-gen {zero} (CS-gen ↥ ↥) = Σ₂₃
λ¹-gen {zero} (I-gen ↥ ↥ ↥) =
  up-case (Sᵗ ₃) (up (up (scal γⅈ)))
    (up-case (Sᵗ ₂) (up (scal γⅈ)) (up-case (Sᵗ ₁) (scal γⅈ) (Sᵗ-sem ₁)))
λ¹-gen {zero} (S-gen ↥ ↥ ↥) =
  up-case (CSᵗ ₀ ↑ ↑) (up (up (emb sM)))
    (up-case (CSᵗ ₀ ↑) (up (emb sM)) (up-case (CSᵗ ₀) (emb sM) (CSᵗ-sem ₀)))
λ¹-gen {zero} (K-gen ↥ ↥ ↥) =
  up-case (CKᵗ ₀ ↑ ↑) (up (up (emb kM)))
    (up-case (CKᵗ ₀ ↑) (up (emb kM)) (up-case (CKᵗ ₀) (emb kM) (CKᵗ-sem ₀)))
λ¹-gen {zero} (I-gen ↥ ↥ ↥ ↥) =
  up-case (Sᵗ ₃) (up (up (up (scal γⅈ))))
    (up-case (Sᵗ ₂) (up (up (scal γⅈ)))
      (up-case (Sᵗ ₁) (up (scal γⅈ)) (up-case (Sᵗ ₀) (scal γⅈ) (Sᵗ-sem ₀))))

-- With the control white: X on the top wire exchanges the blocks.
private
  conj-flip : (l : ℕ) (P M : Op m) →
              ((0 , permOp flipL) ∙ ((l , blk P M) ∙ (0 , permOp flipL))) ~ (l , blk M P)
  conj-flip l P M =
    ~-reflexive {l = 0 +ℕ (l +ℕ 0)} {l} (NP.+-identityʳ l)
      (λ x y → Eq.trans (perm-conj flipL flipL-δ (blk P M) x y) (blk-flipL P M x y))

λ⁰-gen : (g : Gen (₄₊ n)) → ⟦ λ⁰ g ⟧ ~ ctrl⁰ (1 , ⟦ g ⟧ᵍ)
λ⁰-gen {n} g = begin
  ⟦ Xt • λ¹ g • Xt ⟧                 ≈⟨ ⟦•⟧ Xt (λ¹ g • Xt) ⟩
  ⟦ Xt ⟧ ∙ ⟦ λ¹ g • Xt ⟧             ≈⟨ ∙-cong′ ⟦ Xt ⟧ ⟦ Xt ⟧ ⟦ λ¹ g • Xt ⟧ (⟦ λ¹ g ⟧ ∙ ⟦ Xt ⟧) (~-refl ⟦ Xt ⟧) (⟦•⟧ (λ¹ g) Xt) ⟩
  ⟦ Xt ⟧ ∙ (⟦ λ¹ g ⟧ ∙ ⟦ Xt ⟧)       ≈⟨ ∙-cong′ ⟦ Xt ⟧ φ (⟦ λ¹ g ⟧ ∙ ⟦ Xt ⟧) (ctrl (1 , ⟦ g ⟧ᵍ) ∙ φ) (Xᵗ-sem (₄₊ n))
                                          (∙-cong′ ⟦ λ¹ g ⟧ (ctrl (1 , ⟦ g ⟧ᵍ)) ⟦ Xt ⟧ φ
                                             (λ¹-gen g) (Xᵗ-sem (₄₊ n))) ⟩
  φ ∙ (ctrl (1 , ⟦ g ⟧ᵍ) ∙ φ)        ≈⟨ conj-flip 1 (scal (γ^ 1)) ⟦ g ⟧ᵍ ⟩
  ctrl⁰ (1 , ⟦ g ⟧ᵍ)                 ∎
  where
  open R (suc (₄₊ n))
  Xt = Xᵗ (₄₊ n)
  φ  = (0 , permOp (flipL {₄₊ n}))

------------------------------------------------------------------------
-- Circuits

λ¹-sem : (w : Circuit (₄₊ n)) → ⟦ λ¹ʷ w ⟧ ~ ctrl ⟦ w ⟧
λ¹-sem {n} [ g ]ʷ = begin
  ⟦ λ¹ g ⟧                 ≈⟨ λ¹-gen g ⟩
  ctrl (1 , ⟦ g ⟧ᵍ)        ≈⟨ ctrl-~ {s = 1 , ⟦ g ⟧ᵍ} {⟦ [ g ]ʷ ⟧}
                                (~-sym {s = ⟦ [ g ]ʷ ⟧} {1 , ⟦ g ⟧ᵍ} (⟦gen⟧ g)) ⟩
  ctrl ⟦ [ g ]ʷ ⟧          ∎
  where open R (suc (₄₊ n))
λ¹-sem {n} ε = begin
  ⟦ ε ⟧                    ≈⟨ ⟦ε⟧ ⟩
  ε∙                       ≈⟨ ~-sym {s = ctrl ε∙} {ε∙} ctrl-ε ⟩
  ctrl ε∙                  ≈⟨ ctrl-~ {s = ε∙} {⟦ ε ⟧} (~-sym {s = ⟦ ε ⟧} {ε∙} ⟦ε⟧) ⟩
  ctrl ⟦ ε ⟧               ∎
  where open R (suc (₄₊ n))
λ¹-sem {n} (w • v) = begin
  ⟦ λ¹ʷ w • λ¹ʷ v ⟧               ≈⟨ ⟦•⟧ (λ¹ʷ w) (λ¹ʷ v) ⟩
  ⟦ λ¹ʷ w ⟧ ∙ ⟦ λ¹ʷ v ⟧           ≈⟨ ∙-cong′ ⟦ λ¹ʷ w ⟧ (ctrl ⟦ w ⟧) ⟦ λ¹ʷ v ⟧ (ctrl ⟦ v ⟧)
                                       (λ¹-sem w) (λ¹-sem v) ⟩
  ctrl ⟦ w ⟧ ∙ ctrl ⟦ v ⟧         ≈⟨ ~-sym {s = ctrl (⟦ w ⟧ ∙ ⟦ v ⟧)} {ctrl ⟦ w ⟧ ∙ ctrl ⟦ v ⟧}
                                       (ctrl-∙ ⟦ w ⟧ ⟦ v ⟧) ⟩
  ctrl (⟦ w ⟧ ∙ ⟦ v ⟧)            ≈⟨ ctrl-~ {s = ⟦ w ⟧ ∙ ⟦ v ⟧} {⟦ w • v ⟧}
                                       (~-sym {s = ⟦ w • v ⟧} {⟦ w ⟧ ∙ ⟦ v ⟧} (⟦•⟧ w v)) ⟩
  ctrl ⟦ w • v ⟧                  ∎
  where open R (suc (₄₊ n))

λ⁰-sem : (w : Circuit (₄₊ n)) → ⟦ λ⁰ʷ w ⟧ ~ ctrl⁰ ⟦ w ⟧
λ⁰-sem {n} [ g ]ʷ = begin
  ⟦ λ⁰ g ⟧                 ≈⟨ λ⁰-gen g ⟩
  ctrl⁰ (1 , ⟦ g ⟧ᵍ)       ≈⟨ ctrl⁰-~ {s = 1 , ⟦ g ⟧ᵍ} {⟦ [ g ]ʷ ⟧}
                                (~-sym {s = ⟦ [ g ]ʷ ⟧} {1 , ⟦ g ⟧ᵍ} (⟦gen⟧ g)) ⟩
  ctrl⁰ ⟦ [ g ]ʷ ⟧         ∎
  where open R (suc (₄₊ n))
λ⁰-sem {n} ε = begin
  ⟦ ε ⟧                    ≈⟨ ⟦ε⟧ ⟩
  ε∙                       ≈⟨ ~-sym {s = ctrl⁰ ε∙} {ε∙} ctrl⁰-ε ⟩
  ctrl⁰ ε∙                 ≈⟨ ctrl⁰-~ {s = ε∙} {⟦ ε ⟧} (~-sym {s = ⟦ ε ⟧} {ε∙} ⟦ε⟧) ⟩
  ctrl⁰ ⟦ ε ⟧              ∎
  where open R (suc (₄₊ n))
λ⁰-sem {n} (w • v) = begin
  ⟦ λ⁰ʷ w • λ⁰ʷ v ⟧               ≈⟨ ⟦•⟧ (λ⁰ʷ w) (λ⁰ʷ v) ⟩
  ⟦ λ⁰ʷ w ⟧ ∙ ⟦ λ⁰ʷ v ⟧           ≈⟨ ∙-cong′ ⟦ λ⁰ʷ w ⟧ (ctrl⁰ ⟦ w ⟧) ⟦ λ⁰ʷ v ⟧ (ctrl⁰ ⟦ v ⟧)
                                       (λ⁰-sem w) (λ⁰-sem v) ⟩
  ctrl⁰ ⟦ w ⟧ ∙ ctrl⁰ ⟦ v ⟧       ≈⟨ ~-sym {s = ctrl⁰ (⟦ w ⟧ ∙ ⟦ v ⟧)} {ctrl⁰ ⟦ w ⟧ ∙ ctrl⁰ ⟦ v ⟧}
                                       (ctrl⁰-∙ ⟦ w ⟧ ⟦ v ⟧) ⟩
  ctrl⁰ (⟦ w ⟧ ∙ ⟦ v ⟧)           ≈⟨ ctrl⁰-~ {s = ⟦ w ⟧ ∙ ⟦ v ⟧} {⟦ w • v ⟧}
                                       (~-sym {s = ⟦ w • v ⟧} {⟦ w ⟧ ∙ ⟦ v ⟧} (⟦•⟧ w v)) ⟩
  ctrl⁰ ⟦ w • v ⟧                 ∎
  where open R (suc (₄₊ n))

------------------------------------------------------------------------
-- Controlled versions of sound equations are sound

λ¹-~ : {u v : Circuit (₄₊ n)} → ⟦ u ⟧ ~ ⟦ v ⟧ → ⟦ λ¹ʷ u ⟧ ~ ⟦ λ¹ʷ v ⟧
λ¹-~ {n} {u} {v} e = begin
  ⟦ λ¹ʷ u ⟧     ≈⟨ λ¹-sem u ⟩
  ctrl ⟦ u ⟧    ≈⟨ ctrl-~ {s = ⟦ u ⟧} {⟦ v ⟧} e ⟩
  ctrl ⟦ v ⟧    ≈⟨ ~-sym {s = ⟦ λ¹ʷ v ⟧} {ctrl ⟦ v ⟧} (λ¹-sem v) ⟩
  ⟦ λ¹ʷ v ⟧     ∎
  where open R (suc (₄₊ n))

λ⁰-~ : {u v : Circuit (₄₊ n)} → ⟦ u ⟧ ~ ⟦ v ⟧ → ⟦ λ⁰ʷ u ⟧ ~ ⟦ λ⁰ʷ v ⟧
λ⁰-~ {n} {u} {v} e = begin
  ⟦ λ⁰ʷ u ⟧     ≈⟨ λ⁰-sem u ⟩
  ctrl⁰ ⟦ u ⟧   ≈⟨ ctrl⁰-~ {s = ⟦ u ⟧} {⟦ v ⟧} e ⟩
  ctrl⁰ ⟦ v ⟧   ≈⟨ ~-sym {s = ⟦ λ⁰ʷ v ⟧} {ctrl⁰ ⟦ v ⟧} (λ⁰-sem v) ⟩
  ⟦ λ⁰ʷ v ⟧     ∎
  where open R (suc (₄₊ n))

λ¹ᵏ-~ : (k : ℕ) {u v : Circuit (₄₊ n)} → ⟦ u ⟧ ~ ⟦ v ⟧ → ⟦ λ¹ᵏ k u ⟧ ~ ⟦ λ¹ᵏ k v ⟧
λ¹ᵏ-~ zero    e = e
λ¹ᵏ-~ (suc k) e = λ¹-~ (λ¹ᵏ-~ k e)
