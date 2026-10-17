------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of Stable.Base7: a controlled gate conjugated by swaps the
-- control does not see
--
-- Each window of Stable.Base7 compares two placements on six wires of a
-- doubly controlled S that differ in one borrowed wire.  Evaluating
-- them exhausts 8 GB; but each is the other conjugated by a swap S of
-- wires below the control, with an idle wire on top (`top S`), and the
-- one is already known to denote a controlled operator ctrl ⟦c⟧.  Then
-- (`win-sem`)
--
--     ⟦top S • Y • top S⟧ ~ topS ⟦S⟧ ∙ ctrl ⟦c⟧ ∙ topS ⟦S⟧ ~ ctrl ⟦c⟧
--
-- as soon as S is an involution and passes c, both on five wires and
-- decided by one small evaluation each: the two blocks of `topS ⟦S⟧`
-- conjugate the two blocks of ctrl ⟦c⟧ (`core`, by blk-⊙).  The first
-- placements are λ¹-images (Lambda.Semantics.λ¹-gen): the controlled CS
-- of the wires 0 1, and one wire up the four-wire domain's CS on its top
-- two wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Windows6 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ)
open import Examples.Groups.Clifford+CS.Soundness using (sound)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.SemanticSteps using (same-sem)
open import Examples.Groups.Clifford+CS.Swaps using (Swap²)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σσ⁻¹ ; nat)
open import Examples.Groups.Clifford+CS.Lambda using (Σᵗ ; λ¹)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦gen⟧ ; ⟦ε⟧ ; ⟦•⟧ ; topS ; ⟦top⟧ ; λ¹-gen)
open import Examples.Groups.Clifford+CS.Stable.Nets7

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Conjugating a controlled operator

private
  -- Two blocks of the same scale.
  blk-~ : {l l′ : ℕ} {P P′ M M′ : Op n} → (l , P) ~ (l′ , P′) → (l , M) ~ (l′ , M′) →
          (l , blk P M) ~ (l′ , blk P′ M′)
  blk-~ {l = l} {l′} {P} {P′} {M} {M′} e f x y =
    Eq.trans (Eq.sym (blk-scale (γ^ l′) P M x y))
      (Eq.trans (blk-cong e f x y) (blk-scale (γ^ l) P′ M′ x y))

  -- The scalar block of ctrl is the unit.
  unit~ : (b : ℕ) → (b , scal {n} (γ^ b)) ~ ε∙
  unit~ b x y = *-identityˡ (γ^ b * δb x y)

core : (s t : Scaled n) → (s ∙ s) ~ ε∙ → (s ∙ (t ∙ s)) ~ t →
       (topS s ∙ (ctrl t ∙ topS s)) ~ ctrl t
core (a , A) (b , B) h1 h2 =
  ~-trans {s = topS s ∙ (ctrl (b , B) ∙ topS s)}
          {t = (a +ℕ (b +ℕ a) , blk (A ⊙ (scal (γ^ b) ⊙ A)) (A ⊙ (B ⊙ A)))}
          {u = ctrl (b , B)}
    (~-reflexive {l = a +ℕ (b +ℕ a)} {a +ℕ (b +ℕ a)}
                 {M = blk A A ⊙ (blk (scal (γ^ b)) B ⊙ blk A A)}
                 {blk (A ⊙ (scal (γ^ b) ⊙ A)) (A ⊙ (B ⊙ A))} Eq.refl
       (≐-trans (⊙-cong (≐-refl (blk A A)) (blk-⊙ (scal (γ^ b)) B A A))
                (blk-⊙ A A (scal (γ^ b) ⊙ A) (B ⊙ A))))
    (blk-~ {l = a +ℕ (b +ℕ a)} {b} {A ⊙ (scal (γ^ b) ⊙ A)} {scal (γ^ b)} {A ⊙ (B ⊙ A)} {B} comp₁ h2)
  where
  s = (a , A)
  u = (b , scal (γ^ b))
  comp₁ : (a +ℕ (b +ℕ a) , A ⊙ (scal (γ^ b) ⊙ A)) ~ (b , scal (γ^ b))
  comp₁ =
    ~-trans {s = s ∙ (u ∙ s)} {t = s ∙ (ε∙ ∙ s)} {u = u}
      (∙-cong {s = s} {s} {u ∙ s} {ε∙ ∙ s} (~-refl s) (∙-cong {s = u} {ε∙} {s} {s} (unit~ b) (~-refl s)))
      (~-trans {s = s ∙ (ε∙ ∙ s)} {t = s ∙ s} {u = u}
        (∙-cong {s = s} {s} {ε∙ ∙ s} {s} (~-refl s) (∙-identityˡ s))
        (~-trans {s = s ∙ s} {t = ε∙} {u = u} h1 (~-sym {s = u} {t = ε∙} (unit~ b))))

-- The window: S an involution passing c, and Y a controlled c.
win-sem : (S c : Circuit n) (Y : Circuit (₁₊ n)) →
          ⟦ S • S ⟧ ~ ⟦ ε {X = Gen n} ⟧ → ⟦ S • (c • S) ⟧ ~ ⟦ c ⟧ → ⟦ Y ⟧ ~ ctrl ⟦ c ⟧ →
          ⟦ top S • (Y • top S) ⟧ ~ ctrl ⟦ c ⟧
win-sem S c Y hS hc hY =
  ~-trans {s = ⟦ top S • (Y • top S) ⟧} {t = ⟦ top S ⟧ ∙ ⟦ Y • top S ⟧} {u = ctrl tc}
    (⟦•⟧ (top S) (Y • top S))
  (~-trans {s = ⟦ top S ⟧ ∙ ⟦ Y • top S ⟧} {t = topS sS ∙ (ctrl tc ∙ topS sS)} {u = ctrl tc}
    (∙-cong {s = ⟦ top S ⟧} {topS sS} {⟦ Y • top S ⟧} {ctrl tc ∙ topS sS}
      (⟦top⟧ S)
      (~-trans {s = ⟦ Y • top S ⟧} {t = ⟦ Y ⟧ ∙ ⟦ top S ⟧} {u = ctrl tc ∙ topS sS}
        (⟦•⟧ Y (top S))
        (∙-cong {s = ⟦ Y ⟧} {ctrl tc} {⟦ top S ⟧} {topS sS} hY (⟦top⟧ S))))
    (core sS tc h1 h2))
  where
  sS = ⟦ S ⟧
  tc = ⟦ c ⟧
  h1 : (sS ∙ sS) ~ ε∙
  h1 = ~-trans {s = sS ∙ sS} {t = ⟦ S • S ⟧} {u = ε∙}
         (~-sym {s = ⟦ S • S ⟧} {t = sS ∙ sS} (⟦•⟧ S S))
         (~-trans {s = ⟦ S • S ⟧} {t = ⟦ ε ⟧} {u = ε∙} hS ⟦ε⟧)
  h2 : (sS ∙ (tc ∙ sS)) ~ tc
  h2 = ~-trans {s = sS ∙ (tc ∙ sS)} {t = ⟦ S • (c • S) ⟧} {u = tc}
         (~-sym {s = ⟦ S • (c • S) ⟧} {t = sS ∙ (tc ∙ sS)}
           (~-trans {s = ⟦ S • (c • S) ⟧} {t = sS ∙ ⟦ c • S ⟧} {u = sS ∙ (tc ∙ sS)}
             (⟦•⟧ S (c • S))
             (∙-cong {s = sS} {sS} {⟦ c • S ⟧} {tc ∙ sS} (~-refl sS) (⟦•⟧ c S))))
         hc

------------------------------------------------------------------------
-- The four windows

private
  CS₀₁ CS₃₄ : Circuit 5
  CS₀₁ = [ gate₂ CS-gate ]ʷ
  CS₃₄ = [ gate₂ CS-gate ↥ ↥ ↥ ]ʷ

  S₀ S₁ S₂ S₃ : Circuit 5
  S₀ = Swap
  S₁ = Swap ↑
  S₂ = Swap ↑ ↑
  S₃ = Swap ↑ ↑ ↑

  -- The placements.
  Y₀ Y₁ Y₂ Z₀ Z₁ Z₂ : Circuit 6
  Y₀ = P₆ (ns₆ (4 ∷ [])) Σ₀
  Y₁ = P₆ (ns₆ (3 ∷ 4 ∷ [])) Σ₀
  Y₂ = P₆ (ns₆ (2 ∷ 3 ∷ 4 ∷ [])) Σ₀
  Z₀ = P₆ (ns₆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂
  Z₁ = P₆ (ns₆ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) Σ₂
  Z₂ = P₆ (ns₆ (2 ∷ 3 ∷ 4 ∷ [])) Σ₂

  -- The controlled CS of the wires 0 1, and of 3 4.
  ctrl-gen : (g : Gen 5) → ⟦ λ¹ {1} g ⟧ ~ ctrl ⟦ [ g ]ʷ ⟧
  ctrl-gen g = ~-trans {s = ⟦ λ¹ {1} g ⟧} {t = ctrl (1 , ⟦ g ⟧ᵍ)} {u = ctrl ⟦ [ g ]ʷ ⟧}
                 (λ¹-gen g) (ctrl-~ {s = 1 , ⟦ g ⟧ᵍ} {t = ⟦ [ g ]ʷ ⟧} (~-sym {s = ⟦ [ g ]ʷ ⟧} {t = 1 , ⟦ g ⟧ᵍ} (⟦gen⟧ g)))

  ↑≈ : (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ σ n • top w • σ⁻¹ n
  ↑≈ {n} w = begin
    w ↑                         ≈⟨ sym right-unit ⟩
    w ↑ • ε                     ≈⟨ back _ (sym (σσ⁻¹ n)) ⟩
    w ↑ • σ n • σ⁻¹ n           ≈⟨ sym assoc ⟩
    (w ↑ • σ n) • σ⁻¹ n         ≈⟨ front _ (nat w) ⟩
    (σ n • top w) • σ⁻¹ n       ≈⟨ assoc ⟩
    σ n • top w • σ⁻¹ n ∎
    where open Tools ((₁₊ n) VRel,_===_)

  eY₀ : ⟦ Y₀ ⟧ ~ ctrl ⟦ CS₀₁ ⟧
  eY₀ = ~-trans {s = ⟦ Y₀ ⟧} {t = ⟦ Σᵗ 1 ⟧} {u = ctrl ⟦ CS₀₁ ⟧}
          (sound {w = Y₀} {v = Σᵗ 1} (by-assoc Eq.refl)) (ctrl-gen (gate₂ CS-gate))
    where open Tools (6 VRel,_===_)

  eY₁ : ⟦ Y₁ ⟧ ~ ctrl ⟦ CS₀₁ ⟧
  eY₁ = ~-trans {s = ⟦ Y₁ ⟧} {t = ⟦ top S₃ • (Y₀ • top S₃) ⟧} {u = ctrl ⟦ CS₀₁ ⟧}
          (sound {w = Y₁} {v = top S₃ • (Y₀ • top S₃)} (by-assoc Eq.refl))
          (win-sem S₃ CS₀₁ Y₀ (same-sem (S₃ • S₃) ε Eq.refl) (same-sem (S₃ • (CS₀₁ • S₃)) CS₀₁ Eq.refl) eY₀)
    where open Tools (6 VRel,_===_)

  eY₂ : ⟦ Y₂ ⟧ ~ ctrl ⟦ CS₀₁ ⟧
  eY₂ = ~-trans {s = ⟦ Y₂ ⟧} {t = ⟦ top S₂ • (Y₁ • top S₂) ⟧} {u = ctrl ⟦ CS₀₁ ⟧}
          (sound {w = Y₂} {v = top S₂ • (Y₁ • top S₂)} (by-assoc Eq.refl))
          (win-sem S₂ CS₀₁ Y₁ (same-sem (S₂ • S₂) ε Eq.refl) (same-sem (S₂ • (CS₀₁ • S₂)) CS₀₁ Eq.refl) eY₁)
    where open Tools (6 VRel,_===_)

  eZ₀ : ⟦ Z₀ ⟧ ~ ctrl ⟦ CS₃₄ ⟧
  eZ₀ = ~-trans {s = ⟦ Z₀ ⟧} {t = ⟦ Σ₂ ↑ ⟧} {u = ctrl ⟦ CS₃₄ ⟧}
          (sound {w = Z₀} {v = Σ₂ ↑} (sym (trans (↑≈ Σ₂) (by-assoc Eq.refl))))
          (ctrl-gen (gate₂ CS-gate ↥ ↥ ↥))
    where open Tools (6 VRel,_===_)

  -- Swap twice at both ends of a word cancels.
  cancel : (T : Circuit 6) (X : Circuit 6) → 6 ⊢ T • T ≈ ε → 6 ⊢ (T • T) • (X • (T • T)) ≈ X
  cancel T X e = trans (cong e (back _ e)) (trans left-unit right-unit)
    where open Tools (6 VRel,_===_)

  eZ₁ : ⟦ Z₁ ⟧ ~ ctrl ⟦ CS₃₄ ⟧
  eZ₁ = ~-trans {s = ⟦ Z₁ ⟧} {t = ⟦ top S₀ • (Z₀ • top S₀) ⟧} {u = ctrl ⟦ CS₃₄ ⟧}
          (sound {w = Z₁} {v = top S₀ • (Z₀ • top S₀)}
            (sym (trans (by-assoc Eq.refl) (cancel Swap Z₁ Swap²))))
          (win-sem S₀ CS₃₄ Z₀ (same-sem (S₀ • S₀) ε Eq.refl) (same-sem (S₀ • (CS₃₄ • S₀)) CS₃₄ Eq.refl) eZ₀)
    where open Tools (6 VRel,_===_)

  eZ₂ : ⟦ Z₂ ⟧ ~ ctrl ⟦ CS₃₄ ⟧
  eZ₂ = ~-trans {s = ⟦ Z₂ ⟧} {t = ⟦ top S₁ • (Z₁ • top S₁) ⟧} {u = ctrl ⟦ CS₃₄ ⟧}
          (sound {w = Z₂} {v = top S₁ • (Z₁ • top S₁)}
            (sym (trans (by-assoc Eq.refl) (cancel (Swap ↑) Z₂ (lemma-cong↑ (Swap • Swap) ε Swap²)))))
          (win-sem S₁ CS₃₄ Z₁ (same-sem (S₁ • S₁) ε Eq.refl) (same-sem (S₁ • (CS₃₄ • S₁)) CS₃₄ Eq.refl) eZ₁)
    where open Tools (6 VRel,_===_)

  -- Two placements denoting the same controlled operator.
  same : {Y Y′ : Circuit 6} {c : Circuit 5} → ⟦ Y ⟧ ~ ctrl ⟦ c ⟧ → ⟦ Y′ ⟧ ~ ctrl ⟦ c ⟧ → ⟦ Y ⟧ ~ ⟦ Y′ ⟧
  same {Y} {Y′} {c} e e′ = ~-trans {s = ⟦ Y ⟧} {t = ctrl ⟦ c ⟧} {u = ⟦ Y′ ⟧} e (~-sym {s = ⟦ Y′ ⟧} {t = ctrl ⟦ c ⟧} e′)

windows₆ : Windows₆
windows₆ = record
  { w₁ = same {Y₀} {Y₁} {CS₀₁} eY₀ eY₁
  ; w₂ = same {Y₁} {Y₂} {CS₀₁} eY₁ eY₂
  ; w₃ = same {Z₀} {Z₁} {CS₃₄} eZ₀ eZ₁
  ; w₄ = same {Z₁} {Z₂} {CS₃₄} eZ₁ eZ₂
  }
