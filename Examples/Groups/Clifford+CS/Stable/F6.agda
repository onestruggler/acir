------------------------------------------------------------------------
-- Presentations of groups
--
-- (F6) on five wires, in Lambda's spelling
--
-- Stable.GadgetAll's five-wire input (`Gadget.TopTarget 0`): λ⁰ of a
-- four-wire gadget commutes with the CX from a wire 1, 2 or 3 onto the
-- top.  Five.Gadget5 proves it for the CX from wire 1 (`f6`), over
-- Five.Calc's reading of λ⁰ as a list of macro letters, in Five's
-- theory.  Lambda's λ¹ on a four-wire domain is Five.Lambda's λ₁ letter
-- for letter (`λ¹≡`, sixteen cases by `refl`), so that reading is
-- Lambda's λ⁰ (`Λ⁰≈`); the CX of Affine.Circuits is Five's macro CX14,
-- conjugated by the exchanges of the wires 1 2 and 2 3 for the controls
-- 2 and 3 (`cx`, by evaluation on five wires after replacing bring₂'s
-- network by a concrete one), and those exchanges pass λ⁰ of the gadget
-- (CalcW.pass⁰ with Five.Facts4's sw₁, sw₂).  So `f6`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.F6
  (c4 : Complete 4) (c₅ : Completeᵧ 5)
  (f4₀ : F4ᵗ 0) (f5₀ : F5ᵗ 0)
  (tr₀ : ∀ {u v : Circuit 4} → 4 ⊢ᵧ u ≈ v → 5 ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Fin using (Fin ; toℕ ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (_<_ ; s≤s)
open import Data.Product using (proj₁ ; proj₂)
import Data.Empty.Irrelevant as Irr
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; same-sem)
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₂)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; λ⁰ʷ ; Xᵗ)
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁)
open import Examples.Groups.Clifford+CS.Five.Letters using (Mac ; ⟪_⟫ ; X4 ; CX14)
open import Examples.Groups.Clifford+CS.Five.Lines 5 Mac ⟪_⟫ using (⟪_⟫ʷ ; ⟪⟫-++)
open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.Inputs5 using (inputs)
open import Examples.Groups.Clifford+CS.Five.MissingInst using (missing)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed ; embed₅)
import Examples.Groups.Clifford+CS.Five.Calc as Calc5
import Examples.Groups.Clifford+CS.Five.Gadget5 as Gadget5
import Examples.Groups.Clifford+CS.Affine.Theory 4 as A₁
import Examples.Groups.Clifford+CS.Affine.Circuits 1 c4 as C₁
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW

open Facts4 F using (G ; sw₁ ; sw₂)

private
  I : Inputs
  I = inputs c4 (missing c4)

  module G5 = Gadget5 I F
  module FC = Calc5 (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I)
  module CW = CalcW 0 f4₀ f5₀ tr₀

  open Tools (5 YVRel,_===_)

  ≡→≈ : ∀ {a b : Circuit 5} → a ≡ b → 5 ⊢ᵧ a ≈ b
  ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- Five's reading of λ⁰ is Lambda's

λ¹≡ : ∀ (g : Gen 4) → ⟪ λ₁ g ⟫ ≡ λ¹ {0} g
λ¹≡ (gate₀ I-gate)              = Eq.refl
λ¹≡ (gate₁ S-gate)              = Eq.refl
λ¹≡ (gate₁ K-gate)              = Eq.refl
λ¹≡ (gate₂ CS-gate)             = Eq.refl
λ¹≡ (gate₀ I-gate ↥)            = Eq.refl
λ¹≡ (gate₁ S-gate ↥)            = Eq.refl
λ¹≡ (gate₁ K-gate ↥)            = Eq.refl
λ¹≡ (gate₂ CS-gate ↥)           = Eq.refl
λ¹≡ (gate₀ I-gate ↥ ↥)          = Eq.refl
λ¹≡ (gate₁ S-gate ↥ ↥)          = Eq.refl
λ¹≡ (gate₁ K-gate ↥ ↥)          = Eq.refl
λ¹≡ (gate₂ CS-gate ↥ ↥)         = Eq.refl
λ¹≡ (gate₀ I-gate ↥ ↥ ↥)        = Eq.refl
λ¹≡ (gate₁ S-gate ↥ ↥ ↥)        = Eq.refl
λ¹≡ (gate₁ K-gate ↥ ↥ ↥)        = Eq.refl
λ¹≡ (gate₀ I-gate ↥ ↥ ↥ ↥)      = Eq.refl

Λ⁰≈ : ∀ (w : Circuit 4) → 5 ⊢ᵧ ⟪ FC.λ⁰ʷ w ⟫ʷ ≈ λ⁰ʷ w
Λ⁰≈ [ g ]ʷ  = ≡→≈ (Eq.cong (λ x → Xᵗ 4 • x • Xᵗ 4) (λ¹≡ g))
Λ⁰≈ ε       = refl
Λ⁰≈ (u • v) = trans (embed₅ (⟪⟫-++ (FC.λ⁰ʷ u) (FC.λ⁰ʷ v))) (cong (Λ⁰≈ u) (Λ⁰≈ v))

------------------------------------------------------------------------
-- The CX onto the top

private
  Pass : Circuit 5 → Circuit 5 → Set
  Pass L x = 5 ⊢ᵧ x • L ≈ L • x

  pass-• : ∀ {L a b} → Pass L a → Pass L b → Pass L (a • b)
  pass-• {L} {a} {b} pa pb = begin
    (a • b) • L     ≈⟨ assoc ⟩
    a • (b • L)     ≈⟨ back a pb ⟩
    a • (L • b)     ≈⟨ sym assoc ⟩
    (a • L) • b     ≈⟨ front b pa ⟩
    (L • a) • b     ≈⟨ assoc ⟩
    L • (a • b)     ∎

  pass≈ : ∀ {L x y} → 5 ⊢ᵧ x ≈ y → Pass L y → Pass L x
  pass≈ e p = trans (front _ e) (trans p (back _ (sym e)))

  -- The CX from wire 1 onto the top, and the exchanges below the top.
  pA : ∀ V → Pass (λ⁰ʷ (G V)) ⟪ CX14 ⟫
  pA V = trans (back _ (sym (Λ⁰≈ (G V)))) (trans (embed₅ (G5.f6 V)) (front _ (Λ⁰≈ (G V))))

  ps₁ : ∀ V → Pass (λ⁰ʷ (G V)) (Swap ↑)
  ps₁ V = CW.pass⁰ (Swap ↑) (G V) (embed (sw₁ V))

  ps₂ : ∀ V → Pass (λ⁰ʷ (G V)) (Swap ↑ ↑)
  ps₂ V = CW.pass⁰ (Swap ↑ ↑) (G V) (embed (sw₂ V))

  back-to : ∀ (σ : Word (S.Gen 5)) {a i} → perm σ ⟨$⟩ʳ a ≡ i → perm (revS σ) ⟨$⟩ʳ i ≡ a
  back-to σ {a} e = Eq.subst (λ x → perm (revS σ) ⟨$⟩ʳ x ≡ a) e (perm-inv σ a)

  tp : Fin 5
  tp = fromℕ 4

  cxu : ∀ (u : Fin 3) .(p : sF (inject₁ u) ≢ tp) → Circuit 5
  cxu u p = C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫

  -- The CX placed by a concrete network with the same action.
  by : ∀ (u : Fin 3) .(p : sF (inject₁ u) ≢ tp) (ν : Word (S.Gen 5)) (x : Circuit 5) →
       perm ν ⟨$⟩ʳ tp ≡ 0F → perm ν ⟨$⟩ʳ sF (inject₁ u) ≡ sF 0F → Same (pl ν CX₁₀) x →
       5 ⊢ᵧ cxu u p ≈ x
  by u p ν x e0 e1 s =
    trans (embed (place-eq {k = 2} CX₁₀ b ν agree)) (c₅ (same-sem (pl ν CX₁₀) x s))
    where
    B = bring₂ tp (sF (inject₁ u)) (C₁.ne p)
    b = proj₁ B
    agree : ∀ (j : Fin 5) → toℕ j < 2 → perm ν ⟨$⟩ʳ (perm (revS b) ⟨$⟩ʳ j) ≡ j
    agree 0F _          = Eq.trans (Eq.cong (perm ν ⟨$⟩ʳ_) (back-to b (proj₁ (proj₂ B)))) e0
    agree (sF 0F) _     = Eq.trans (Eq.cong (perm ν ⟨$⟩ʳ_) (back-to b (proj₂ (proj₂ B)))) e1
    agree (sF (sF j)) (s≤s (s≤s ()))

  σ₀ σ₁ σ₂ σ₃ : Word (S.Gen 5)
  σ₀ = S.σ
  σ₁ = S.σ S.↑
  σ₂ = S.σ S.↑ S.↑
  σ₃ = S.σ S.↑ S.↑ S.↑

-- (F6) on five wires: Stable.Gadget's TopTarget 0 for the gadgets.
f6 : ∀ V (u : Fin 3) .(p : sF (inject₁ u) ≢ tp) →
     5 ⊢ᵧ C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫ • λ⁰ʷ (G V) ≈ λ⁰ʷ (G V) • C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫
f6 V 0F p =
  pass≈ (by 0F p (σ₃ • σ₂ • σ₁ • σ₀ • σ₁) ⟪ CX14 ⟫ Eq.refl Eq.refl Eq.refl) (pA V)
f6 V (sF 0F) p =
  pass≈ (by (sF 0F) p (σ₃ • σ₂ • σ₁ • σ₀ • σ₂ • σ₁) (Swap ↑ • ⟪ CX14 ⟫ • Swap ↑) Eq.refl Eq.refl Eq.refl)
        (pass-• (ps₁ V) (pass-• (pA V) (ps₁ V)))
f6 V (sF (sF 0F)) p =
  pass≈ (by (sF (sF 0F)) p (σ₃ • σ₂ • σ₁ • σ₀ • σ₃ • σ₂ • σ₁) (Swap ↑ ↑ • Swap ↑ • ⟪ CX14 ⟫ • Swap ↑ • Swap ↑ ↑) Eq.refl Eq.refl Eq.refl)
        (pass-• (ps₂ V) (pass-• (ps₁ V) (pass-• (pA V) (pass-• (ps₁ V) (ps₂ V)))))
