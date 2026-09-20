------------------------------------------------------------------------
-- Presentations of groups
--
-- Two doubly controlled H gates of different colours, continued
-- (Clément, Lemma D.5, Equations (203)–(207))
--
--   (203)   H(1, 3; 0, 2)      H(0, 3; 1, °2)
--   (204)   H(0, 1; 2, 3)      H(1, 3; 0, °2)
--   (205)   H(2, 1; 0, 3)      H(0, 2; 1, °3)
--   (206)   H(1, 2; 0, 3)      H(2, 1; 0, °3)
--   (207)   X on wire 0        H(1, 0; 2, 3)
--
-- (204) and (205) are (181) and (189) through the Klein four-group of
-- HGates.  In (203) the two gates share their box wire, and the third
-- P ⊗ P of the triangle sits on two controls of a box, where it makes no
-- H gate: the statement becomes
--
--   Box(3; 0, 1, 2)  against  P ⊗ P on 0 1 around Box(3; 0, 1, °2).
--
-- Both boxes move their box wire to wire 1 by (177), and P ⊗ P then does
-- make H gates of the boxes on wire 1: each side is a product of a doubly
-- controlled rotation of wire 3 and an H gate (black on one side, white
-- on the other), and the four kinds of factor commute pairwise — rotation
-- against rotation by one three-wire evaluation (Evals203), rotation
-- against H gate as in (181), H gate against box by (196).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.HGates2
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex² ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Ev complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals181 complete₂ complete₃
  using (ev-PP-HC ; ev-°R-CCZX)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals203 complete₂ complete₃
  using (ev-203)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq154 ; eq155 ; eq157)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top ; eq179)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; eq177)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; ΛH₂′-rot′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (tr ; N₂-box₃′ ; eq189)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (S₂₃-box₃′ ; S₂₃-°box₃ ; eq196)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; eq117 ; eq118 ; eq130)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- (204), (205)

-- (204): H(0, 1; 2, 3) against H(1, 3; 0, °2), from (181).
eq204 : (₄₊ n) ⊢ ΛH₀₁ • S₀₁.⟪ °ΛH₂′ ⟫ ≈ S₀₁.⟪ °ΛH₂′ ⟫ • ΛH₀₁
eq204 {n} = begin
  ΛH₀₁ • S₀₁.⟪ °ΛH₂′ ⟫
    ≈⟨ cong ΛH₀₁-PP S₀₁-°ΛH₂′-PP ⟩
  (PP₀₁ • box₃′ • PP₀₁) • (PP₁₃ • °box₃‴ • PP₁₃)
    ≈⟨ klein Γ PP₀₁² PP₁₃² PP₀₃² (klein-ab Γ PP₀₁² PP-triangle) e181 ⟩
  (PP₁₃ • °box₃‴ • PP₁₃) • (PP₀₁ • box₃′ • PP₀₁)
    ≈⟨ sym (cong S₀₁-°ΛH₂′-PP ΛH₀₁-PP) ⟩
  S₀₁.⟪ °ΛH₂′ ⟫ • ΛH₀₁ ∎
  where
  Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  e181 : (₄₊ n) ⊢ box₃′ • (PP₀₃ • °box₃‴ • PP₀₃) ≈ (PP₀₃ • °box₃‴ • PP₀₃) • box₃′
  e181 = trans (back _ (sym °ΛH₂′-PP)) (trans eq181 (front _ °ΛH₂′-PP))

-- (205): H(2, 1; 0, 3) against H(0, 2; 1, °3), from (189), on the
-- triangle 0 1 2.
private
  PP₁₂ PP₀₂ : Circuit (₄₊ n)
  PP₁₂ = PP ↑
  PP₀₂ = O PP

  PP₁₂² : (₄₊ n) ⊢ PP₁₂ • PP₁₂ ≈ ε
  PP₁₂² = U-sem (PP • PP) ε Eq.refl

  PP₀₂² : (₄₊ n) ⊢ PP₀₂ • PP₀₂ ≈ ε
  PP₀₂² {n} = conj-invol Ex² PP₁₂²
    where open Tools ((₄₊ n) VRel,_===_)

  -- (130)
  PP-triangle₂ : (₄₊ n) ⊢ PP₀₁ • PP₁₂ ≈ PP₀₂
  PP-triangle₂ {n} = trans eq130 (O-L PP)
    where open Tools ((₄₊ n) VRel,_===_)

  -- The box with its box wire on wire 2 and its control on wire 3 white.
  box₃″° : Circuit (₄₊ n)
  box₃″° = N₃.⟪ S₁₂.⟪ box₃′ ⟫ ⟫

  -- The two H gates as boxes between P ⊗ P.
  G-PP : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ≈ PP₁₂ • box₃′ • PP₁₂
  G-PP {n} = trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-•₃ (O-L PP) eq157 (O-L PP)))
                   (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ (U PP)) refl (S₀₁.⟪⟫-⟪⟫ (U PP)))
    where open Tools ((₄₊ n) VRel,_===_)

  N₃-PP₀₂ : (₄₊ n) ⊢ N₃.⟪ PP₀₂ ⟫ ≈ PP₀₂
  N₃-PP₀₂ {n} = N₃.⟪⟫-fix (sym (L₃-top (O₀ PP) X))
    where open Tools ((₄₊ n) VRel,_===_)

  G′-PP : (₄₊ n) ⊢ N₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ≈ PP₀₂ • box₃″° • PP₀₂
  G′-PP {n} = trans (N₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong ΛH₀₁-PP) (S₁₂.⟪⟫-•₃ (O-L PP) refl (O-L PP))))
                    (N₃.⟪⟫-•₃ N₃-PP₀₂ refl N₃-PP₀₂)
    where open Tools ((₄₊ n) VRel,_===_)

  -- (189), in these spellings.
  e189 : (₄₊ n) ⊢ box₃″° • (PP₀₁ • box₃′ • PP₀₁) ≈ (PP₀₁ • box₃′ • PP₀₁) • box₃″°
  e189 {n} = sym (begin
    (PP₀₁ • box₃′ • PP₀₁) • box₃″°
      ≈⟨ sym (cong (trans H-bridge ΛH₀₁-PP) B-bridge) ⟩
    S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫
      ≈⟨ eq189 ⟩
    S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫
      ≈⟨ cong B-bridge (trans H-bridge ΛH₀₁-PP) ⟩
    box₃″° • (PP₀₁ • box₃′ • PP₀₁) ∎)
    where
    open Tools ((₄₊ n) VRel,_===_)
    H-bridge : (₄₊ n) ⊢ S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫ ≈ ΛH₀₁
    H-bridge = trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ (S₁₂.⟪ ΛH₀₁ ⟫))) (S₁₂.⟪⟫-⟪⟫ ΛH₀₁)
    B-bridge : (₄₊ n) ⊢ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ≈ box₃″°
    B-bridge = trans (S₁₂.⟪⟫-cong (trans (S₂₃.⟪⟫-•₃ (L-S₂₃ Ex) S₂₃-°box₃ (L-S₂₃ Ex)) (S₀₁-N₃ box₃)))
                     (S₁₂-N₃ box₃′)

eq205 : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ • N₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫
               ≈ N₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ • S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫
eq205 {n} = begin
  S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ • N₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫
    ≈⟨ cong G-PP G′-PP ⟩
  (PP₁₂ • box₃′ • PP₁₂) • (PP₀₂ • box₃″° • PP₀₂)
    ≈⟨ sym (klein Γ PP₀₂² PP₁₂² PP₀₁² (klein-ba Γ PP₀₁² PP₀₂² PP₁₂² PP-triangle₂) e189) ⟩
  (PP₀₂ • box₃″° • PP₀₂) • (PP₁₂ • box₃′ • PP₁₂)
    ≈⟨ sym (cong G′-PP G-PP) ⟩
  N₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ • S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ∎
  where
  Γ = (₄₊ n) VRel,_===_
  open Tools Γ

------------------------------------------------------------------------
-- (1 3) and (0 3) on what (203) is made of

T₀₃-via : {w w₁ w₂ w₃ : Circuit (₄₊ n)} →
          (₄₊ n) ⊢ S₀₁.⟪ w ⟫ ≈ w₁ → (₄₊ n) ⊢ T₁₃.⟪ w₁ ⟫ ≈ w₂ → (₄₊ n) ⊢ S₀₁.⟪ w₂ ⟫ ≈ w₃ →
          (₄₊ n) ⊢ T₀₃.⟪ w ⟫ ≈ w₃
T₀₃-via {n} {w} p q r =
  trans (T₀₃-nest w) (trans (S₀₁.⟪⟫-cong (trans (T₁₃.⟪⟫-cong p) q)) r)
  where open Tools ((₄₊ n) VRel,_===_)

T₀₃-L : (u : Circuit 2) → (₄₊ n) ⊢ T₀₃.⟪ L u ⟫ ≈ P₁₃ (Ex • u • Ex)
T₀₃-L {n} u = T₀₃-via {w₁ = L (Ex • u • Ex)} refl (T₁₃-L (Ex • u • Ex))
                      (S₀₁.⟪⟫-⟪⟫ (P₁₃ (Ex • u • Ex)))
  where open Tools ((₄₊ n) VRel,_===_)

T₀₃-O : (u : Circuit 2) → (₄₊ n) ⊢ T₀₃.⟪ O u ⟫ ≈ P₂₃ (Ex • u • Ex)
T₀₃-O {n} u = T₀₃-via (S₀₁.⟪⟫-⟪⟫ (U u)) (T₁₃-U u) (P₂₃-S₀₁ ((Ex • u • Ex) ↓ᵏ n))

T₀₃-box₃ : (₄₊ n) ⊢ T₀₃.⟪ box₃ ⟫ ≈ box₃‴
T₀₃-box₃ {n} = begin
  T₀₃.⟪ box₃ ⟫                        ≈⟨ T₀₃-nest′ box₃ ⟩
  T₁₃.⟪ S₀₁.⟪ T₁₃.⟪ box₃ ⟫ ⟫ ⟫        ≈⟨ T₁₃.⟪⟫-cong (S₀₁.⟪⟫-cong T₁₃-box₃) ⟩
  T₁₃.⟪ box₃′ ⟫                       ≈⟨ T₁₃-nest box₃′ ⟩
  S₂₃.⟪ S₁₂.⟪ S₂₃.⟪ box₃′ ⟫ ⟫ ⟫       ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong S₂₃-box₃′) ⟩
  box₃‴ ∎
  where open Tools ((₄₊ n) VRel,_===_)

T₀₃-box₃′ : (₄₊ n) ⊢ T₀₃.⟪ box₃′ ⟫ ≈ box₃′
T₀₃-box₃′ {n} = T₀₃-via (S₀₁.⟪⟫-⟪⟫ box₃) T₁₃-box₃ refl
  where open Tools ((₄₊ n) VRel,_===_)

-- X on wire 2 against a two-wire circuit on the wires 1 and 3.
X₂-P₁₃ : (u : Circuit 2) → (₄₊ n) ⊢ X ↑ ↑ • P₁₃ u ≈ P₁₃ u • X ↑ ↑
X₂-P₁₃ {n} u = S₁₂.⟪⟫-≈ X₁-P₂₃ (S₁₂.⟪⟫-•₂ S₁₂-X₁ refl) (S₁₂.⟪⟫-•₂ refl S₁₂-X₁)
  where
  open Tools ((₄₊ n) VRel,_===_)
  X₁-P₂₃ : (₄₊ n) ⊢ X ↑ • P₂₃ u ≈ P₂₃ u • X ↑
  X₁-P₂₃ = lemma-cong↑ (X ↓ • (u ↓ᵏ n) ↑) ((u ↓ᵏ n) ↑ • X ↓) (comm-↓↑ X (u ↓ᵏ n))

------------------------------------------------------------------------
-- (203)

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    a â ẑ °ẑ ê ĥ °ĥ d Ŵ Ŵ⁻ °Ŵ °Ŵ⁻ W₁ V₁ °h : Circuit (₄₊ n)
    a   = CH ↓
    â   = P₁₃ HC
    ẑ   = P₂₃ CZ
    °ẑ  = P₂₃ CZ°
    ê   = P₁₃ CH
    ĥ   = P₂₃ HC
    °ĥ  = P₂₃ HC°
    d   = P₁₃ CZ
    Ŵ   = â • ẑ • â • ẑ
    Ŵ⁻  = ẑ • â • ẑ • â
    °Ŵ  = â • °ẑ • â • °ẑ
    °Ŵ⁻ = °ẑ • â • °ẑ • â
    W₁  = CCZX ↑
    V₁  = CCXZ ↑
    °h  = N₂.⟪ ΛH₀₁ ⟫

    ------------------------------------------------------------------
    -- Involutions and inverses

    P₂₃-sem : (u v : Circuit 2) → (₃₊ n) ⊢ U u ≈ U v → (₄₊ n) ⊢ P₂₃ u ≈ P₂₃ v
    P₂₃-sem u v e = lemma-cong↑ (U u) (U v) e

    P₁₃-sem : (u v : Circuit 2) → (₃₊ n) ⊢ U u ≈ U v → (₄₊ n) ⊢ P₁₃ u ≈ P₁₃ v
    P₁₃-sem u v e = S₁₂.⟪⟫-cong (P₂₃-sem u v e)

    â² : â • â ≈ ε
    â² = conj-invol Ex₁² (lemma-cong↑ (U (HC • HC)) ε (U-sem (HC • HC) ε Eq.refl))

    ẑ² : ẑ • ẑ ≈ ε
    ẑ² = lemma-cong↑ (U (CZ • CZ)) ε (U-sem (CZ • CZ) ε Eq.refl)

    °ẑ² : °ẑ • °ẑ ≈ ε
    °ẑ² = lemma-cong↑ (U (CZ° • CZ°)) ε (U-sem (CZ° • CZ°) ε Eq.refl)

    ŴŴ⁻ : Ŵ • Ŵ⁻ ≈ ε
    ŴŴ⁻ = invol-abab â² ẑ²

    Ŵ⁻Ŵ : Ŵ⁻ • Ŵ ≈ ε
    Ŵ⁻Ŵ = invol-abab ẑ² â²

    °Ŵ°Ŵ⁻ : °Ŵ • °Ŵ⁻ ≈ ε
    °Ŵ°Ŵ⁻ = invol-abab â² °ẑ²

    °Ŵ⁻°Ŵ : °Ŵ⁻ • °Ŵ ≈ ε
    °Ŵ⁻°Ŵ = invol-abab °ẑ² â²

    W₁V₁ : W₁ • V₁ ≈ ε
    W₁V₁ = lemma-cong↑ (CCZX • CCXZ) ε eq117

    V₁W₁ : V₁ • W₁ ≈ ε
    V₁W₁ = lemma-cong↑ (CCXZ • CCZX) ε eq118

    -- w passes y, so its inverse does.
    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    ------------------------------------------------------------------
    -- The boxes on wire 3 from the boxes on wire 1: (177) under (0 3)

    T-b : T₀₃.⟪ CZ₂₀ ⟫ ≈ ẑ
    T-b = trans (T₀₃-O CZ) (P₂₃-sem (Ex • CZ • Ex) CZ (U-sem (Ex • CZ • Ex) CZ Eq.refl))

    x-form : box₃‴ ≈ Ŵ • box₃′ • Ŵ⁻ • box₃′
    x-form = trans (sym T₀₃-box₃) (trans (T₀₃.⟪⟫-cong eq177)
      (T₀₃.⟪⟫-•₄ (T₀₃.⟪⟫-•₄ (T₀₃-L CH) T-b (T₀₃-L CH) T-b) T₀₃-box₃′
                 (T₀₃.⟪⟫-•₄ T-b (T₀₃-L CH) T-b (T₀₃-L CH)) T₀₃-box₃′))

    N₂-â : N₂.⟪ â ⟫ ≈ â
    N₂-â = N₂.⟪⟫-fix (X₂-P₁₃ HC)

    N₂-Ŵ : N₂.⟪ Ŵ ⟫ ≈ °Ŵ
    N₂-Ŵ = N₂.⟪⟫-•₄ N₂-â refl N₂-â refl

    N₂-Ŵ⁻ : N₂.⟪ Ŵ⁻ ⟫ ≈ °Ŵ⁻
    N₂-Ŵ⁻ = N₂.⟪⟫-•₄ refl N₂-â refl N₂-â

    N₂-°Ŵ : N₂.⟪ °Ŵ ⟫ ≈ Ŵ
    N₂-°Ŵ = trans (N₂.⟪⟫-cong (sym N₂-Ŵ)) (N₂.⟪⟫-⟪⟫ Ŵ)

    °x-form : °box₃‴ ≈ °Ŵ • S₀₁.⟪ °box₃ ⟫ • °Ŵ⁻ • S₀₁.⟪ °box₃ ⟫
    °x-form = trans (N₂.⟪⟫-cong x-form) (N₂.⟪⟫-•₄ N₂-Ŵ N₂-box₃′ N₂-Ŵ⁻ N₂-box₃′)

    ------------------------------------------------------------------
    -- The H gate on the wires 0 1 as a rotation of wire 1 around the CH
    -- below: (1 3) on the form of the H gate with its box wire on wire 3

    ΛH₀₁-rot : ΛH₀₁ ≈ V₁ • a • W₁ • a
    ΛH₀₁-rot = trans (sym T₁₃-ΛH₂′) (trans (T₁₃.⟪⟫-cong ΛH₂′-rot′)
      (T₁₃.⟪⟫-•₄ (T₁₃.⟪⟫-•₄ T-d T-h T-d T-h) (T₁₃-P₀₃ CH)
                 (T₁₃.⟪⟫-•₄ T-h T-d T-h T-d) (T₁₃-P₀₃ CH)))
      where
      T-d : T₁₃.⟪ P₁₃ CZ ⟫ ≈ P₁₃ CZ
      T-d = trans (T₁₃-P₁₃ CZ) (P₁₃-sem (Ex • CZ • Ex) CZ (U-sem (Ex • CZ • Ex) CZ Eq.refl))
      T-h : T₁₃.⟪ P₂₃ HC ⟫ ≈ U CH
      T-h = trans (T₁₃-P₂₃ HC) (U-sem (Ex • HC • Ex) CH Eq.refl)

    -- The white rotation of wire 3 passes it: the rotation of wire 1 as
    -- in (181), the CH below factor by factor.
    W₁-°Ŵ⁻ : W₁ • °Ŵ⁻ ≈ °Ŵ⁻ • W₁
    W₁-°Ŵ⁻ = sym (U₃-comm-ev ev-°R-CCZX)

    W₁-°Ŵ : W₁ • °Ŵ ≈ °Ŵ • W₁
    W₁-°Ŵ = comm-inv °Ŵ⁻°Ŵ °Ŵ°Ŵ⁻ W₁-°Ŵ⁻

    V₁-°Ŵ : V₁ • °Ŵ ≈ °Ŵ • V₁
    V₁-°Ŵ = inv-row W₁V₁ V₁W₁ W₁-°Ŵ

    a-â : a • â ≈ â • a
    a-â = comm-01-13 CH HC (evaluated Eq.refl)

    a-°ẑ : a • °ẑ ≈ °ẑ • a
    a-°ẑ = sym (P₂₃-L CZ° CH)

    a-°Ŵ : a • °Ŵ ≈ °Ŵ • a
    a-°Ŵ = comm-abab a-â a-°ẑ

    ΛH₀₁-°Ŵ : ΛH₀₁ • °Ŵ ≈ °Ŵ • ΛH₀₁
    ΛH₀₁-°Ŵ = begin
      ΛH₀₁ • °Ŵ                    ≈⟨ front _ ΛH₀₁-rot ⟩
      (V₁ • a • W₁ • a) • °Ŵ       ≈⟨ sym (comm-• (sym V₁-°Ŵ) (comm-• (sym a-°Ŵ)
                                         (comm-• (sym W₁-°Ŵ) (sym a-°Ŵ)))) ⟩
      °Ŵ • (V₁ • a • W₁ • a)       ≈⟨ back _ (sym ΛH₀₁-rot) ⟩
      °Ŵ • ΛH₀₁ ∎

    -- With the colours exchanged.
    °h-Ŵ : °h • Ŵ ≈ Ŵ • °h
    °h-Ŵ = N₂.⟪⟫-≈ ΛH₀₁-°Ŵ (N₂.⟪⟫-•₂ refl N₂-°Ŵ) (N₂.⟪⟫-•₂ N₂-°Ŵ refl)

    ------------------------------------------------------------------
    -- P ⊗ P around the rotations

    -- On 1 3: the CH onto wire 3 turns over, (114); the CZ of 2 3 becomes
    -- the CH onto wire 3.
    C-â : PP₁₃ • â • PP₁₃ ≈ ê
    C-â = trans (sym (trans (P₁₃-• PP (HC • PP)) (back _ (P₁₃-• HC PP))))
                (P₁₃-sem (PP • HC • PP) CH (U-sem (PP • HC • PP) CH Eq.refl))

    C-ĥ : PP₁₃ • ĥ • PP₁₃ ≈ ẑ
    C-ĥ = U₃-ev ev-PP-HC

    C-ẑ : PP₁₃ • ẑ • PP₁₃ ≈ ĥ
    C-ẑ = conj-sym PP₁₃² C-ĥ

    -- On 0 3: the CH from wire 1 onto wire 3 becomes their CZ; the CZ of
    -- 2 3 the CH onto wire 3, in either colour.
    B-â : PP₀₃ • â • PP₀₃ ≈ d
    B-â = begin
      PP₀₃ • â • PP₀₃
        ≈⟨ sym (cong (M₃-O PP) (cong (M₃-U HC) (M₃-O PP))) ⟩
      M₃ (O₀ PP) • M₃ (U₀ HC) • M₃ (O₀ PP)
        ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
      M₃ (O₀ PP • U₀ HC • O₀ PP)
        ≈⟨ M₃-ev ev-PP-HC ⟩
      M₃ (U₀ CZ)
        ≈⟨ M₃-U CZ ⟩
      d ∎

    B-ĥ : PP₀₃ • ĥ • PP₀₃ ≈ ẑ
    B-ĥ = begin
      PP₀₃ • ĥ • PP₀₃
        ≈⟨ back _ (front _ (sym (P₂₃-S₀₁ HC))) ⟩
      O₃ (O₀ PP) • O₃ (U₀ HC) • O₃ (O₀ PP)
        ≈⟨ sym (S₀₁.⟪⟫-•₃ refl refl refl) ⟩
      O₃ (O₀ PP • U₀ HC • O₀ PP)
        ≈⟨ O₃-ev ev-PP-HC ⟩
      O₃ (U₀ CZ)
        ≈⟨ P₂₃-S₀₁ CZ ⟩
      ẑ ∎

    B-ẑ : PP₀₃ • ẑ • PP₀₃ ≈ ĥ
    B-ẑ = conj-sym PP₀₃² B-ĥ

    B-°ẑ : PP₀₃ • °ẑ • PP₀₃ ≈ °ĥ
    B-°ẑ = N₂.⟪⟫-≈ B-ẑ (N₂.⟪⟫-•₃ N₂-PP₀₃ refl N₂-PP₀₃) refl

  private
    module Cj = Conj {₄₊ n} PP₁₃ PP₁₃²
    module Bj = Conj {₄₊ n} PP₀₃ PP₀₃²
    module Aj = Conj {₄₊ n} PP₀₁ PP₀₁²

  private
    -- The black rotation against the white one between P ⊗ P on 0 1:
    -- conjugated by P ⊗ P on 1 3, the evaluation.
    P Q : Circuit (₄₊ n)
    P = Aj.⟪ °Ŵ ⟫
    Q = Aj.⟪ °Ŵ⁻ ⟫

    CA : PP₁₃ • PP₀₁ ≈ PP₀₃
    CA = klein-ca Γ PP₀₁² PP₀₃² PP₁₃² PP-triangle

    C-Ŵ : Cj.⟪ Ŵ ⟫ ≈ ê • ĥ • ê • ĥ
    C-Ŵ = Cj.⟪⟫-•₄ C-â C-ẑ C-â C-ẑ

    C-P : Cj.⟪ P ⟫ ≈ d • °ĥ • d • °ĥ
    C-P = begin
      PP₁₃ • (PP₀₁ • °Ŵ • PP₀₁) • PP₁₃
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (PP₁₃ • PP₀₁) • °Ŵ • (PP₀₁ • PP₁₃)
        ≈⟨ cong CA (back _ PP-triangle) ⟩
      PP₀₃ • °Ŵ • PP₀₃
        ≈⟨ Bj.⟪⟫-•₄ B-â B-°ẑ B-â B-°ẑ ⟩
      d • °ĥ • d • °ĥ ∎

    back-C : ∀ {w w′ : Circuit (₄₊ n)} → Cj.⟪ w ⟫ ≈ w′ → Cj.⟪ w′ ⟫ ≈ w
    back-C {w} e = trans (Cj.⟪⟫-cong (sym e)) (Cj.⟪⟫-⟪⟫ w)

    P-Ŵ : P • Ŵ ≈ Ŵ • P
    P-Ŵ = sym (Cj.⟪⟫-≈ (U₃-comm-ev ev-203)
      (Cj.⟪⟫-•₂ (back-C C-Ŵ) (back-C C-P))
      (Cj.⟪⟫-•₂ (back-C C-P) (back-C C-Ŵ)))

    P-Ŵ⁻ : P • Ŵ⁻ ≈ Ŵ⁻ • P
    P-Ŵ⁻ = comm-inv ŴŴ⁻ Ŵ⁻Ŵ P-Ŵ

    -- The H gate is the box on wire 1 between P ⊗ P on 0 1.
    A-ΛH₀₁ : Aj.⟪ ΛH₀₁ ⟫ ≈ box₃′
    A-ΛH₀₁ = trans (Aj.⟪⟫-cong ΛH₀₁-PP) (Aj.⟪⟫-⟪⟫ box₃′)

    P-b₁ : P • box₃′ ≈ box₃′ • P
    P-b₁ = Aj.⟪⟫-≈ (sym ΛH₀₁-°Ŵ) (Aj.⟪⟫-•₂ refl A-ΛH₀₁) (Aj.⟪⟫-•₂ A-ΛH₀₁ refl)

    PQ : P • Q ≈ ε
    PQ = trans (sym (Aj.⟪⟫-• °Ŵ °Ŵ⁻)) (trans (Aj.⟪⟫-cong °Ŵ°Ŵ⁻) Aj.⟪⟫-ε)

    QP : Q • P ≈ ε
    QP = trans (sym (Aj.⟪⟫-• °Ŵ⁻ °Ŵ)) (trans (Aj.⟪⟫-cong °Ŵ⁻°Ŵ) Aj.⟪⟫-ε)

    -- The white H gate against the black box on wire 1: (196).
    °h-b₁ : °h • box₃′ ≈ box₃′ • °h
    °h-b₁ = N₂.⟪⟫-≈ eq196 (N₂.⟪⟫-•₂ refl N₂-°b₁) (N₂.⟪⟫-•₂ N₂-°b₁ refl)
      where
      N₂-°b₁ : N₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ≈ box₃′
      N₂-°b₁ = trans (N₂.⟪⟫-cong (sym N₂-box₃′)) (N₂.⟪⟫-⟪⟫ box₃′)

    °h-Ŵ⁻ : °h • Ŵ⁻ ≈ Ŵ⁻ • °h
    °h-Ŵ⁻ = comm-inv ŴŴ⁻ Ŵ⁻Ŵ °h-Ŵ

    -- Each factor of the white side passes the black box on wire 3.
    pass : ∀ {f : Circuit (₄₊ n)} → f • Ŵ ≈ Ŵ • f → f • box₃′ ≈ box₃′ • f → f • Ŵ⁻ ≈ Ŵ⁻ • f →
           f • (Ŵ • box₃′ • Ŵ⁻ • box₃′) ≈ (Ŵ • box₃′ • Ŵ⁻ • box₃′) • f
    pass fW fb fV = comm-• fW (comm-• fb (comm-• fV fb))

    -- The white box on wire 3 between P ⊗ P on 0 1.
    AyA-form : PP₀₁ • °box₃‴ • PP₀₁ ≈ P • °h • Q • °h
    AyA-form = trans (Aj.⟪⟫-cong °x-form) (Aj.⟪⟫-•₄ refl A-°b₁ refl A-°b₁)
      where
      A-°b₁ : Aj.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ≈ °h
      A-°b₁ = sym (trans (N₂.⟪⟫-cong ΛH₀₁-PP) (N₂.⟪⟫-•₃ N₂-PP₀₁ N₂-box₃′ N₂-PP₀₁))

    core : box₃‴ • (PP₀₁ • °box₃‴ • PP₀₁) ≈ (PP₀₁ • °box₃‴ • PP₀₁) • box₃‴
    core = begin
      box₃‴ • (PP₀₁ • °box₃‴ • PP₀₁)
        ≈⟨ cong x-form AyA-form ⟩
      (Ŵ • box₃′ • Ŵ⁻ • box₃′) • (P • °h • Q • °h)
        ≈⟨ comm-• (sym P-x) (comm-• (sym °h-x) (comm-• (sym Q-x) (sym °h-x))) ⟩
      (P • °h • Q • °h) • (Ŵ • box₃′ • Ŵ⁻ • box₃′)
        ≈⟨ sym (cong AyA-form x-form) ⟩
      (PP₀₁ • °box₃‴ • PP₀₁) • box₃‴ ∎
      where
      P-x : P • (Ŵ • box₃′ • Ŵ⁻ • box₃′) ≈ (Ŵ • box₃′ • Ŵ⁻ • box₃′) • P
      P-x = pass P-Ŵ P-b₁ P-Ŵ⁻
      Q-x : Q • (Ŵ • box₃′ • Ŵ⁻ • box₃′) ≈ (Ŵ • box₃′ • Ŵ⁻ • box₃′) • Q
      Q-x = pass (inv-row PQ QP P-Ŵ) (inv-row PQ QP P-b₁) (inv-row PQ QP P-Ŵ⁻)
      °h-x : °h • (Ŵ • box₃′ • Ŵ⁻ • box₃′) ≈ (Ŵ • box₃′ • Ŵ⁻ • box₃′) • °h
      °h-x = pass °h-Ŵ °h-b₁ °h-Ŵ⁻

  -- (203): H(1, 3; 0, 2) against H(0, 3; 1, °2).
  eq203 : (₄₊ n) ⊢ S₀₁.⟪ ΛH₂′ ⟫ • °ΛH₂′ ≈ °ΛH₂′ • S₀₁.⟪ ΛH₂′ ⟫
  eq203 = begin
    S₀₁.⟪ ΛH₂′ ⟫ • °ΛH₂′
      ≈⟨ cong S₀₁-ΛH₂′-PP °ΛH₂′-PP ⟩
    (PP₁₃ • box₃‴ • PP₁₃) • (PP₀₃ • °box₃‴ • PP₀₃)
      ≈⟨ klein Γ PP₁₃² PP₀₃² PP₀₁² CA core ⟩
    (PP₀₃ • °box₃‴ • PP₀₃) • (PP₁₃ • box₃‴ • PP₁₃)
      ≈⟨ sym (cong °ΛH₂′-PP S₀₁-ΛH₂′-PP) ⟩
    °ΛH₂′ • S₀₁.⟪ ΛH₂′ ⟫ ∎

------------------------------------------------------------------------
-- (206), (207)

-- (206): H(1, 2; 0, 3) against H(2, 1; 0, °3).  The two gates lie between
-- the same P ⊗ P, on the wires 1 2, so the statement is one about their
-- boxes: (179), a box against a box of the other colour, under the cycle
-- 0 → 1 → 2 → 3 → 0.
private
  e179₃ : (₄₊ n) ⊢ box₃′ • N₃.⟪ box₃ ⟫ ≈ N₃.⟪ box₃ ⟫ • box₃′
  e179₃ = S₂₃.⟪⟫-≈ eq179 (S₂₃.⟪⟫-•₂ S₂₃-box₃′ S₂₃-°box₃) (S₂₃.⟪⟫-•₂ S₂₃-°box₃ S₂₃-box₃′)

  S₁₂-box₃³ : (₄₊ n) ⊢ S₁₂.⟪ N₃.⟪ box₃ ⟫ ⟫ ≈ N₃.⟪ box₃ ⟫
  S₁₂-box₃³ = S₁₂.⟪⟫-•₃ S₁₂-X₃ eq157 S₁₂-X₃

  e179ᶜ : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ box₃′ ⟫ ⟫ • N₃.⟪ box₃′ ⟫ ≈ N₃.⟪ box₃′ ⟫ • S₀₁.⟪ S₁₂.⟪ box₃′ ⟫ ⟫
  e179ᶜ {n} = S₀₁.⟪⟫-≈
    (S₁₂.⟪⟫-≈ e179₃ (S₁₂.⟪⟫-•₂ refl S₁₂-box₃³) (S₁₂.⟪⟫-•₂ S₁₂-box₃³ refl))
    (S₀₁.⟪⟫-•₂ refl (S₀₁-N₃ box₃)) (S₀₁.⟪⟫-•₂ (S₀₁-N₃ box₃) refl)
    where open Tools ((₄₊ n) VRel,_===_)

  N₃-PP₁₂ : (₄₊ n) ⊢ N₃.⟪ PP₁₂ ⟫ ≈ PP₁₂
  N₃-PP₁₂ {n} = N₃.⟪⟫-fix (sym (L₃-top (U₀ PP) X))
    where open Tools ((₄₊ n) VRel,_===_)

  G₆-PP : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ≈ PP₁₂ • S₀₁.⟪ S₁₂.⟪ box₃′ ⟫ ⟫ • PP₁₂
  G₆-PP {n} = trans (S₀₁.⟪⟫-cong (trans (S₁₂.⟪⟫-cong ΛH₀₁-PP) (S₁₂.⟪⟫-•₃ (O-L PP) refl (O-L PP))))
                    (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ (U PP)) refl (S₀₁.⟪⟫-⟪⟫ (U PP)))
    where open Tools ((₄₊ n) VRel,_===_)

  G₆′-PP : (₄₊ n) ⊢ N₃.⟪ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ≈ PP₁₂ • N₃.⟪ box₃′ ⟫ • PP₁₂
  G₆′-PP {n} = trans (N₃.⟪⟫-cong G-PP) (N₃.⟪⟫-•₃ N₃-PP₁₂ refl N₃-PP₁₂)
    where open Tools ((₄₊ n) VRel,_===_)

eq206 : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ • N₃.⟪ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫
               ≈ N₃.⟪ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ • S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫
eq206 {n} = begin
  S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ • N₃.⟪ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫
    ≈⟨ cong G₆-PP G₆′-PP ⟩
  (PP₁₂ • S₀₁.⟪ S₁₂.⟪ box₃′ ⟫ ⟫ • PP₁₂) • (PP₁₂ • N₃.⟪ box₃′ ⟫ • PP₁₂)
    ≈⟨ tr PP₁₂² e179ᶜ ⟩
  (PP₁₂ • N₃.⟪ box₃′ ⟫ • PP₁₂) • (PP₁₂ • S₀₁.⟪ S₁₂.⟪ box₃′ ⟫ ⟫ • PP₁₂)
    ≈⟨ sym (cong G₆′-PP G₆-PP) ⟩
  N₃.⟪ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ • S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- (207): X on the box wire passes the H gate.  Between P ⊗ P it is
-- Z H Z, which passes the box, (154) and (155).
eq207 : (₄₊ n) ⊢ X ↓ • (ΛH 2 ↓ᵏ n) ≈ (ΛH 2 ↓ᵏ n) • X ↓
eq207 {n} = Aj.⟪⟫-≈ zhz-box (Aj.⟪⟫-•₂ A-zhz refl) (Aj.⟪⟫-•₂ refl A-zhz)
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)
  module Aj = Conj {₄₊ n} PP₀₁ PP₀₁²
  zhz : Circuit (₄₊ n)
  zhz = Z ↓ • H ↓ • Z ↓
  A-zhz : (₄₊ n) ⊢ Aj.⟪ zhz ⟫ ≈ X ↓
  A-zhz = L-sem (PP • (Z ↓ • H ↓ • Z ↓) • PP) (X ↓) Eq.refl
  zhz-box : (₄₊ n) ⊢ zhz • box₃ ≈ box₃ • zhz
  zhz-box = sym (comm-• (sym eq154) (comm-• (sym eq155) (sym eq154)))
