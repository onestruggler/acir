------------------------------------------------------------------------
-- Presentations of groups
--
-- Two doubly controlled H gates of different colours (Clément, Lemma
-- D.5, Equations (201), (202))
--
-- A doubly controlled H is a box between two P ⊗ P on its H wire and its
-- box wire (Definition 2.4, (112)).  On three wires the three P ⊗ P form
-- a Klein four-group, (130): each is the product of the other two.  So
-- for H gates whose H wires and box wires lie in one triangle, commuting
-- is a statement about one box and one H gate — conjugate by the third
-- P ⊗ P (`klein`).  (202) is (191) in this way.  (201) is (171): two H
-- gates that differ in one colour merge into a controlled H.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.HGates
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq157 ; eq161 ; eq162)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq171 ; eq171′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (tr)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq191 ; τ₀₂-box₃)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; eq130)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The Klein four-group of three involutions

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ
  open Alg Γ

  private
    variable
      a b c p q : Word X

  -- If a c = b for involutions a, b, c, then any two of them multiply to
  -- the third, in either order.
  klein-ca : a • a ≈ ε → b • b ≈ ε → c • c ≈ ε → a • c ≈ b → c • a ≈ b
  klein-ca {a = a} {c = c} aa bb cc ac = inv-unique acca bb ac
    where
    acca : (a • c) • (c • a) ≈ ε
    acca = unwrap cc aa

  klein-ab : a • a ≈ ε → a • c ≈ b → a • b ≈ c
  klein-ab {a = a} {c = c} {b = b} aa ac = begin
    a • b         ≈⟨ back _ (sym ac) ⟩
    a • a • c     ≈⟨ sym assoc ⟩
    (a • a) • c   ≈⟨ trans (front _ aa) left-unit ⟩
    c ∎

  klein-ba : a • a ≈ ε → b • b ≈ ε → c • c ≈ ε → a • c ≈ b → b • a ≈ c
  klein-ba {a = a} {b = b} {c = c} aa bb cc ac = begin
    b • a         ≈⟨ front _ (sym (klein-ca aa bb cc ac)) ⟩
    (c • a) • a   ≈⟨ assoc ⟩
    c • a • a     ≈⟨ trans (back _ aa) right-unit ⟩
    c ∎

  -- A conjugate by a against a conjugate by b, from the one against the
  -- conjugate by c.
  klein : a • a ≈ ε → b • b ≈ ε → c • c ≈ ε → a • c ≈ b →
          p • (c • q • c) ≈ (c • q • c) • p →
          (a • p • a) • (b • q • b) ≈ (b • q • b) • (a • p • a)
  klein {a = a} {b = b} {c = c} {p = p} {q = q} aa bb cc ac h = begin
    (a • p • a) • (b • q • b)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    a • p • (a • b) • q • b
      ≈⟨ back _ (back _ (cong (klein-ab aa ac) (back _ (sym (klein-ca aa bb cc ac))))) ⟩
    a • p • c • q • (c • a)
      ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □)) (□ • (□ • (□ • □ • □)) • □) Eq.refl ⟩
    a • (p • (c • q • c)) • a
      ≈⟨ mid _ _ h ⟩
    a • ((c • q • c) • p) • a
      ≈⟨ by-passoc (□ • ((□ • □ • □) • □) • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (a • c) • q • c • p • a
      ≈⟨ cong ac (back _ (front _ (sym (klein-ba aa bb cc ac)))) ⟩
    b • q • (b • a) • p • a
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
    (b • q • b) • (a • p • a) ∎

------------------------------------------------------------------------
-- P ⊗ P on the pairs 0 1, 0 3 and 1 3

PP₀₁ PP₀₃ PP₁₃ : Circuit (₄₊ n)
PP₀₁ = PP ↓
PP₀₃ = P₀₃ PP
PP₁₃ = P₁₃ PP

PP₀₁² : (₄₊ n) ⊢ PP₀₁ • PP₀₁ ≈ ε
PP₀₁² = L-sem (PP • PP) ε Eq.refl

PP₁₃² : (₄₊ n) ⊢ PP₁₃ • PP₁₃ ≈ ε
PP₁₃² {n} = conj-invol Ex₁² (lemma-cong↑ (U (PP • PP)) ε (U-sem (PP • PP) ε Eq.refl))
  where open Tools ((₄₊ n) VRel,_===_)

PP₀₃² : (₄₊ n) ⊢ PP₀₃ • PP₀₃ ≈ ε
PP₀₃² {n} = conj-invol Ex² PP₁₃²
  where open Tools ((₄₊ n) VRel,_===_)

-- (130), with wire 3 for wire 2.
PP-triangle : (₄₊ n) ⊢ PP₀₁ • PP₁₃ ≈ PP₀₃
PP-triangle {n} = S₂₃.⟪⟫-≈ eq130
  (S₂₃.⟪⟫-•₂ (L-S₂₃ PP) (U-S₂₃ PP))
  (trans (S₂₃.⟪⟫-cong (O-L PP)) (O-S₂₃ PP))
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- The H gates as boxes between P ⊗ P

-- The box with its box wire on wire 3.
box₃‴ : Circuit (₄₊ n)
box₃‴ = S₂₃.⟪ S₁₂.⟪ box₃′ ⟫ ⟫

°box₃‴ : Circuit (₄₊ n)
°box₃‴ = N₂.⟪ box₃‴ ⟫

private
  S₀₁-PP : (₄₊ n) ⊢ S₀₁.⟪ PP ↓ ⟫ ≈ PP ↓
  S₀₁-PP = L-sem (Ex • PP • Ex) PP Eq.refl

ΛH₀₁-PP : (₄₊ n) ⊢ ΛH₀₁ ≈ PP₀₁ • box₃′ • PP₀₁
ΛH₀₁-PP {n} = S₀₁.⟪⟫-•₃ S₀₁-PP refl S₀₁-PP
  where open Tools ((₄₊ n) VRel,_===_)

ΛH₂′-PP : (₄₊ n) ⊢ ΛH₂′ ≈ PP₀₃ • box₃‴ • PP₀₃
ΛH₂′-PP {n} = begin
  S₂₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫
    ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong ΛH₀₁-PP) ⟩
  S₂₃.⟪ S₁₂.⟪ PP₀₁ • box₃′ • PP₀₁ ⟫ ⟫
    ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-•₃ (O-L PP) refl (O-L PP)) ⟩
  S₂₃.⟪ O PP • S₁₂.⟪ box₃′ ⟫ • O PP ⟫
    ≈⟨ S₂₃.⟪⟫-•₃ (O-S₂₃ PP) refl (O-S₂₃ PP) ⟩
  PP₀₃ • box₃‴ • PP₀₃ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- X on wire 2 leaves them alone.
N₂-PP₀₃ : (₄₊ n) ⊢ N₂.⟪ PP₀₃ ⟫ ≈ PP₀₃
N₂-PP₀₃ {n} = N₂.⟪⟫-fix (sym (P₀₃-U PP (X ↑)))
  where open Tools ((₄₊ n) VRel,_===_)

N₂-PP₀₁ : (₄₊ n) ⊢ N₂.⟪ PP₀₁ ⟫ ≈ PP₀₁
N₂-PP₀₁ {n} = N₂.⟪⟫-fix (sym (L-comm PP X))
  where open Tools ((₄₊ n) VRel,_===_)

°ΛH₂′-PP : (₄₊ n) ⊢ °ΛH₂′ ≈ PP₀₃ • °box₃‴ • PP₀₃
°ΛH₂′-PP {n} = trans (N₂.⟪⟫-cong ΛH₂′-PP) (N₂.⟪⟫-•₃ N₂-PP₀₃ refl N₂-PP₀₃)
  where open Tools ((₄₊ n) VRel,_===_)

-- The box on wire 3 is symmetric in its controls on wires 0 and 1.
S₀₁-box₃‴ : (₄₊ n) ⊢ S₀₁.⟪ box₃‴ ⟫ ≈ box₃‴
S₀₁-box₃‴ = S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ Ex) τ₀₂-box₃ (P₂₃-S₀₁ Ex)

S₀₁-°box₃‴ : (₄₊ n) ⊢ S₀₁.⟪ °box₃‴ ⟫ ≈ °box₃‴
S₀₁-°box₃‴ = S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) S₀₁-box₃‴ (P₂₃-S₀₁ X)

-- Under the lower swap the H gate has its H on wire 1.
S₀₁-°ΛH₂′-PP : (₄₊ n) ⊢ S₀₁.⟪ °ΛH₂′ ⟫ ≈ PP₁₃ • °box₃‴ • PP₁₃
S₀₁-°ΛH₂′-PP {n} = trans (S₀₁.⟪⟫-cong °ΛH₂′-PP)
  (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ PP₁₃) S₀₁-°box₃‴ (S₀₁.⟪⟫-⟪⟫ PP₁₃))
  where open Tools ((₄₊ n) VRel,_===_)

S₀₁-ΛH₂′-PP : (₄₊ n) ⊢ S₀₁.⟪ ΛH₂′ ⟫ ≈ PP₁₃ • box₃‴ • PP₁₃
S₀₁-ΛH₂′-PP {n} = trans (S₀₁.⟪⟫-cong ΛH₂′-PP)
  (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ PP₁₃) S₀₁-box₃‴ (S₀₁.⟪⟫-⟪⟫ PP₁₃))
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (201)

-- A white control on wire 3 under the swaps.
S₀₁-N₃ : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ S₀₁.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₃.⟪ S₀₁.⟪ w ⟫ ⟫
S₀₁-N₃ {n} w = S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ (X ↑)) refl (P₂₃-S₀₁ (X ↑))
  where open Tools ((₄₊ n) VRel,_===_)

S₁₂-N₃ : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ S₁₂.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₃.⟪ S₁₂.⟪ w ⟫ ⟫
S₁₂-N₃ {n} w = S₁₂.⟪⟫-•₃ S₁₂-X₃ refl S₁₂-X₃
  where open Tools ((₄₊ n) VRel,_===_)

S₂₃-N₃ : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ S₂₃.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₂.⟪ S₂₃.⟪ w ⟫ ⟫
S₂₃-N₃ {n} w = S₂₃.⟪⟫-•₃ S₂₃-X₃ refl S₂₃-X₃
  where open Tools ((₄₊ n) VRel,_===_)

private
  -- The cycle that takes the base H gate to the one with its box wire on
  -- wire 3 takes a white control on wire 3 to wire 2.
  cycle-N₃ : (w : Circuit (₄₊ n)) →
             (₄₊ n) ⊢ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ w ⟫ ⟫ ⟫ ⟫ ≈ N₂.⟪ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ w ⟫ ⟫ ⟫ ⟫
  cycle-N₃ {n} w = trans (S₂₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (S₀₁-N₃ w)) (S₁₂-N₃ (S₀₁.⟪ w ⟫))))
                         (S₂₃-N₃ (S₁₂.⟪ S₀₁.⟪ w ⟫ ⟫))
    where open Tools ((₄₊ n) VRel,_===_)

  S₂₃-°ΛH : (₄₊ n) ⊢ S₂₃.⟪ N₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ≈ N₃.⟪ ΛH 2 ↓ᵏ n ⟫
  S₂₃-°ΛH = S₂₃.⟪⟫-•₃ S₂₃-X₂ eq162 S₂₃-X₂

  -- (171) with the white control on wire 3.
  eq171₃ : (₄₊ n) ⊢ (ΛH 2 ↓ᵏ n) • N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ≈ U CH
  eq171₃ = S₂₃.⟪⟫-≈ eq171 (S₂₃.⟪⟫-•₂ eq162 S₂₃-°ΛH) (S₂₃-P₁₃ CH)

  eq171₃′ : (₄₊ n) ⊢ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ • (ΛH 2 ↓ᵏ n) ≈ U CH
  eq171₃′ = S₂₃.⟪⟫-≈ eq171′ (S₂₃.⟪⟫-•₂ S₂₃-°ΛH eq162) (S₂₃-P₁₃ CH)

  -- The cycle on the controlled H of wires 1 and 2.
  cycle-UCH : (₄₊ n) ⊢ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ U CH ⟫ ⟫ ⟫ ≈ CH ↓
  cycle-UCH {n} = trans (S₂₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (sym (O-L CH))) (S₁₂.⟪⟫-⟪⟫ (L CH))))
                        (L-S₂₃ CH)
    where open Tools ((₄₊ n) VRel,_===_)

  cycle-• : (u v : Circuit (₄₊ n)) →
            (₄₊ n) ⊢ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ u • v ⟫ ⟫ ⟫
                   ≈ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ u ⟫ ⟫ ⟫ • S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ v ⟫ ⟫ ⟫
  cycle-• {n} u v = trans (S₂₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-• u v)) (S₁₂.⟪⟫-• _ _)))
                          (S₂₃.⟪⟫-• _ _)
    where open Tools ((₄₊ n) VRel,_===_)

-- (171) for the H gate with its box wire on wire 3: the two colours on
-- wire 2 merge into the controlled H below.
eq171ᶜ : (₄₊ n) ⊢ ΛH₂′ • °ΛH₂′ ≈ CH ↓
eq171ᶜ {n} = begin
  ΛH₂′ • °ΛH₂′
    ≈⟨ back _ (sym (cycle-N₃ (ΛH 2 ↓ᵏ n))) ⟩
  ΛH₂′ • S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ⟫
    ≈⟨ sym (cycle-• (ΛH 2 ↓ᵏ n) (N₃.⟪ ΛH 2 ↓ᵏ n ⟫)) ⟩
  S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ (ΛH 2 ↓ᵏ n) • N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ⟫
    ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong eq171₃)) ⟩
  S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ U CH ⟫ ⟫ ⟫
    ≈⟨ cycle-UCH ⟩
  CH ↓ ∎
  where open Tools ((₄₊ n) VRel,_===_)

eq171ᶜ′ : (₄₊ n) ⊢ °ΛH₂′ • ΛH₂′ ≈ CH ↓
eq171ᶜ′ {n} = begin
  °ΛH₂′ • ΛH₂′
    ≈⟨ front _ (sym (cycle-N₃ (ΛH 2 ↓ᵏ n))) ⟩
  S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ⟫ • ΛH₂′
    ≈⟨ sym (cycle-• (N₃.⟪ ΛH 2 ↓ᵏ n ⟫) (ΛH 2 ↓ᵏ n)) ⟩
  S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ • (ΛH 2 ↓ᵏ n) ⟫ ⟫ ⟫
    ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong eq171₃′)) ⟩
  S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ U CH ⟫ ⟫ ⟫
    ≈⟨ cycle-UCH ⟩
  CH ↓ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The two colours commute.
ΛH₂′-°ΛH₂′ : (₄₊ n) ⊢ ΛH₂′ • °ΛH₂′ ≈ °ΛH₂′ • ΛH₂′
ΛH₂′-°ΛH₂′ {n} = trans eq171ᶜ (sym eq171ᶜ′)
  where open Tools ((₄₊ n) VRel,_===_)

-- (201): H(1, 3; 0, 2) against H(1, 3; 0, °2).
eq201 : (₄₊ n) ⊢ S₀₁.⟪ ΛH₂′ ⟫ • S₀₁.⟪ °ΛH₂′ ⟫ ≈ S₀₁.⟪ °ΛH₂′ ⟫ • S₀₁.⟪ ΛH₂′ ⟫
eq201 = tr Ex² ΛH₂′-°ΛH₂′

------------------------------------------------------------------------
-- (202)

-- H(0, 1; 2, 3) against H(0, 3; 1, °2): by the Klein four-group, (191).
eq202 : (₄₊ n) ⊢ ΛH₀₁ • °ΛH₂′ ≈ °ΛH₂′ • ΛH₀₁
eq202 {n} = begin
  ΛH₀₁ • °ΛH₂′
    ≈⟨ cong ΛH₀₁-PP °ΛH₂′-PP ⟩
  (PP₀₁ • box₃′ • PP₀₁) • (PP₀₃ • °box₃‴ • PP₀₃)
    ≈⟨ klein ((₄₊ n) VRel,_===_) PP₀₁² PP₀₃² PP₁₃² PP-triangle e191 ⟩
  (PP₀₃ • °box₃‴ • PP₀₃) • (PP₀₁ • box₃′ • PP₀₁)
    ≈⟨ sym (cong °ΛH₂′-PP ΛH₀₁-PP) ⟩
  °ΛH₂′ • ΛH₀₁ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  e191 : (₄₊ n) ⊢ box₃′ • (PP₁₃ • °box₃‴ • PP₁₃) ≈ (PP₁₃ • °box₃‴ • PP₁₃) • box₃′
  e191 = trans (back _ (sym S₀₁-°ΛH₂′-PP)) (trans eq191 (front _ S₀₁-°ΛH₂′-PP))
