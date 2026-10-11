------------------------------------------------------------------------
-- Presentations of groups
--
-- The doubly controlled H against a box of the other colour, continued
-- (Clément, Lemma D.5, Equations (191)–(200))
--
-- Writing H(h, t; …) for the doubly controlled H with its H on wire h
-- and its box wire on wire t, and Box(u; …) for the box with box wire u,
-- a ° marking a white control:
--
--   (190)   H(0, 3; 1, 2)      Box(0; 1, °2, 3)
--   (191)   Box(1; 0, 2, 3)    H(1, 3; 0, °2)
--   (192)   H(1, 3; 0, 2)      Box(1; 0, °2, 3)
--   (193)   Box(1; 0, 2, 3)    H(1, 2; 0, °3)
--   (194)   H(0, 1; 2, 3)      Box(0; 1, °2, 3)
--   (195)   H(0, 1; 2, 3)      Box(0; 1, °2, °3)
--   (196)   H(0, 1; 2, 3)      Box(1; 0, °2, 3)
--   (197)   H(0, 1; 2, 3)      Box(1; 0, °2, °3)
--   (198)   H(0, 2; 1, 3)      Box(2; 0, 1, °3)
--   (199)   H(2, 1; 0, 3)      Box(1; 0, 2, °3)
--   (200)   Box(2; 0, 1, 3)    H(1, 2; 0, °3)
--
-- (191)–(194) and (198)–(200) are (190) and (196) carried along a
-- permutation of the wires, with a colour exchanged.  A second white
-- control, (195) and (197), comes from (170): the box with two white
-- controls is the box with one and a CZ negated on the wire they share
-- with the H gate, which the H gate passes.  (196) moves the box wire
-- of the box off the H gate's box wire by (178); what is left is (175)
-- and (181).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Colours3
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
  using (eq157 ; eq161 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq170)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; eq175 ; eq178)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; °°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (tr ; N₂-box₃′ ; eq181ᵇ ; eq190 ; °CZ₂₀-ΛH₂′ ; CZ°₂₃-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; °CZ₂₀-O)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- (191)–(193)

-- (190) with the colours on wire 2 exchanged.
eq190ᵇ : (₄₊ n) ⊢ °ΛH₂′ • box₃ ≈ box₃ • °ΛH₂′
eq190ᵇ {n} = N₂.⟪⟫-≈ eq190
  (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ box₃))
  (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ box₃) refl)
  where open Tools ((₄₊ n) VRel,_===_)

-- (191)
eq191 : (₄₊ n) ⊢ box₃′ • S₀₁.⟪ °ΛH₂′ ⟫ ≈ S₀₁.⟪ °ΛH₂′ ⟫ • box₃′
eq191 {n} = sym (tr Ex² eq190ᵇ)
  where open Tools ((₄₊ n) VRel,_===_)

-- (192)
eq192 : (₄₊ n) ⊢ S₀₁.⟪ ΛH₂′ ⟫ • S₀₁.⟪ °box₃ ⟫ ≈ S₀₁.⟪ °box₃ ⟫ • S₀₁.⟪ ΛH₂′ ⟫
eq192 = tr Ex² eq190

-- The box on wire 1 is symmetric in its controls on wires 2 and 3.
S₂₃-box₃′ : (₄₊ n) ⊢ S₂₃.⟪ box₃′ ⟫ ≈ box₃′
S₂₃-box₃′ = S₂₃.⟪⟫-•₃ (L-S₂₃ Ex) eq161 (L-S₂₃ Ex)

-- (193)
eq193 : (₄₊ n) ⊢ box₃′ • S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ≈ S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ • box₃′
eq193 {n} = S₂₃.⟪⟫-≈ eq191
  (S₂₃.⟪⟫-•₂ S₂₃-box₃′ refl)
  (S₂₃.⟪⟫-•₂ refl S₂₃-box₃′)
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (194)

-- (190) under (1 3).
eq194 : (₄₊ n) ⊢ ΛH₀₁ • °box₃ ≈ °box₃ • ΛH₀₁
eq194 = T₁₃.⟪⟫-≈ eq190
  (T₁₃.⟪⟫-•₂ T₁₃-ΛH₂′ T₁₃-°box₃)
  (T₁₃.⟪⟫-•₂ T₁₃-°box₃ T₁₃-ΛH₂′)

------------------------------------------------------------------------
-- (195): a second white control

-- The upper swap moves the white control of the box from wire 2 to
-- wire 3.
S₂₃-°box₃ : (₄₊ n) ⊢ S₂₃.⟪ °box₃ ⟫ ≈ N₃.⟪ box₃ ⟫
S₂₃-°box₃ = S₂₃.⟪⟫-•₃ S₂₃-X₂ eq161 S₂₃-X₂

-- (170) for the control on wire 3 …
eq170₃ : (₄₊ n) ⊢ box₃ • N₃.⟪ box₃ ⟫ ≈ U CZ
eq170₃ = S₂₃.⟪⟫-≈ eq170 (S₂₃.⟪⟫-•₂ eq161 S₂₃-°box₃) (S₂₃-P₁₃ CZ)

-- … and with the control on wire 2 white.
eq170₂₃ : (₄₊ n) ⊢ °box₃ • °°box₃ ≈ U °CZ
eq170₂₃ {n} = N₂.⟪⟫-≈ eq170₃ (N₂.⟪⟫-•₂ refl (N₂-N₃ box₃)) refl
  where open Tools ((₄₊ n) VRel,_===_)

private
  °box₃² : (₄₊ n) ⊢ °box₃ • °box₃ ≈ ε
  °box₃² = N₂.⟪⟫-invol eq166

-- The box with two white controls from the box with one.
°°box₃-form : (₄₊ n) ⊢ °°box₃ ≈ °box₃ • U °CZ
°°box₃-form {n} = begin
  °°box₃                        ≈⟨ sym left-unit ⟩
  ε • °°box₃                    ≈⟨ front _ (sym °box₃²) ⟩
  (°box₃ • °box₃) • °°box₃      ≈⟨ assoc ⟩
  °box₃ • °box₃ • °°box₃        ≈⟨ back _ eq170₂₃ ⟩
  °box₃ • U °CZ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The H gate passes the CZ from wire 2 to its box wire, negated on
-- wire 2.
°CZ₂₁-ΛH₀₁ : (₄₊ n) ⊢ U °CZ • ΛH₀₁ ≈ ΛH₀₁ • U °CZ
°CZ₂₁-ΛH₀₁ {n} = T₁₃.⟪⟫-≈ CZ°₂₃-ΛH₂′
  (T₁₃.⟪⟫-•₂ w-map T₁₃-ΛH₂′)
  (T₁₃.⟪⟫-•₂ T₁₃-ΛH₂′ w-map)
  where
  open Tools ((₄₊ n) VRel,_===_)
  w-map : (₄₊ n) ⊢ T₁₃.⟪ P₂₃ CZ° ⟫ ≈ U °CZ
  w-map = trans (T₁₃-P₂₃ CZ°) (U-sem (Ex • CZ° • Ex) °CZ Eq.refl)

-- (195)
eq195 : (₄₊ n) ⊢ ΛH₀₁ • °°box₃ ≈ °°box₃ • ΛH₀₁
eq195 {n} = begin
  ΛH₀₁ • °°box₃              ≈⟨ back _ °°box₃-form ⟩
  ΛH₀₁ • (°box₃ • U °CZ)     ≈⟨ comm-• eq194 (sym °CZ₂₁-ΛH₀₁) ⟩
  (°box₃ • U °CZ) • ΛH₀₁     ≈⟨ front _ (sym °°box₃-form) ⟩
  °°box₃ • ΛH₀₁ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (196): the box and the H gate on the same box wire

private
  N₂-L : (u : Circuit 2) → (₄₊ n) ⊢ N₂.⟪ L u ⟫ ≈ L u
  N₂-L {n} u = N₂.⟪⟫-fix (sym (L-comm u X))
    where open Tools ((₄₊ n) VRel,_===_)

  -- (178), negated on wire 2.
  °eq178 : (₄₊ n) ⊢ °box₃ ≈ L (ΛZX 1) • S₀₁.⟪ °box₃ ⟫ • L (ΛXZ 1) • S₀₁.⟪ °box₃ ⟫
  °eq178 {n} = trans (N₂.⟪⟫-cong eq178)
    (N₂.⟪⟫-•₄ (N₂-L (ΛZX 1)) N₂-box₃′ (N₂-L (ΛXZ 1)) N₂-box₃′)
    where open Tools ((₄₊ n) VRel,_===_)

-- The same under the cycle 0 → 1 → 3 → 0: the box on wire 1 from the
-- box on wire 3, by a rotation of wire 1 controlled by wire 3.
box-13 : (₄₊ n) ⊢ S₀₁.⟪ °box₃ ⟫ ≈ P₁₃ (ΛZX 1) • T₀₃.⟪ °box₃ ⟫ • P₁₃ (ΛXZ 1) • T₀₃.⟪ °box₃ ⟫
box-13 {n} = begin
  S₀₁.⟪ °box₃ ⟫
    ≈⟨ S₀₁.⟪⟫-cong (sym T₁₃-°box₃) ⟩
  S₀₁.⟪ T₁₃.⟪ °box₃ ⟫ ⟫
    ≈⟨ S₀₁.⟪⟫-cong (T₁₃.⟪⟫-cong °eq178) ⟩
  S₀₁.⟪ T₁₃.⟪ L (ΛZX 1) • S₀₁.⟪ °box₃ ⟫ • L (ΛXZ 1) • S₀₁.⟪ °box₃ ⟫ ⟫ ⟫
    ≈⟨ S₀₁.⟪⟫-cong (T₁₃.⟪⟫-•₄ (T₁₃-L (ΛZX 1)) refl (T₁₃-L (ΛXZ 1)) refl) ⟩
  S₀₁.⟪ P₀₃ (ΛZX 1) • T₁₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ • P₀₃ (ΛXZ 1) • T₁₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫
    ≈⟨ S₀₁.⟪⟫-•₄ (S₀₁.⟪⟫-⟪⟫ (P₁₃ (ΛZX 1))) (sym (T₀₃-nest °box₃))
                 (S₀₁.⟪⟫-⟪⟫ (P₁₃ (ΛXZ 1))) (sym (T₀₃-nest °box₃)) ⟩
  P₁₃ (ΛZX 1) • T₀₃.⟪ °box₃ ⟫ • P₁₃ (ΛXZ 1) • T₀₃.⟪ °box₃ ⟫ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- (181), with the colours exchanged, under (1 3): the H gate against the
-- box on wire 3.  ((187), in this spelling of the box.)
eq187′ : (₄₊ n) ⊢ ΛH₀₁ • T₀₃.⟪ °box₃ ⟫ ≈ T₀₃.⟪ °box₃ ⟫ • ΛH₀₁
eq187′ {n} = sym (T₁₃.⟪⟫-≈ eq181ᵇ
  (T₁₃.⟪⟫-•₂ B-map T₁₃-ΛH₂′)
  (T₁₃.⟪⟫-•₂ T₁₃-ΛH₂′ B-map))
  where
  open Tools ((₄₊ n) VRel,_===_)
  B-map : (₄₊ n) ⊢ T₁₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ≈ T₀₃.⟪ °box₃ ⟫
  B-map = trans (T₁₃.⟪⟫-cong (S₀₁.⟪⟫-cong (sym T₁₃-°box₃))) (sym (T₀₃-nest′ °box₃))

private
  P₁₃-inv : (u v : Circuit 2) → (₃₊ n) ⊢ U (u • v) ≈ ε → (₄₊ n) ⊢ P₁₃ u • P₁₃ v ≈ ε
  P₁₃-inv {n} u v e = begin
    P₁₃ u • P₁₃ v     ≈⟨ sym (P₁₃-• u v) ⟩
    P₁₃ (u • v)       ≈⟨ S₁₂.⟪⟫-cong (lemma-cong↑ (U (u • v)) ε e) ⟩
    S₁₂.⟪ ε ⟫         ≈⟨ S₁₂.⟪⟫-ε ⟩
    ε ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- The rotation of wire 1 passes the H gate, (175); so does its inverse.
  ΛH₀₁-ZX : (₄₊ n) ⊢ ΛH₀₁ • P₁₃ (ΛZX 1) ≈ P₁₃ (ΛZX 1) • ΛH₀₁
  ΛH₀₁-ZX {n} = sym eq175
    where open Tools ((₄₊ n) VRel,_===_)

  ΛH₀₁-XZ : (₄₊ n) ⊢ ΛH₀₁ • P₁₃ (ΛXZ 1) ≈ P₁₃ (ΛXZ 1) • ΛH₀₁
  ΛH₀₁-XZ {n} = comm-inv (P₁₃-inv (ΛZX 1) (ΛXZ 1) (U-sem (ΛZX 1 • ΛXZ 1) ε Eq.refl))
                         (P₁₃-inv (ΛXZ 1) (ΛZX 1) (U-sem (ΛXZ 1 • ΛZX 1) ε Eq.refl)) ΛH₀₁-ZX
    where open Alg ((₄₊ n) VRel,_===_)

-- (196)
eq196 : (₄₊ n) ⊢ ΛH₀₁ • S₀₁.⟪ °box₃ ⟫ ≈ S₀₁.⟪ °box₃ ⟫ • ΛH₀₁
eq196 {n} = begin
  ΛH₀₁ • S₀₁.⟪ °box₃ ⟫
    ≈⟨ back _ box-13 ⟩
  ΛH₀₁ • (P₁₃ (ΛZX 1) • T₀₃.⟪ °box₃ ⟫ • P₁₃ (ΛXZ 1) • T₀₃.⟪ °box₃ ⟫)
    ≈⟨ comm-• ΛH₀₁-ZX (comm-• eq187′ (comm-• ΛH₀₁-XZ eq187′)) ⟩
  (P₁₃ (ΛZX 1) • T₀₃.⟪ °box₃ ⟫ • P₁₃ (ΛXZ 1) • T₀₃.⟪ °box₃ ⟫) • ΛH₀₁
    ≈⟨ front _ (sym box-13) ⟩
  S₀₁.⟪ °box₃ ⟫ • ΛH₀₁ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (197)

-- The H gate passes the CZ from wire 2 to its H wire, negated on wire 2.
°CZ₂₀-ΛH₀₁ : (₄₊ n) ⊢ O °CZ • ΛH₀₁ ≈ ΛH₀₁ • O °CZ
°CZ₂₀-ΛH₀₁ {n} = T₁₃.⟪⟫-≈ °CZ₂₀-ΛH₂′
  (T₁₃.⟪⟫-•₂ w-map T₁₃-ΛH₂′)
  (T₁₃.⟪⟫-•₂ T₁₃-ΛH₂′ w-map)
  where
  open Tools ((₄₊ n) VRel,_===_)
  w-map : (₄₊ n) ⊢ T₁₃.⟪ °CZ₂₀ ⟫ ≈ O °CZ
  w-map = trans (T₁₃.⟪⟫-cong °CZ₂₀-O) (T₁₃-O °CZ)

-- (197)
eq197 : (₄₊ n) ⊢ ΛH₀₁ • S₀₁.⟪ °°box₃ ⟫ ≈ S₀₁.⟪ °°box₃ ⟫ • ΛH₀₁
eq197 {n} = begin
  ΛH₀₁ • S₀₁.⟪ °°box₃ ⟫               ≈⟨ back _ form ⟩
  ΛH₀₁ • (S₀₁.⟪ °box₃ ⟫ • O °CZ)      ≈⟨ comm-• eq196 (sym °CZ₂₀-ΛH₀₁) ⟩
  (S₀₁.⟪ °box₃ ⟫ • O °CZ) • ΛH₀₁      ≈⟨ front _ (sym form) ⟩
  S₀₁.⟪ °°box₃ ⟫ • ΛH₀₁ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)
  form : (₄₊ n) ⊢ S₀₁.⟪ °°box₃ ⟫ ≈ S₀₁.⟪ °box₃ ⟫ • O °CZ
  form = trans (S₀₁.⟪⟫-cong °°box₃-form) (S₀₁.⟪⟫-• °box₃ (U °CZ))

------------------------------------------------------------------------
-- (198)–(200)

-- (196) under the upper swap: the white control on wire 3.
eq196ᵗ : (₄₊ n) ⊢ ΛH₀₁ • S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫ ≈ S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫ • ΛH₀₁
eq196ᵗ = S₂₃.⟪⟫-≈ eq196
  (S₂₃.⟪⟫-•₂ S₂₃-ΛH₀₁ B-map)
  (S₂₃.⟪⟫-•₂ B-map S₂₃-ΛH₀₁)
  where
  B-map : (₄₊ n) ⊢ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ≈ S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫
  B-map = S₂₃.⟪⟫-•₃ (L-S₂₃ Ex) S₂₃-°box₃ (L-S₂₃ Ex)

-- (198)
eq198 : (₄₊ n) ⊢ S₁₂.⟪ ΛH₀₁ ⟫ • S₁₂.⟪ S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫ ⟫
               ≈ S₁₂.⟪ S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫ ⟫ • S₁₂.⟪ ΛH₀₁ ⟫
eq198 = tr Ex₁² eq196ᵗ

-- (196ᵗ) under the lower swap: the H gate in its base position, the box
-- on wire 0.
eq196ᶜ : (₄₊ n) ⊢ (ΛH 2 ↓ᵏ n) • N₃.⟪ box₃ ⟫ ≈ N₃.⟪ box₃ ⟫ • (ΛH 2 ↓ᵏ n)
eq196ᶜ {n} = S₀₁.⟪⟫-≈ eq196ᵗ
  (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (ΛH 2 ↓ᵏ n)) (S₀₁.⟪⟫-⟪⟫ (N₃.⟪ box₃ ⟫)))
  (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (N₃.⟪ box₃ ⟫)) (S₀₁.⟪⟫-⟪⟫ (ΛH 2 ↓ᵏ n)))

private
  S₁₂-box₃³ : (₄₊ n) ⊢ S₁₂.⟪ N₃.⟪ box₃ ⟫ ⟫ ≈ N₃.⟪ box₃ ⟫
  S₁₂-box₃³ = S₁₂.⟪⟫-•₃ S₁₂-X₃ eq157 S₁₂-X₃

-- (199)
eq199 : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ • S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫
               ≈ S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫ • S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫
eq199 {n} = tr Ex² (S₁₂.⟪⟫-≈ eq196ᶜ
  (S₁₂.⟪⟫-•₂ refl S₁₂-box₃³)
  (S₁₂.⟪⟫-•₂ S₁₂-box₃³ refl))
  where open Tools ((₄₊ n) VRel,_===_)

-- (196ᶜ) with the colours on wire 3 exchanged.
eq196ᵈ : (₄₊ n) ⊢ box₃ • N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ≈ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ • box₃
eq196ᵈ {n} = sym (N₃.⟪⟫-≈ eq196ᶜ
  (N₃.⟪⟫-•₂ refl (N₃.⟪⟫-⟪⟫ box₃))
  (N₃.⟪⟫-•₂ (N₃.⟪⟫-⟪⟫ box₃) refl))
  where open Tools ((₄₊ n) VRel,_===_)

-- The box on wire 2: the exchange of wires 0 and 2 on the base box is
-- the middle swap on the box on wire 1.
τ₀₂-box₃ : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ box₃ ⟫ ⟫ ⟫ ≈ S₁₂.⟪ box₃′ ⟫
τ₀₂-box₃ {n} = trans (sym (braid-conj box₃)) (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong eq157))
  where open Tools ((₄₊ n) VRel,_===_)

-- (200)
eq200 : (₄₊ n) ⊢ S₁₂.⟪ box₃′ ⟫ • S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ⟫
               ≈ S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ⟫ • S₁₂.⟪ box₃′ ⟫
eq200 {n} = begin
  S₁₂.⟪ box₃′ ⟫ • Hx
    ≈⟨ front _ (sym τ₀₂-box₃) ⟩
  S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ box₃ ⟫ ⟫ ⟫ • Hx
    ≈⟨ tr Ex² (tr Ex₁² (tr Ex² eq196ᵈ)) ⟩
  Hx • S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ box₃ ⟫ ⟫ ⟫
    ≈⟨ back _ τ₀₂-box₃ ⟩
  Hx • S₁₂.⟪ box₃′ ⟫ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  Hx : Circuit (₄₊ n)
  Hx = S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ N₃.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫ ⟫
