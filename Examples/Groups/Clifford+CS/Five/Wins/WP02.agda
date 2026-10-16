------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP02 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0186 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0186 c4 = pw3 c4 (CS04⁻ ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0187 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0187 c4 = pw2 c4 (CS04⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0188 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0188 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0189 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0189 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0190 : Complete 4 → ⟪ (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wp0190 c4 = pw1 c4 (S0 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wp0191 : Complete 4 → ⟪ (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wp0191 c4 = pw2 c4 (S0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wp0192 : Complete 4 → ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) ⟫ʷ
wp0192 c4 = pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0193 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0193 c4 = pw2 c4 (CS04⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0194 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wp0194 c4 = pw3 c4 (CS01 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wp0195 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wp0195 c4 = pw2 c4 (CS01 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wp0196 : Complete 4 → ⟪ (CS01 ∷ X0 ∷ CS24 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wp0196 c4 = pw3 c4 (CS01 ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wp0197 : Complete 4 → ⟪ (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) ⟫ʷ
wp0197 c4 = pw2 c4 (K1 ∷ CS01 ∷ K1 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1 ∷ CS01 ∷ K1 ∷ []) tt tt Eq.refl

wp0198 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wp0198 c4 = pw1 c4 (S0⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wp0199 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wp0199 c4 = pw2 c4 (S0⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wp0200 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0200 c4 = pw1 c4 (CS03⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0201 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0201 c4 = pw2 c4 (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0202 : Complete 4 → ⟪ (Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ []) ⟫ʷ
wp0202 c4 = pw2 c4 (Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0203 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wp0203 c4 = pw1 c4 (CS03 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wp0204 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wp0204 c4 = pw2 c4 (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wp0205 : Complete 4 → ⟪ (CCZ134 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ134 ∷ []) ⟫ʷ
wp0205 c4 = pw2 c4 (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0206 : Complete 4 → ⟪ (CK41⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ S4 ∷ ι1⁻ ∷ []) ⟫ʷ
wp0206 c4 = pw0 c4 (CK41⁻ ∷ []) (CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ K1⁻ ∷ CS14⁻ ∷ S4 ∷ ι1⁻ ∷ []) tt tt Eq.refl

wp0207 : Complete 4 → ⟪ (S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0207 c4 = pw1 c4 (S4 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0208 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wp0208 c4 = pw3 c4 (CS01⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp0209 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wp0209 c4 = pw2 c4 (CS01⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp0210 : Complete 4 → ⟪ (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ []) ⟫ʷ
wp0210 c4 = pw3 c4 (CS01⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp0211 : Complete 4 → ⟪ (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wp0211 c4 = pw2 c4 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0212 : Complete 4 → ⟪ (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01⁻ ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) ⟫ʷ
wp0212 c4 = pw2 c4 (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) tt tt Eq.refl

wp0213 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wp0213 c4 = pw2 c4 (CS03 ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wp0214 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0214 c4 = pw2 c4 (CS03⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0215 : Complete 4 → ⟪ (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ []) ⟫ʷ
wp0215 c4 = pw1 c4 (CS02 ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02 ∷ []) tt tt Eq.refl

wp0216 : Complete 4 → ⟪ (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ []) ⟫ʷ
wp0216 c4 = pw3 c4 (CS02 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02 ∷ []) tt tt Eq.refl

wp0217 : Complete 4 → ⟪ (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ134 ∷ X0 ∷ CX30 ∷ []) ⟫ʷ
wp0217 c4 = pw2 c4 (CX30 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CX30 ∷ []) tt tt Eq.refl

wp0218 : Complete 4 → ⟪ (CS02⁻ ∷ X0 ∷ CS34 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0218 c4 = pw1 c4 (CS02⁻ ∷ X0 ∷ CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ X0 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0219 : Complete 4 → ⟪ (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX41 ∷ X0 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0219 c4 = pw3 c4 (CS02⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0220 : Complete 4 → ⟪ (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) ⟫ʷ
wp0220 c4 = pw1 c4 (K2 ∷ CX03 ∷ K2⁻ ∷ X0 ∷ CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ X0 ∷ K2 ∷ CX03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0221 : Complete 4 → ⟪ (K2 ∷ X0 ∷ CX41 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX41 ∷ X0 ∷ K2 ∷ []) ⟫ʷ
wp0221 c4 = pw3 c4 (K2 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2 ∷ []) tt tt Eq.refl

wp0222 : Complete 4 → ⟪ (CX03 ∷ X0 ∷ CX41 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX41 ∷ X0 ∷ CX03 ∷ []) ⟫ʷ
wp0222 c4 = pw2 c4 (CX03 ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ CX03 ∷ []) tt tt Eq.refl

wp0223 : Complete 4 → ⟪ (K2⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX41 ∷ X0 ∷ K2⁻ ∷ []) ⟫ʷ
wp0223 c4 = pw3 c4 (K2⁻ ∷ X0 ∷ CX41 ∷ X0 ∷ []) (X0 ∷ CX41 ∷ X0 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0224 : Complete 4 → ⟪ (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ
wp0224 c4 = pw3 c4 (K2 ∷ CS02 ∷ K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ []) (X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0225 : Complete 4 → ⟪ (CCZ124 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ124 ∷ []) ⟫ʷ
wp0225 c4 = pw3 c4 (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0226 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0226 c4 = pw1 c4 (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0227 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS12 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0227 c4 = pw3 c4 (CS04 ∷ X0 ∷ CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0228 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CX13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX13 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0228 c4 = pw2 c4 (CS04 ∷ X0 ∷ CX13 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0229 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23⁻ ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0229 c4 = pw1 c4 (CS04 ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0230 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0230 c4 = pw1 c4 (CS04 ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0231 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0231 c4 = pw1 c4 (CS04 ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0232 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0232 c4 = pw2 c4 (CS04 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0233 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03⁻ ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0233 c4 = pw1 c4 (CS04 ∷ X0 ∷ CS03⁻ ∷ X0 ∷ []) (X0 ∷ CS03⁻ ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0234 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0234 c4 = pw1 c4 (CS04 ∷ X0 ∷ CS03 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0235 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01⁻ ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0235 c4 = pw2 c4 (CS04 ∷ X0 ∷ CK01⁻ ∷ X0 ∷ []) (X0 ∷ CK01⁻ ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0236 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wp0236 c4 = pw1 c4 (S0⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wp0237 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0237 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0238 : Complete 4 → ⟪ (CCZ134 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CCZ134 ∷ []) ⟫ʷ
wp0238 c4 = pw2 c4 (CCZ134 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0239 : Complete 4 → ⟪ (Toff314 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ []) ⟫ʷ
wp0239 c4 = pw2 c4 (Toff314 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0240 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wp0240 c4 = pw1 c4 (CS03 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wp0241 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0241 c4 = pw1 c4 (CS03⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0242 : Complete 4 → ⟪ (CCZ134 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CCZ134 ∷ []) ⟫ʷ
wp0242 c4 = pw2 c4 (CCZ134 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0243 : Complete 4 → ⟪ (Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ []) ⟫ʷ
wp0243 c4 = pw2 c4 (Toff314 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0244 : Complete 4 → ⟪ (CK01 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wp0244 c4 = pw2 c4 (CK01 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wp0245 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) ⟫ʷ
wp0245 c4 = pw3 c4 (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ Toff214 ∷ X0 ∷ K2 ∷ []) tt tt Eq.refl

wp0246 : Complete 4 → ⟪ (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff304 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) ⟫ʷ
wp0246 c4 = pw1 c4 (K2 ∷ CS03 ∷ K2⁻ ∷ X0 ∷ Toff304 ∷ X0 ∷ []) (X0 ∷ Toff304 ∷ X0 ∷ K2 ∷ CS03 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0247 : Complete 4 → ⟪ (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0247 c4 = pw2 c4 (CS03⁻ ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0248 : Complete 4 → ⟪ (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) ⟫ʷ
wp0248 c4 = pw2 c4 (Toff314 ∷ CS03⁻ ∷ Toff314 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) tt tt Eq.refl

wp0249 : Complete 4 → ⟪ (Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ []) ⟫ʷ
wp0249 c4 = pw1 c4 (Toff204 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0250 : Complete 4 → ⟪ (Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ []) ⟫ʷ
wp0250 c4 = pw1 c4 (Toff204 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0251 : Complete 4 → ⟪ (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wp0251 c4 = pw2 c4 (K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ []) (X0 ∷ Toff314 ∷ X0 ∷ X0 ∷ CS03 ∷ X0 ∷ X0 ∷ Toff314 ∷ X0 ∷ K1⁻ ∷ CS01⁻ ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0252 : Complete 4 → ⟪ (CK01⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CK01⁻ ∷ []) ⟫ʷ
wp0252 c4 = pw2 c4 (CK01⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CK01⁻ ∷ []) tt tt Eq.refl

wp0253 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0253 c4 = pw2 c4 (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0254 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0254 c4 = pw1 c4 (CS04 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0255 : Complete 4 → ⟪ (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp0255 c4 = pw1 c4 (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0256 : Complete 4 → ⟪ (S0⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ S0⁻ ∷ []) ⟫ʷ
wp0256 c4 = pw1 c4 (S0⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ S0⁻ ∷ []) tt tt Eq.refl

wp0257 : Complete 4 → ⟪ (CS04⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0257 c4 = pw1 c4 (CS04⁻ ∷ CS04 ∷ []) [] tt tt Eq.refl

wp0258 : Complete 4 → ⟪ (CS03 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ134 ∷ X0 ∷ CS03 ∷ []) ⟫ʷ
wp0258 c4 = pw2 c4 (CS03 ∷ X0 ∷ CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ X0 ∷ CS03 ∷ []) tt tt Eq.refl

wp0259 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ []) ⟫ʷ
wp0259 c4 = pw3 c4 (CCZ124 ∷ []) (K2⁻ ∷ X0 ∷ K2 ∷ X0 ∷ X0 ∷ CCZ124 ∷ X0 ∷ X0 ∷ K2⁻ ∷ X0 ∷ K2 ∷ []) tt tt Eq.refl

wp0260 : Complete 4 → ⟪ (CS02 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) ⟫ʷ
wp0260 c4 = pw1 c4 (CS02 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) tt tt Eq.refl

wp0261 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0261 c4 = pw1 c4 (CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0262 : Complete 4 → ⟪ (CS03⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0262 c4 = pw1 c4 (CS03⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0263 : Complete 4 → ⟪ (CCZ024 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0263 c4 = pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0264 : Complete 4 → ⟪ (CS02⁻ ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0264 c4 = pw3 c4 (CS02⁻ ∷ Toff124 ∷ []) (Toff124 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0265 : Complete 4 → ⟪ (CCZ014 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp0265 c4 = pw3 c4 (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0266 : Complete 4 → ⟪ (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp0266 c4 = pw2 c4 (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp0267 : Complete 4 → ⟪ (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ []) ⟫ʷ
wp0267 c4 = pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl

wp0268 : Complete 4 → ⟪ (Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0268 c4 = pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl

wp0269 : Complete 4 → ⟪ (Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0269 c4 = pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl

wp0270 : Complete 4 → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp0270 c4 = pw2 c4 (Toff014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp0271 : Complete 4 → ⟪ (CCZ024 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0271 c4 = pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0272 : Complete 4 → ⟪ (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0272 c4 = pw3 c4 (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0273 : Complete 4 → ⟪ (CCZ124 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0273 c4 = pw3 c4 (CCZ124 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0274 : Complete 4 → ⟪ (CCZ124 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0274 c4 = pw3 c4 (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0275 : Complete 4 → ⟪ (Toff014 ∷ Toff104 ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ
wp0275 c4 = pw3 c4 (Toff014 ∷ Toff104 ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ []) (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0276 : Complete 4 → ⟪ (CCZ014 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ []) ⟫ʷ
wp0276 c4 = pw3 c4 (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0277 : Complete 4 → ⟪ (CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0277 c4 = pw3 c4 (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0278 : Complete 4 → ⟪ (CCZ124 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0278 c4 = pw3 c4 (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0279 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0279 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0280 : Complete 4 → ⟪ (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0280 c4 = pw3 c4 (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0281 : Complete 4 → ⟪ (CCZ024 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0281 c4 = pw3 c4 (CCZ024 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0282 : Complete 4 → ⟪ (CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0282 c4 = pw3 c4 (CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0283 : Complete 4 → ⟪ (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0283 c4 = pw3 c4 (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CZ24 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl

wp0284 : Complete 4 → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0284 c4 = pw1 c4 (Toff034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0285 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0285 c4 = pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0286 : Complete 4 → ⟪ (Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0286 c4 = pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl

wp0287 : Complete 4 → ⟪ (CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0287 c4 = pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0288 : Complete 4 → ⟪ (S0 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ S0 ∷ []) ⟫ʷ
wp0288 c4 = pw1 c4 (S0 ∷ Toff403 ∷ []) (Toff403 ∷ S0 ∷ []) tt tt Eq.refl

wp0289 : Complete 4 → ⟪ (CS01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CS01 ∷ []) ⟫ʷ
wp0289 c4 = pw2 c4 (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) tt tt Eq.refl

wp0290 : Complete 4 → ⟪ (CS01 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS01 ∷ []) ⟫ʷ
wp0290 c4 = pw3 c4 (CS01 ∷ CS24 ∷ []) (CS24 ∷ CS01 ∷ []) tt tt Eq.refl

wp0291 : Complete 4 → ⟪ (CS01 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CS01 ∷ []) ⟫ʷ
wp0291 c4 = pw3 c4 (CS01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01 ∷ []) tt tt Eq.refl

wp0292 : Complete 4 → ⟪ (CK01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CK01 ∷ []) ⟫ʷ
wp0292 c4 = pw2 c4 (CK01 ∷ Toff403 ∷ []) (Toff403 ∷ CK01 ∷ []) tt tt Eq.refl

wp0293 : Complete 4 → ⟪ (CK01 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK01 ∷ []) ⟫ʷ
wp0293 c4 = pw3 c4 (CK01 ∷ CS24 ∷ []) (CS24 ∷ CK01 ∷ []) tt tt Eq.refl

wp0294 : Complete 4 → ⟪ (CK01 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CK01 ∷ []) ⟫ʷ
wp0294 c4 = pw3 c4 (CK01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CK01 ∷ []) tt tt Eq.refl

wp0295 : Complete 4 → ⟪ (CK01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CK01 ∷ []) ⟫ʷ
wp0295 c4 = pw3 c4 (CK01 ∷ Toff204 ∷ []) (Toff204 ∷ CK01 ∷ []) tt tt Eq.refl

wp0296 : Complete 4 → ⟪ (CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0296 c4 = pw2 c4 (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0297 : Complete 4 → ⟪ (CCZ013 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0297 c4 = pw2 c4 (CCZ013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0298 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0298 c4 = pw1 c4 (CS03 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0299 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0299 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0300 : Complete 4 → ⟪ (CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0300 c4 = pw2 c4 (CCZ013 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0301 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wp0301 c4 = pw2 c4 (Toff314 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0302 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0302 c4 = pw1 c4 (CS03 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0303 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0303 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0304 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wp0304 c4 = pw1 c4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wp0305 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wp0305 c4 = pw2 c4 (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0306 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0306 c4 = pw2 c4 (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0307 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wp0307 c4 = pw2 c4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wp0308 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) ⟫ʷ
wp0308 c4 = pw3 c4 (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) tt tt Eq.refl

wp0309 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0309 c4 = pw3 c4 (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0310 : Complete 4 → ⟪ (CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0310 c4 = pw2 c4 (CCZ013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0311 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0311 c4 = pw2 c4 (CS03 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0312 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0312 c4 = pw2 c4 (CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0313 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0313 c4 = pw1 c4 (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0314 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0314 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0315 : Complete 4 → ⟪ (CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0315 c4 = pw2 c4 (CCZ013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0316 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS03 ∷ []) ⟫ʷ
wp0316 c4 = pw1 c4 (CS03 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0317 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0317 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0318 : Complete 4 → ⟪ (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff204 ∷ []) ⟫ʷ
wp0318 c4 = pw1 c4 (Toff204 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0319 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ []) ⟫ʷ
wp0319 c4 = pw2 c4 (Toff314 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0320 : Complete 4 → ⟪ (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0320 c4 = pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0321 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) ⟫ʷ
wp0321 c4 = pw1 c4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wp0322 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) ⟫ʷ
wp0322 c4 = pw2 c4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) tt tt Eq.refl

wp0323 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wp0323 c4 = pw2 c4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wp0324 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) ⟫ʷ
wp0324 c4 = pw2 c4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) tt tt Eq.refl
