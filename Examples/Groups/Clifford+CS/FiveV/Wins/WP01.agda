------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WP01 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0001 : Complete 4 → ⟪ (CCZ034 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0001 c4 = pw2 c4 (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0002 : Complete 4 → ⟪ (CCZ034 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0002 c4 = pw1 c4 (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0003 : Complete 4 → ⟪ (CCZ034 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0003 c4 = pw1 c4 (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0004 : Complete 4 → ⟪ (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0004 c4 = pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0005 : Complete 4 → ⟪ (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0005 c4 = pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0006 : Complete 4 → ⟪ (Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0006 c4 = pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl

wp0007 : Complete 4 → ⟪ (CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0007 c4 = pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl

wp0008 : Complete 4 → ⟪ (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0008 c4 = pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0009 : Complete 4 → ⟪ (CZ01 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) ⟫ʷ
wp0009 c4 = pw2 c4 (CZ01 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0010 : Complete 4 → ⟪ (Toff034 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff034 ∷ []) ⟫ʷ
wp0010 c4 = pw1 c4 (Toff034 ∷ X2 ∷ []) (X2 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0011 : Complete 4 → ⟪ (CCZ012 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0011 c4 = pw3 c4 (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0012 : Complete 4 → ⟪ (CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0012 c4 = pw2 c4 (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0013 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) ⟫ʷ
wp0013 c4 = pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl

wp0014 : Complete 4 → ⟪ (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp0014 c4 = pw1 c4 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp0015 : Complete 4 → ⟪ (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
wp0015 c4 = pw1 c4 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0016 : Complete 4 → ⟪ (CS04⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS04⁻ ∷ []) ⟫ʷ
wp0016 c4 = pw2 c4 (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0017 : Complete 4 → ⟪ (CS04⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0017 c4 = pw1 c4 (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0018 : Complete 4 → ⟪ (CS04⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS04⁻ ∷ []) ⟫ʷ
wp0018 c4 = pw1 c4 (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0019 : Complete 4 → ⟪ (Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0019 c4 = pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl

wp0020 : Complete 4 → ⟪ (CCZ024 ∷ X4 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0020 c4 = pw3 c4 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0021 : Complete 4 → ⟪ (CCZ024 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ024 ∷ []) ⟫ʷ
wp0021 c4 = pw1 c4 (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0022 : Complete 4 → ⟪ (CCZ024 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ024 ∷ []) ⟫ʷ
wp0022 c4 = pw3 c4 (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0023 : Complete 4 → ⟪ (CCZ024 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ024 ∷ []) ⟫ʷ
wp0023 c4 = pw3 c4 (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0024 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ
wp0024 c4 = pw2 c4 (CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl

wp0025 : Complete 4 → ⟪ (CCZ024 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) ⟫ʷ
wp0025 c4 = pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0026 : Complete 4 → ⟪ (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp0026 c4 = pw1 c4 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp0027 : Complete 4 → ⟪ (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
wp0027 c4 = pw1 c4 (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0028 : Complete 4 → ⟪ (CCZ024 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0028 c4 = pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0029 : Complete 4 → ⟪ (CS01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ []) ⟫ʷ
wp0029 c4 = pw2 c4 (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ []) tt tt Eq.refl

wp0030 : Complete 4 → ⟪ (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ013 ∷ []) ⟫ʷ
wp0030 c4 = pw2 c4 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0031 : Complete 4 → ⟪ (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0031 c4 = pw2 c4 (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0032 : Complete 4 → ⟪ (CCZ024 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0032 c4 = pw1 c4 (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0033 : Complete 4 → ⟪ (CCZ024 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0033 c4 = pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0034 : Complete 4 → ⟪ (CCZ024 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ024 ∷ []) ⟫ʷ
wp0034 c4 = pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0035 : Complete 4 → ⟪ (CCZ024 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0035 c4 = pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0036 : Complete 4 → ⟪ (CCZ024 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ024 ∷ []) ⟫ʷ
wp0036 c4 = pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0037 : Complete 4 → ⟪ (CCZ024 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ024 ∷ []) ⟫ʷ
wp0037 c4 = pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0038 : Complete 4 → ⟪ (CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0038 c4 = pw3 c4 (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0039 : Complete 4 → ⟪ (CCZ024 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ024 ∷ []) ⟫ʷ
wp0039 c4 = pw3 c4 (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0040 : Complete 4 → ⟪ (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0040 c4 = pw2 c4 (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0041 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) ⟫ʷ
wp0041 c4 = pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl

wp0042 : Complete 4 → ⟪ (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ024 ∷ []) ⟫ʷ
wp0042 c4 = pw3 c4 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0043 : Complete 4 → ⟪ (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ CS03 ∷ []) ⟫ʷ
wp0043 c4 = pw2 c4 (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ []) tt tt Eq.refl

wp0044 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) ⟫ʷ
wp0044 c4 = pw3 c4 (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) tt tt Eq.refl

wp0045 : Complete 4 → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0045 c4 = pw2 c4 (CS01 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0046 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) ⟫ʷ
wp0046 c4 = pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) tt tt Eq.refl

wp0047 : Complete 4 → ⟪ (CCZ023 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wp0047 c4 = pw1 c4 (CCZ023 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0048 : Complete 4 → ⟪ (CCZ023 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ023 ∷ []) ⟫ʷ
wp0048 c4 = pw1 c4 (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0049 : Complete 4 → ⟪ (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp0049 c4 = pw2 c4 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp0050 : Complete 4 → ⟪ (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0050 c4 = pw2 c4 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0051 : Complete 4 → ⟪ (Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0051 c4 = pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl

wp0052 : Complete 4 → ⟪ (CCZ014 ∷ X4 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0052 c4 = pw2 c4 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0053 : Complete 4 → ⟪ (CCZ014 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ014 ∷ []) ⟫ʷ
wp0053 c4 = pw2 c4 (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0054 : Complete 4 → ⟪ (CCZ014 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ014 ∷ []) ⟫ʷ
wp0054 c4 = pw3 c4 (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0055 : Complete 4 → ⟪ (CCZ014 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ014 ∷ []) ⟫ʷ
wp0055 c4 = pw2 c4 (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0056 : Complete 4 → ⟪ (CCZ014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) ⟫ʷ
wp0056 c4 = pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0057 : Complete 4 → ⟪ (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp0057 c4 = pw2 c4 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp0058 : Complete 4 → ⟪ (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0058 c4 = pw2 c4 (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0059 : Complete 4 → ⟪ (CCZ014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0059 c4 = pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0060 : Complete 4 → ⟪ (CCZ014 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0060 c4 = pw2 c4 (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0061 : Complete 4 → ⟪ (CCZ014 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0061 c4 = pw2 c4 (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0062 : Complete 4 → ⟪ (CCZ014 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ014 ∷ []) ⟫ʷ
wp0062 c4 = pw3 c4 (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0063 : Complete 4 → ⟪ (CCZ014 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0063 c4 = pw2 c4 (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0064 : Complete 4 → ⟪ (CCZ014 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ014 ∷ []) ⟫ʷ
wp0064 c4 = pw2 c4 (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0065 : Complete 4 → ⟪ (CCZ014 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ014 ∷ []) ⟫ʷ
wp0065 c4 = pw2 c4 (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0066 : Complete 4 → ⟪ (CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp0066 c4 = pw3 c4 (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0067 : Complete 4 → ⟪ (CCZ014 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ014 ∷ []) ⟫ʷ
wp0067 c4 = pw3 c4 (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0068 : Complete 4 → ⟪ (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff023 ∷ []) ⟫ʷ
wp0068 c4 = pw1 c4 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0069 : Complete 4 → ⟪ (CS24⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0069 c4 = pw1 c4 (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0070 : Complete 4 → ⟪ (CS24 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS24 ∷ []) ⟫ʷ
wp0070 c4 = pw1 c4 (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl

wp0071 : Complete 4 → ⟪ (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0071 c4 = pw3 c4 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0072 : Complete 4 → ⟪ (Toff023 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff023 ∷ []) ⟫ʷ
wp0072 c4 = pw1 c4 (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0073 : Complete 4 → ⟪ (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wp0073 c4 = pw1 c4 (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wp0074 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) ⟫ʷ
wp0074 c4 = pw3 c4 (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0075 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) ⟫ʷ
wp0075 c4 = pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl

wp0076 : Complete 4 → ⟪ (CCZ013 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wp0076 c4 = pw2 c4 (CCZ013 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0077 : Complete 4 → ⟪ (CCZ013 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ013 ∷ []) ⟫ʷ
wp0077 c4 = pw2 c4 (CCZ013 ∷ CS04 ∷ []) (CS04 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0078 : Complete 4 → ⟪ (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp0078 c4 = pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp0079 : Complete 4 → ⟪ (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0079 c4 = pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0080 : Complete 4 → ⟪ (Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0080 c4 = pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl

wp0081 : Complete 4 → ⟪ (CCZ024 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ024 ∷ []) ⟫ʷ
wp0081 c4 = pw3 c4 (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0082 : Complete 4 → ⟪ (CCZ024 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ024 ∷ []) ⟫ʷ
wp0082 c4 = pw1 c4 (CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0083 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) ⟫ʷ
wp0083 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0084 : Complete 4 → ⟪ (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp0084 c4 = pw1 c4 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp0085 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0085 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0086 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0086 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0087 : Complete 4 → ⟪ (CCZ024 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0087 c4 = pw3 c4 (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0088 : Complete 4 → ⟪ (CCZ024 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0088 c4 = pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0089 : Complete 4 → ⟪ (CCZ024 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ024 ∷ []) ⟫ʷ
wp0089 c4 = pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0090 : Complete 4 → ⟪ (CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0090 c4 = pw1 c4 (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0091 : Complete 4 → ⟪ (CCZ024 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0091 c4 = pw1 c4 (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0092 : Complete 4 → ⟪ (CCZ024 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ024 ∷ []) ⟫ʷ
wp0092 c4 = pw1 c4 (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0093 : Complete 4 → ⟪ (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff013 ∷ []) ⟫ʷ
wp0093 c4 = pw2 c4 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0094 : Complete 4 → ⟪ (CS34⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0094 c4 = pw2 c4 (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0095 : Complete 4 → ⟪ (CS34 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS34 ∷ []) ⟫ʷ
wp0095 c4 = pw2 c4 (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl

wp0096 : Complete 4 → ⟪ (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0096 c4 = pw1 c4 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0097 : Complete 4 → ⟪ (Toff013 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff013 ∷ []) ⟫ʷ
wp0097 c4 = pw2 c4 (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0098 : Complete 4 → ⟪ (CS23 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ
wp0098 c4 = pw1 c4 (CS23 ∷ CCZ234 ∷ []) (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0099 : Complete 4 → ⟪ (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wp0099 c4 = pw2 c4 (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wp0100 : Complete 4 → ⟪ (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ034 ∷ []) ⟫ʷ
wp0100 c4 = pw2 c4 (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0101 : Complete 4 → ⟪ (CCZ034 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ034 ∷ []) ⟫ʷ
wp0101 c4 = pw1 c4 (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0102 : Complete 4 → ⟪ (CS14 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS14 ∷ []) ⟫ʷ
wp0102 c4 = pw3 c4 (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) tt tt Eq.refl

wp0103 : Complete 4 → ⟪ (CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0103 c4 = pw2 c4 (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0104 : Complete 4 → ⟪ (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0104 c4 = pw1 c4 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0105 : Complete 4 → ⟪ (CCZ024 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0105 c4 = pw3 c4 (CCZ024 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0106 : Complete 4 → ⟪ (CCZ034 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0106 c4 = pw2 c4 (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0107 : Complete 4 → ⟪ (CCZ034 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0107 c4 = pw1 c4 (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0108 : Complete 4 → ⟪ (CCZ034 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ034 ∷ []) ⟫ʷ
wp0108 c4 = pw1 c4 (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0109 : Complete 4 → ⟪ (CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0109 c4 = pw1 c4 (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0110 : Complete 4 → ⟪ (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wp0110 c4 = pw1 c4 (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wp0111 : Complete 4 → ⟪ (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0111 c4 = pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0112 : Complete 4 → ⟪ (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0112 c4 = pw1 c4 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0113 : Complete 4 → ⟪ (CCZ034 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) ⟫ʷ
wp0113 c4 = pw1 c4 (CCZ034 ∷ CZ34 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0114 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) ⟫ʷ
wp0114 c4 = pw1 c4 (CCZ034 ∷ []) (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0115 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) ⟫ʷ
wp0115 c4 = pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl

wp0116 : Complete 4 → ⟪ (CCZ012 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0116 c4 = pw3 c4 (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0117 : Complete 4 → ⟪ (CCZ012 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ012 ∷ []) ⟫ʷ
wp0117 c4 = pw3 c4 (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0118 : Complete 4 → ⟪ (CCZ034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) ⟫ʷ
wp0118 c4 = pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0119 : Complete 4 → ⟪ (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0119 c4 = pw1 c4 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0120 : Complete 4 → ⟪ (CCZ034 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0120 c4 = pw2 c4 (CCZ034 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0121 : Complete 4 → ⟪ (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ034 ∷ []) ⟫ʷ
wp0121 c4 = pw2 c4 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (CX13 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0122 : Complete 4 → ⟪ (CCZ014 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0122 c4 = pw3 c4 (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0123 : Complete 4 → ⟪ (CCZ034 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0123 c4 = pw2 c4 (CCZ034 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0124 : Complete 4 → ⟪ (CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ
wp0124 c4 = pw2 c4 (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0125 : Complete 4 → ⟪ (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wp0125 c4 = pw2 c4 (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wp0126 : Complete 4 → ⟪ (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ034 ∷ []) ⟫ʷ
wp0126 c4 = pw1 c4 (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0127 : Complete 4 → ⟪ (CCZ034 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ034 ∷ []) ⟫ʷ
wp0127 c4 = pw2 c4 (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0128 : Complete 4 → ⟪ (CS24 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS24 ∷ []) ⟫ʷ
wp0128 c4 = pw3 c4 (CS24 ∷ Toff012 ∷ []) (Toff012 ∷ CS24 ∷ []) tt tt Eq.refl

wp0129 : Complete 4 → ⟪ (CCZ034 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ034 ∷ []) ⟫ʷ
wp0129 c4 = pw1 c4 (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0130 : Complete 4 → ⟪ (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0130 c4 = pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0131 : Complete 4 → ⟪ (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0131 c4 = pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0132 : Complete 4 → ⟪ (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0132 c4 = pw1 c4 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0133 : Complete 4 → ⟪ (CCZ024 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) ⟫ʷ
wp0133 c4 = pw1 c4 (CCZ024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0134 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) ⟫ʷ
wp0134 c4 = pw1 c4 (CCZ024 ∷ []) (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0135 : Complete 4 → ⟪ (CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0135 c4 = pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl

wp0136 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) ⟫ʷ
wp0136 c4 = pw3 c4 (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0137 : Complete 4 → ⟪ (CX41 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX41 ∷ []) ⟫ʷ
wp0137 c4 = pw2 c4 (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ []) tt tt Eq.refl

wp0138 : Complete 4 → ⟪ (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ012 ∷ []) ⟫ʷ
wp0138 c4 = pw3 c4 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (CX41 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0139 : Complete 4 → ⟪ (CCZ024 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp0139 c4 = pw1 c4 (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0140 : Complete 4 → ⟪ (CCZ012 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0140 c4 = pw3 c4 (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0141 : Complete 4 → ⟪ (CCZ012 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ012 ∷ []) ⟫ʷ
wp0141 c4 = pw3 c4 (CCZ012 ∷ CS24 ∷ []) (CS24 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0142 : Complete 4 → ⟪ (CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0142 c4 = pw3 c4 (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0143 : Complete 4 → ⟪ (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp0143 c4 = pw3 c4 (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp0144 : Complete 4 → ⟪ (CX14 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX14 ∷ Toff013 ∷ []) ⟫ʷ
wp0144 c4 = pw2 c4 (CX14 ∷ Toff034 ∷ []) (Toff034 ∷ CX14 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0145 : Complete 4 → ⟪ (CCZ012 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0145 c4 = pw3 c4 (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0146 : Complete 4 → ⟪ (CS23 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS23 ∷ []) ⟫ʷ
wp0146 c4 = pw1 c4 (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl

wp0147 : Complete 4 → ⟪ (CX31 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX31 ∷ []) ⟫ʷ
wp0147 c4 = pw2 c4 (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ []) tt tt Eq.refl

wp0148 : Complete 4 → ⟪ (CX14 ∷ Toff013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0148 c4 = pw2 c4 (CX14 ∷ Toff013 ∷ Toff013 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0149 : Complete 4 → ⟪ (CCZ013 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0149 c4 = pw2 c4 (CCZ013 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0150 : Complete 4 → ⟪ (Sw14 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw14 ∷ []) ⟫ʷ
wp0150 c4 = pw2 c4 (Sw14 ∷ Toff034 ∷ []) (Toff013 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0151 : Complete 4 → ⟪ (CCZ034 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ013 ∷ []) ⟫ʷ
wp0151 c4 = pw2 c4 (CCZ034 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0152 : Complete 4 → ⟪ (Sw14 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw14 ∷ []) ⟫ʷ
wp0152 c4 = pw2 c4 (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0153 : Complete 4 → ⟪ (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0153 c4 = pw3 c4 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0154 : Complete 4 → ⟪ (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0154 c4 = pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0155 : Complete 4 → ⟪ (CCZ014 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0155 c4 = pw3 c4 (CCZ014 ∷ CS02 ∷ []) (CS02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0156 : Complete 4 → ⟪ (CCZ014 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0156 c4 = pw2 c4 (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0157 : Complete 4 → ⟪ (CCZ014 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0157 c4 = pw2 c4 (CCZ014 ∷ CS03 ∷ []) (CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0158 : Complete 4 → ⟪ (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0158 c4 = pw2 c4 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0159 : Complete 4 → ⟪ (CCZ014 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) ⟫ʷ
wp0159 c4 = pw2 c4 (CCZ014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0160 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) ⟫ʷ
wp0160 c4 = pw2 c4 (CCZ014 ∷ []) (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0161 : Complete 4 → ⟪ (CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0161 c4 = pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl

wp0162 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) ⟫ʷ
wp0162 c4 = pw3 c4 (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0163 : Complete 4 → ⟪ (CX42 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX42 ∷ []) ⟫ʷ
wp0163 c4 = pw1 c4 (CX42 ∷ Toff034 ∷ []) (Toff034 ∷ CX42 ∷ []) tt tt Eq.refl

wp0164 : Complete 4 → ⟪ (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ012 ∷ []) ⟫ʷ
wp0164 c4 = pw3 c4 (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (CX42 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0165 : Complete 4 → ⟪ (CCZ014 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0165 c4 = pw2 c4 (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0166 : Complete 4 → ⟪ (CCZ012 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0166 c4 = pw3 c4 (CCZ012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0167 : Complete 4 → ⟪ (CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp0167 c4 = pw3 c4 (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0168 : Complete 4 → ⟪ (CX42 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp0168 c4 = pw3 c4 (CX42 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp0169 : Complete 4 → ⟪ (CX24 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX24 ∷ Toff023 ∷ []) ⟫ʷ
wp0169 c4 = pw1 c4 (CX24 ∷ Toff034 ∷ []) (Toff034 ∷ CX24 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0170 : Complete 4 → ⟪ (CCZ012 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ012 ∷ []) ⟫ʷ
wp0170 c4 = pw3 c4 (CCZ012 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0171 : Complete 4 → ⟪ (CS13 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS13 ∷ []) ⟫ʷ
wp0171 c4 = pw2 c4 (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl

wp0172 : Complete 4 → ⟪ (CX32 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX32 ∷ []) ⟫ʷ
wp0172 c4 = pw1 c4 (CX32 ∷ Toff034 ∷ []) (Toff034 ∷ CX32 ∷ []) tt tt Eq.refl

wp0173 : Complete 4 → ⟪ (Toff023 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff023 ∷ []) ⟫ʷ
wp0173 c4 = pw1 c4 (Toff023 ∷ Toff034 ∷ []) (Toff034 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0174 : Complete 4 → ⟪ (CX24 ∷ Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp0174 c4 = pw1 c4 (CX24 ∷ Toff023 ∷ Toff023 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp0175 : Complete 4 → ⟪ (CCZ023 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ034 ∷ []) ⟫ʷ
wp0175 c4 = pw1 c4 (CCZ023 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0176 : Complete 4 → ⟪ (Sw24 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw24 ∷ []) ⟫ʷ
wp0176 c4 = pw1 c4 (Sw24 ∷ Toff034 ∷ []) (Toff023 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0177 : Complete 4 → ⟪ (CCZ034 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ023 ∷ []) ⟫ʷ
wp0177 c4 = pw1 c4 (CCZ034 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0178 : Complete 4 → ⟪ (Sw24 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw24 ∷ []) ⟫ʷ
wp0178 c4 = pw1 c4 (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0179 : Complete 4 → ⟪ (CCZ024 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0179 c4 = pw3 c4 (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0180 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) ⟫ʷ
wp0180 c4 = pw2 c4 (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0181 : Complete 4 → ⟪ (CX41 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX41 ∷ []) ⟫ʷ
wp0181 c4 = pw3 c4 (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ []) tt tt Eq.refl

wp0182 : Complete 4 → ⟪ (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ013 ∷ []) ⟫ʷ
wp0182 c4 = pw2 c4 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (CX41 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0183 : Complete 4 → ⟪ (CCZ034 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) ⟫ʷ
wp0183 c4 = pw1 c4 (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0184 : Complete 4 → ⟪ (CCZ013 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wp0184 c4 = pw2 c4 (CCZ013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0185 : Complete 4 → ⟪ (CCZ013 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ013 ∷ []) ⟫ʷ
wp0185 c4 = pw2 c4 (CCZ013 ∷ CS34 ∷ []) (CS34 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0186 : Complete 4 → ⟪ (CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0186 c4 = pw2 c4 (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0187 : Complete 4 → ⟪ (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp0187 c4 = pw2 c4 (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp0188 : Complete 4 → ⟪ (CX14 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX14 ∷ Toff012 ∷ []) ⟫ʷ
wp0188 c4 = pw3 c4 (CX14 ∷ Toff024 ∷ []) (Toff024 ∷ CX14 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0189 : Complete 4 → ⟪ (CCZ013 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ013 ∷ []) ⟫ʷ
wp0189 c4 = pw2 c4 (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0190 : Complete 4 → ⟪ (CS23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS23 ∷ []) ⟫ʷ
wp0190 c4 = pw1 c4 (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl

wp0191 : Complete 4 → ⟪ (CX21 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX21 ∷ []) ⟫ʷ
wp0191 c4 = pw3 c4 (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ []) tt tt Eq.refl

wp0192 : Complete 4 → ⟪ (Toff012 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff012 ∷ []) ⟫ʷ
wp0192 c4 = pw3 c4 (Toff012 ∷ Toff024 ∷ []) (Toff024 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0193 : Complete 4 → ⟪ (CX14 ∷ Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0193 c4 = pw3 c4 (CX14 ∷ Toff012 ∷ Toff012 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0194 : Complete 4 → ⟪ (CCZ012 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ024 ∷ []) ⟫ʷ
wp0194 c4 = pw3 c4 (CCZ012 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0195 : Complete 4 → ⟪ (Sw14 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw14 ∷ []) ⟫ʷ
wp0195 c4 = pw3 c4 (Sw14 ∷ Toff024 ∷ []) (Toff012 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0196 : Complete 4 → ⟪ (CCZ024 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0196 c4 = pw3 c4 (CCZ024 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0197 : Complete 4 → ⟪ (Sw14 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw14 ∷ []) ⟫ʷ
wp0197 c4 = pw3 c4 (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0198 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) ⟫ʷ
wp0198 c4 = pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) tt tt Eq.refl

wp0199 : Complete 4 → ⟪ (CCZ023 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ
wp0199 c4 = pw1 c4 (CCZ023 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0200 : Complete 4 → ⟪ (CX13 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX13 ∷ Toff014 ∷ []) ⟫ʷ
wp0200 c4 = pw2 c4 (CX13 ∷ Toff034 ∷ []) (Toff034 ∷ CX13 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0201 : Complete 4 → ⟪ (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ012 ∷ []) ⟫ʷ
wp0201 c4 = pw3 c4 (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0202 : Complete 4 → ⟪ (CS24 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS24 ∷ []) ⟫ʷ
wp0202 c4 = pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl

wp0203 : Complete 4 → ⟪ (Toff014 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff014 ∷ []) ⟫ʷ
wp0203 c4 = pw2 c4 (Toff014 ∷ Toff034 ∷ []) (Toff034 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0204 : Complete 4 → ⟪ (CX13 ∷ Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wp0204 c4 = pw2 c4 (CX13 ∷ Toff014 ∷ Toff014 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wp0205 : Complete 4 → ⟪ (CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ
wp0205 c4 = pw3 c4 (CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0206 : Complete 4 → ⟪ (CCZ014 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ034 ∷ []) ⟫ʷ
wp0206 c4 = pw2 c4 (CCZ014 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0207 : Complete 4 → ⟪ (Sw13 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw13 ∷ []) ⟫ʷ
wp0207 c4 = pw2 c4 (Sw13 ∷ Toff034 ∷ []) (Toff014 ∷ Sw13 ∷ []) tt tt Eq.refl

wp0208 : Complete 4 → ⟪ (CCZ034 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ014 ∷ []) ⟫ʷ
wp0208 c4 = pw2 c4 (CCZ034 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0209 : Complete 4 → ⟪ (Sw13 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw13 ∷ []) ⟫ʷ
wp0209 c4 = pw2 c4 (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ []) tt tt Eq.refl

wp0210 : Complete 4 → ⟪ (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0210 c4 = pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0211 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) ⟫ʷ
wp0211 c4 = pw1 c4 (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) tt tt Eq.refl

wp0212 : Complete 4 → ⟪ (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0212 c4 = pw3 c4 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0213 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) ⟫ʷ
wp0213 c4 = pw1 c4 (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) tt tt Eq.refl

wp0214 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) ⟫ʷ
wp0214 c4 = pw2 c4 (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0215 : Complete 4 → ⟪ (CCZ014 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0215 c4 = pw3 c4 (CCZ014 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0216 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) ⟫ʷ
wp0216 c4 = pw1 c4 (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0217 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) ⟫ʷ
wp0217 c4 = pw2 c4 (CCZ014 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) tt tt Eq.refl

wp0218 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) ⟫ʷ
wp0218 c4 = pw3 c4 (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) tt tt Eq.refl

wp0219 : Complete 4 → ⟪ (K0 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K0 ∷ []) ⟫ʷ
wp0219 c4 = pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl

wp0220 : Complete 4 → ⟪ (K0⁻ ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K0⁻ ∷ []) ⟫ʷ
wp0220 c4 = pw1 c4 (K0⁻ ∷ CCZ034 ∷ []) (Toff034 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0221 : Complete 4 → ⟪ (CCZ034 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0221 c4 = pw2 c4 (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0222 : Complete 4 → ⟪ (CCZ034 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ034 ∷ []) ⟫ʷ
wp0222 c4 = pw1 c4 (CCZ034 ∷ S0 ∷ []) (S0 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0223 : Complete 4 → ⟪ (CCZ034 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0223 c4 = pw1 c4 (CCZ034 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0224 : Complete 4 → ⟪ (CCZ034 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0224 c4 = pw2 c4 (CCZ034 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0225 : Complete 4 → ⟪ (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ034 ∷ []) ⟫ʷ
wp0225 c4 = pw2 c4 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0226 : Complete 4 → ⟪ (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp0226 c4 = pw2 c4 (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp0227 : Complete 4 → ⟪ (CCZ034 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0227 c4 = pw1 c4 (CCZ034 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0228 : Complete 4 → ⟪ (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ034 ∷ []) ⟫ʷ
wp0228 c4 = pw1 c4 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (CX20 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0229 : Complete 4 → ⟪ (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wp0229 c4 = pw1 c4 (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ []) tt tt Eq.refl

wp0230 : Complete 4 → ⟪ (CS03 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0230 c4 = pw1 c4 (CS03 ∷ Toff034 ∷ []) (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0231 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) ⟫ʷ
wp0231 c4 = pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl

wp0232 : Complete 4 → ⟪ (CCZ034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0232 c4 = pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0233 : Complete 4 → ⟪ (CS34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS34 ∷ []) ⟫ʷ
wp0233 c4 = pw1 c4 (CS34 ∷ Toff034 ∷ []) (Toff034 ∷ CS34 ∷ []) tt tt Eq.refl

wp0234 : Complete 4 → ⟪ (CS03 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
wp0234 c4 = pw1 c4 (CS03 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS03 ∷ []) tt tt Eq.refl

wp0235 : Complete 4 → ⟪ (CS03⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0235 c4 = pw1 c4 (CS03⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0236 : Complete 4 → ⟪ (CS34⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0236 c4 = pw1 c4 (CS34⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0237 : Complete 4 → ⟪ (CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
wp0237 c4 = pw1 c4 (CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl

wp0238 : Complete 4 → ⟪ (CZ03 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) ⟫ʷ
wp0238 c4 = pw1 c4 (CZ03 ∷ Toff034 ∷ []) (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0239 : Complete 4 → ⟪ (CZ34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ34 ∷ []) ⟫ʷ
wp0239 c4 = pw1 c4 (CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0240 : Complete 4 → ⟪ (CZ03 ∷ CZ34 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
wp0240 c4 = pw1 c4 (CZ03 ∷ CZ34 ∷ CZ34 ∷ []) (CZ03 ∷ []) tt tt Eq.refl

wp0241 : Complete 4 → ⟪ (CS23⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS23⁻ ∷ []) ⟫ʷ
wp0241 c4 = pw1 c4 (CS23⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wp0242 : Complete 4 → ⟪ (CX30 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX30 ∷ []) ⟫ʷ
wp0242 c4 = pw1 c4 (CX30 ∷ Toff034 ∷ []) (Toff034 ∷ CX30 ∷ []) tt tt Eq.refl

wp0243 : Complete 4 → ⟪ (CS04 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0243 c4 = pw1 c4 (CS04 ∷ Toff034 ∷ []) (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0244 : Complete 4 → ⟪ (CS04 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0244 c4 = pw1 c4 (CS04 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0245 : Complete 4 → ⟪ (CS04⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0245 c4 = pw1 c4 (CS04⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0246 : Complete 4 → ⟪ (CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0246 c4 = pw1 c4 (CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0247 : Complete 4 → ⟪ (CCZ012 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CCZ012 ∷ []) ⟫ʷ
wp0247 c4 = pw3 c4 (CCZ012 ∷ CZ04 ∷ []) (CZ04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0248 : Complete 4 → ⟪ (CZ04 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) ⟫ʷ
wp0248 c4 = pw1 c4 (CZ04 ∷ Toff034 ∷ []) (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0249 : Complete 4 → ⟪ (CZ04 ∷ CZ34 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ []) ⟫ʷ
wp0249 c4 = pw1 c4 (CZ04 ∷ CZ34 ∷ CZ34 ∷ []) (CZ04 ∷ []) tt tt Eq.refl

wp0250 : Complete 4 → ⟪ (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ012 ∷ []) ⟫ʷ
wp0250 c4 = pw3 c4 (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (CX40 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0251 : Complete 4 → ⟪ (CS14 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS14 ∷ []) ⟫ʷ
wp0251 c4 = pw2 c4 (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl

wp0252 : Complete 4 → ⟪ (CS24⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0252 c4 = pw1 c4 (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0253 : Complete 4 → ⟪ (CX40 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX40 ∷ []) ⟫ʷ
wp0253 c4 = pw1 c4 (CX40 ∷ Toff034 ∷ []) (Toff034 ∷ CX40 ∷ []) tt tt Eq.refl

wp0254 : Complete 4 → ⟪ (CX40 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ []) ⟫ʷ
wp0254 c4 = pw3 c4 (CX40 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX40 ∷ []) tt tt Eq.refl

wp0255 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0255 c4 = pw1 c4 (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0256 : Complete 4 → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) ⟫ʷ
wp0256 c4 = pw1 c4 (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0257 : Complete 4 → ⟪ (S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
wp0257 c4 = pw1 c4 (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl

wp0258 : Complete 4 → ⟪ (S0⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ
wp0258 c4 = pw1 c4 (S0⁻ ∷ CS04 ∷ []) (X4 ∷ CS04⁻ ∷ X4 ∷ []) tt tt Eq.refl

wp0259 : Complete 4 → ⟪ (K0 ∷ CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
wp0259 c4 = pw1 c4 (K0 ∷ CK40⁻ ∷ []) (X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl
