------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP01 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0001 : Complete 4 → ⟪ (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0001 c4 = pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0002 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) ⟫ʷ
wp0002 c4 = pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl

wp0003 : Complete 4 → ⟪ (CCZ012 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ012 ∷ []) ⟫ʷ
wp0003 c4 = pw3 c4 (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0004 : Complete 4 → ⟪ (CCZ012 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0004 c4 = pw3 c4 (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0005 : Complete 4 → ⟪ (CCZ034 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ034 ∷ []) ⟫ʷ
wp0005 c4 = pw1 c4 (CCZ034 ∷ Z0 ∷ []) (Z0 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0006 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ034 ∷ Z0 ∷ []) ⟫ʷ
wp0006 c4 = pw1 c4 (CCZ034 ∷ []) (Z0 ∷ CCZ034 ∷ Z0 ∷ []) tt tt Eq.refl

wp0007 : Complete 4 → ⟪ (CCZ034 ∷ CS34⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0007 c4 = pw1 c4 (CCZ034 ∷ CS34⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0008 : Complete 4 → ⟪ (S0 ∷ K0 ∷ CCZ034 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wp0008 c4 = pw1 c4 (S0 ∷ K0 ∷ CCZ034 ∷ CS34⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl

wp0009 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0009 c4 = pw1 c4 (CCZ034 ∷ []) (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0010 : Complete 4 → ⟪ (Toff034 ∷ CCZ034 ∷ Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0010 c4 = pw1 c4 (Toff034 ∷ CCZ034 ∷ Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0011 : Complete 4 → ⟪ (K0 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K0 ∷ []) ⟫ʷ
wp0011 c4 = pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl

wp0012 : Complete 4 → ⟪ (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0012 c4 = pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0013 : Complete 4 → ⟪ (Toff034 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ Toff034 ∷ CZ34 ∷ []) ⟫ʷ
wp0013 c4 = pw1 c4 (Toff034 ∷ Z0 ∷ []) (Z0 ∷ Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0014 : Complete 4 → ⟪ (CZ34 ∷ Toff034 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0014 c4 = pw1 c4 (CZ34 ∷ Toff034 ∷ CZ34 ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0015 : Complete 4 → ⟪ (CCZ034 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ034 ∷ []) ⟫ʷ
wp0015 c4 = pw1 c4 (CCZ034 ∷ S0 ∷ []) (S0 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0016 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ034 ∷ S0⁻ ∷ []) ⟫ʷ
wp0016 c4 = pw1 c4 (CCZ034 ∷ []) (S0 ∷ CCZ034 ∷ S0⁻ ∷ []) tt tt Eq.refl

wp0017 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
wp0017 c4 = pw3 c4 (CCZ012 ∷ Toff012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0018 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
wp0018 c4 = pw3 c4 (CCZ012 ∷ Toff012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0019 : Complete 4 → ⟪ (CCZ034 ∷ CCZ134 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ034 ∷ []) ⟫ʷ
wp0019 c4 = pw2 c4 (CCZ034 ∷ CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0020 : Complete 4 → ⟪ (CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ034 ∷ CX10 ∷ []) ⟫ʷ
wp0020 c4 = pw2 c4 (CCZ034 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ CX10 ∷ []) tt tt Eq.refl

wp0021 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0021 c4 = pw2 c4 (CCZ034 ∷ []) (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0022 : Complete 4 → ⟪ (CCZ034 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0022 c4 = pw1 c4 (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0023 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ034 ∷ CS02⁻ ∷ []) ⟫ʷ
wp0023 c4 = pw1 c4 (CCZ034 ∷ []) (CS02 ∷ CCZ034 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp0024 : Complete 4 → ⟪ (CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0024 c4 = pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl

wp0025 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0025 c4 = pw1 c4 (CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0026 : Complete 4 → ⟪ (CCZ034 ∷ CCZ024 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0026 c4 = pw1 c4 (CCZ034 ∷ CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0027 : Complete 4 → ⟪ (CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ034 ∷ CX23 ∷ []) ⟫ʷ
wp0027 c4 = pw1 c4 (CCZ034 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ CX23 ∷ []) tt tt Eq.refl

wp0028 : Complete 4 → ⟪ (CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0028 c4 = pw3 c4 (CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0029 : Complete 4 → ⟪ (CCZ034 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0029 c4 = pw2 c4 (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0030 : Complete 4 → ⟪ (CCZ034 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0030 c4 = pw1 c4 (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0031 : Complete 4 → ⟪ (CCZ034 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ034 ∷ []) ⟫ʷ
wp0031 c4 = pw1 c4 (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0032 : Complete 4 → ⟪ (CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0032 c4 = pw1 c4 (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0033 : Complete 4 → ⟪ (CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ024 ∷ []) ⟫ʷ
wp0033 c4 = pw3 c4 (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0034 : Complete 4 → ⟪ (CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0034 c4 = pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl

wp0035 : Complete 4 → ⟪ (CCZ034 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ034 ∷ []) ⟫ʷ
wp0035 c4 = pw1 c4 (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0036 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ034 ∷ CX32 ∷ []) ⟫ʷ
wp0036 c4 = pw1 c4 (CCZ034 ∷ []) (CX32 ∷ CCZ034 ∷ CX32 ∷ []) tt tt Eq.refl

wp0037 : Complete 4 → ⟪ (CCZ034 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ034 ∷ []) ⟫ʷ
wp0037 c4 = pw2 c4 (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0038 : Complete 4 → ⟪ (CCZ034 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0038 c4 = pw1 c4 (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0039 : Complete 4 → ⟪ (CCZ034 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0039 c4 = pw1 c4 (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0040 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0040 c4 = pw2 c4 (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff013 ∷ CCZ013 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0041 : Complete 4 → ⟪ (CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ
wp0041 c4 = pw3 c4 (CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0042 : Complete 4 → ⟪ (CCZ124 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ124 ∷ []) ⟫ʷ
wp0042 c4 = pw3 c4 (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0043 : Complete 4 → ⟪ (CCZ012 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0043 c4 = pw3 c4 (CCZ012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0044 : Complete 4 → ⟪ (CCZ012 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0044 c4 = pw3 c4 (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0045 : Complete 4 → ⟪ (CS14⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0045 c4 = pw3 c4 (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0046 : Complete 4 → ⟪ (CS14 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS14 ∷ []) ⟫ʷ
wp0046 c4 = pw3 c4 (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) tt tt Eq.refl

wp0047 : Complete 4 → ⟪ (CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0047 c4 = pw2 c4 (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0048 : Complete 4 → ⟪ (CZ14 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0048 c4 = pw2 c4 (CZ14 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) [] tt tt Eq.refl

wp0049 : Complete 4 → ⟪ (CX24 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX24 ∷ []) ⟫ʷ
wp0049 c4 = pw3 c4 (CX24 ∷ Toff012 ∷ []) (Toff012 ∷ CX24 ∷ []) tt tt Eq.refl

wp0050 : Complete 4 → ⟪ (CCZ012 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0050 c4 = pw3 c4 (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0051 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) ⟫ʷ
wp0051 c4 = pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl

wp0052 : Complete 4 → ⟪ (CCZ012 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ012 ∷ []) ⟫ʷ
wp0052 c4 = pw3 c4 (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0053 : Complete 4 → ⟪ (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ []) ⟫ʷ
wp0053 c4 = pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl

wp0054 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0054 c4 = pw3 c4 (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0055 : Complete 4 → ⟪ (CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0055 c4 = pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl

wp0056 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0056 c4 = pw2 c4 (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0057 : Complete 4 → ⟪ (CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0057 c4 = pw3 c4 (CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0058 : Complete 4 → ⟪ (Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0058 c4 = pw1 c4 (Toff304 ∷ Toff304 ∷ []) [] tt tt Eq.refl

wp0059 : Complete 4 → ⟪ (Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0059 c4 = pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl

wp0060 : Complete 4 → ⟪ (CCZ034 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ034 ∷ []) ⟫ʷ
wp0060 c4 = pw2 c4 (CCZ034 ∷ X1 ∷ []) (X1 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0061 : Complete 4 → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CCZ034 ∷ X1 ∷ []) ⟫ʷ
wp0061 c4 = pw2 c4 (CCZ034 ∷ []) (X1 ∷ CCZ034 ∷ X1 ∷ []) tt tt Eq.refl

wp0062 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0062 c4 = pw1 c4 (CCZ234 ∷ []) (CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0063 : Complete 4 → ⟪ (K1⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ K1⁻ ∷ []) ⟫ʷ
wp0063 c4 = pw2 c4 (K1⁻ ∷ CCZ014 ∷ []) (Toff104 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0064 : Complete 4 → ⟪ (Toff104 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0064 c4 = pw2 c4 (Toff104 ∷ Toff104 ∷ []) [] tt tt Eq.refl

wp0065 : Complete 4 → ⟪ (CCZ012 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ
wp0065 c4 = pw3 c4 (CCZ012 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0066 : Complete 4 → ⟪ (CCZ024 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp0066 c4 = pw1 c4 (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0067 : Complete 4 → ⟪ (CCZ024 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ024 ∷ []) ⟫ʷ
wp0067 c4 = pw3 c4 (CCZ024 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0068 : Complete 4 → ⟪ (CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0068 c4 = pw3 c4 (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0069 : Complete 4 → ⟪ (CCZ014 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff104 ∷ []) ⟫ʷ
wp0069 c4 = pw2 c4 (CCZ014 ∷ K1 ∷ []) (K1 ∷ Toff104 ∷ []) tt tt Eq.refl

wp0070 : Complete 4 → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff104 ∷ K1⁻ ∷ []) ⟫ʷ
wp0070 c4 = pw2 c4 (CCZ014 ∷ []) (K1 ∷ Toff104 ∷ K1⁻ ∷ []) tt tt Eq.refl

wp0071 : Complete 4 → ⟪ (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0071 c4 = pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl

wp0072 : Complete 4 → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0072 c4 = pw2 c4 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0073 : Complete 4 → ⟪ (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ []) ⟫ʷ
wp0073 c4 = pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ []) tt tt Eq.refl

wp0074 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) ⟫ʷ
wp0074 c4 = pw1 c4 (CK40 ∷ []) (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl

wp0075 : Complete 4 → ⟪ (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ []) ⟫ʷ
wp0075 c4 = pw1 c4 (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ []) tt tt Eq.refl

wp0076 : Complete 4 → ⟪ (K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0076 c4 = pw1 c4 (K0⁻ ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0077 : Complete 4 → ⟪ (CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ []) ⟫ʷ
wp0077 c4 = pw2 c4 (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0078 : Complete 4 → ⟪ (CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) ⟫ʷ
wp0078 c4 = pw2 c4 (CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0079 : Complete 4 → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ []) ⟫ʷ
wp0079 c4 = pw1 c4 (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ []) tt tt Eq.refl

wp0080 : Complete 4 → ⟪ (CX40 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0080 c4 = pw1 c4 (CX40 ∷ CX40 ∷ []) [] tt tt Eq.refl

wp0081 : Complete 4 → ⟪ (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ []) ⟫ʷ
wp0081 c4 = pw2 c4 (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ []) tt tt Eq.refl

wp0082 : Complete 4 → ⟪ (CS03⁻ ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0082 c4 = pw2 c4 (CS03⁻ ∷ CX41 ∷ []) (CX41 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0083 : Complete 4 → ⟪ (CCZ014 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CZ04 ∷ CCZ014 ∷ []) ⟫ʷ
wp0083 c4 = pw2 c4 (CCZ014 ∷ CX41 ∷ []) (CX41 ∷ CZ04 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0084 : Complete 4 → ⟪ (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ []) ⟫ʷ
wp0084 c4 = pw2 c4 (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ []) tt tt Eq.refl

wp0085 : Complete 4 → ⟪ (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) ⟫ʷ
wp0085 c4 = pw2 c4 (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) tt tt Eq.refl

wp0086 : Complete 4 → ⟪ (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) ⟫ʷ
wp0086 c4 = pw2 c4 (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ []) (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0087 : Complete 4 → ⟪ (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CCZ014 ∷ []) ⟫ʷ
wp0087 c4 = pw2 c4 (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0088 : Complete 4 → ⟪ (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wp0088 c4 = pw2 c4 (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS01 ∷ []) tt tt Eq.refl

wp0089 : Complete 4 → ⟪ (CS12⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0089 c4 = pw3 c4 (CS12⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0090 : Complete 4 → ⟪ (K0⁻ ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ K0⁻ ∷ []) ⟫ʷ
wp0090 c4 = pw2 c4 (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0091 : Complete 4 → ⟪ (CS01 ∷ Toff104 ∷ CS13 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CS13 ∷ Toff104 ∷ CS01 ∷ []) ⟫ʷ
wp0091 c4 = pw2 c4 (CS01 ∷ Toff104 ∷ CS13 ∷ Toff104 ∷ []) (Toff104 ∷ CS13 ∷ Toff104 ∷ CS01 ∷ []) tt tt Eq.refl

wp0092 : Complete 4 → ⟪ (K0 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ K0 ∷ []) ⟫ʷ
wp0092 c4 = pw2 c4 (K0 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ []) tt tt Eq.refl

wp0093 : Complete 4 → ⟪ (CS12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS12 ∷ []) ⟫ʷ
wp0093 c4 = pw3 c4 (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) tt tt Eq.refl

wp0094 : Complete 4 → ⟪ (K4 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K4 ∷ []) ⟫ʷ
wp0094 c4 = pw1 c4 (K4 ∷ Toff023 ∷ []) (Toff023 ∷ K4 ∷ []) tt tt Eq.refl

wp0095 : Complete 4 → ⟪ (K4⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K4⁻ ∷ []) ⟫ʷ
wp0095 c4 = pw1 c4 (K4⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K4⁻ ∷ []) tt tt Eq.refl

wp0096 : Complete 4 → ⟪ (CS14⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0096 c4 = pw2 c4 (CS14⁻ ∷ K0 ∷ []) (K0 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0097 : Complete 4 → ⟪ (CS14 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS14 ∷ []) ⟫ʷ
wp0097 c4 = pw2 c4 (CS14 ∷ K0 ∷ []) (K0 ∷ CS14 ∷ []) tt tt Eq.refl

wp0098 : Complete 4 → ⟪ (CS02 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS02 ∷ []) ⟫ʷ
wp0098 c4 = pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl

wp0099 : Complete 4 → ⟪ (CS02 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS02 ∷ []) ⟫ʷ
wp0099 c4 = pw3 c4 (CS02 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02 ∷ []) tt tt Eq.refl

wp0100 : Complete 4 → ⟪ (CS02 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS02 ∷ []) ⟫ʷ
wp0100 c4 = pw3 c4 (CS02 ∷ CS14 ∷ []) (CS14 ∷ CS02 ∷ []) tt tt Eq.refl

wp0101 : Complete 4 → ⟪ (CS01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS01 ∷ []) ⟫ʷ
wp0101 c4 = pw2 c4 (CS01 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS01 ∷ []) tt tt Eq.refl

wp0102 : Complete 4 → ⟪ (CS01 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS01 ∷ []) ⟫ʷ
wp0102 c4 = pw2 c4 (CS01 ∷ CS14 ∷ []) (CS14 ∷ CS01 ∷ []) tt tt Eq.refl

wp0103 : Complete 4 → ⟪ (CCZ024 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0103 c4 = pw1 c4 (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0104 : Complete 4 → ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ
wp0104 c4 = pw2 c4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4⁻ ∷ []) (K4⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) tt tt Eq.refl

wp0105 : Complete 4 → ⟪ (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) ⟫ʷ
wp0105 c4 = pw2 c4 (CS34 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS34 ∷ []) tt tt Eq.refl

wp0106 : Complete 4 → ⟪ (CS03⁻ ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0106 c4 = pw1 c4 (CS03⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0107 : Complete 4 → ⟪ (CS03⁻ ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0107 c4 = pw1 c4 (CS03⁻ ∷ CS24 ∷ []) (CS24 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0108 : Complete 4 → ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ
wp0108 c4 = pw2 c4 (CX13 ∷ CS03⁻ ∷ CX13 ∷ K4 ∷ []) (K4 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) tt tt Eq.refl

wp0109 : Complete 4 → ⟪ (CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0109 c4 = pw2 c4 (CS14⁻ ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0110 : Complete 4 → ⟪ (CS14 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) ⟫ʷ
wp0110 c4 = pw2 c4 (CS14 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ []) (CX13 ∷ CS03⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl

wp0111 : Complete 4 → ⟪ (CS14⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wp0111 c4 = pw2 c4 (CS14⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0112 : Complete 4 → ⟪ (CS14 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS14 ∷ []) ⟫ʷ
wp0112 c4 = pw2 c4 (CS14 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS14 ∷ []) tt tt Eq.refl

wp0113 : Complete 4 → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0113 c4 = pw1 c4 (CS04 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0114 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0114 c4 = pw1 c4 (CS04⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0115 : Complete 4 → ⟪ (CS03 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS03 ∷ []) ⟫ʷ
wp0115 c4 = pw2 c4 (CS03 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03 ∷ []) tt tt Eq.refl

wp0116 : Complete 4 → ⟪ (CS03 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS03 ∷ []) ⟫ʷ
wp0116 c4 = pw1 c4 (CS03 ∷ Toff423 ∷ []) (Toff423 ∷ CS03 ∷ []) tt tt Eq.refl

wp0117 : Complete 4 → ⟪ (CS03 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS03 ∷ []) ⟫ʷ
wp0117 c4 = pw2 c4 (CS03 ∷ CS14 ∷ []) (CS14 ∷ CS03 ∷ []) tt tt Eq.refl

wp0118 : Complete 4 → ⟪ (CS03⁻ ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
wp0118 c4 = pw2 c4 (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0119 : Complete 4 → ⟪ (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) ⟫ʷ
wp0119 c4 = pw1 c4 (CX23 ∷ CS03⁻ ∷ CX23 ∷ Toff423 ∷ []) (Toff423 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) tt tt Eq.refl

wp0120 : Complete 4 → ⟪ (CS03⁻ ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0120 c4 = pw2 c4 (CS03⁻ ∷ CS14 ∷ []) (CS14 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0121 : Complete 4 → ⟪ (CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ012 ∷ []) ⟫ʷ
wp0121 c4 = pw3 c4 (CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0122 : Complete 4 → ⟪ (CCZ014 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ014 ∷ []) ⟫ʷ
wp0122 c4 = pw2 c4 (CCZ014 ∷ S0 ∷ []) (S0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0123 : Complete 4 → ⟪ (S0⁻ ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ S0⁻ ∷ []) ⟫ʷ
wp0123 c4 = pw1 c4 (S0⁻ ∷ Toff403 ∷ []) (Toff403 ∷ S0⁻ ∷ []) tt tt Eq.refl

wp0124 : Complete 4 → ⟪ (CK40⁻ ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0124 c4 = pw1 c4 (CK40⁻ ∷ CK40 ∷ []) [] tt tt Eq.refl

wp0125 : Complete 4 → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4⁻ ∷ []) ⟫ʷ
wp0125 c4 = pw1 c4 (CK40 ∷ CK40 ∷ []) (S4⁻ ∷ []) tt tt Eq.refl

wp0126 : Complete 4 → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) ⟫ʷ
wp0126 c4 = pw1 c4 (CK40 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0127 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0127 c4 = pw3 c4 (CS14⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0128 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0128 c4 = pw2 c4 (CS14⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0129 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0129 c4 = pw2 c4 (CS14⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0130 : Complete 4 → ⟪ (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) ⟫ʷ
wp0130 c4 = pw3 c4 (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) tt tt Eq.refl

wp0131 : Complete 4 → ⟪ (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0131 c4 = pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0132 : Complete 4 → ⟪ (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) ⟫ʷ
wp0132 c4 = pw2 c4 (Toff314 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0133 : Complete 4 → ⟪ (CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0133 c4 = pw2 c4 (CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0134 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wp0134 c4 = pw3 c4 (CS01 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wp0135 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wp0135 c4 = pw2 c4 (CS01 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wp0136 : Complete 4 → ⟪ (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) ⟫ʷ
wp0136 c4 = pw3 c4 (CS01 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01 ∷ []) tt tt Eq.refl

wp0137 : Complete 4 → ⟪ (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) ⟫ʷ
wp0137 c4 = pw2 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl

wp0138 : Complete 4 → ⟪ (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) ⟫ʷ
wp0138 c4 = pw2 c4 (K0 ∷ CS01 ∷ K0 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ []) tt tt Eq.refl

wp0139 : Complete 4 → ⟪ (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) ⟫ʷ
wp0139 c4 = pw3 c4 (S1⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1⁻ ∷ []) tt tt Eq.refl

wp0140 : Complete 4 → ⟪ (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) ⟫ʷ
wp0140 c4 = pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl

wp0141 : Complete 4 → ⟪ (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) ⟫ʷ
wp0141 c4 = pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl

wp0142 : Complete 4 → ⟪ (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp0142 c4 = pw1 c4 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp0143 : Complete 4 → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) ⟫ʷ
wp0143 c4 = pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl

wp0144 : Complete 4 → ⟪ (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) ⟫ʷ
wp0144 c4 = pw2 c4 (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) tt tt Eq.refl

wp0145 : Complete 4 → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ S4 ∷ ι⁻ ∷ []) ⟫ʷ
wp0145 c4 = pw1 c4 (CK40⁻ ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ S4 ∷ ι⁻ ∷ []) tt tt Eq.refl

wp0146 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wp0146 c4 = pw3 c4 (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp0147 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wp0147 c4 = pw2 c4 (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp0148 : Complete 4 → ⟪ (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) ⟫ʷ
wp0148 c4 = pw3 c4 (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp0149 : Complete 4 → ⟪ (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wp0149 c4 = pw2 c4 (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0150 : Complete 4 → ⟪ (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wp0150 c4 = pw2 c4 (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0151 : Complete 4 → ⟪ (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0151 c4 = pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0152 : Complete 4 → ⟪ (Toff314 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Toff314 ∷ []) ⟫ʷ
wp0152 c4 = pw2 c4 (Toff314 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff314 ∷ []) tt tt Eq.refl

wp0153 : Complete 4 → ⟪ (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) ⟫ʷ
wp0153 c4 = pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl

wp0154 : Complete 4 → ⟪ (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) ⟫ʷ
wp0154 c4 = pw2 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl

wp0155 : Complete 4 → ⟪ (Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ []) ⟫ʷ
wp0155 c4 = pw3 c4 (Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0156 : Complete 4 → ⟪ (CCZ024 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ024 ∷ []) ⟫ʷ
wp0156 c4 = pw1 c4 (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0157 : Complete 4 → ⟪ (CZ13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX04 ∷ X1 ∷ CZ13 ∷ []) ⟫ʷ
wp0157 c4 = pw2 c4 (CZ13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CZ13 ∷ []) tt tt Eq.refl

wp0158 : Complete 4 → ⟪ (CCZ024 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0158 c4 = pw1 c4 (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0159 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff204 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wp0159 c4 = pw3 c4 (CS14 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wp0160 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03⁻ ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wp0160 c4 = pw2 c4 (CS14 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wp0161 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS03 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wp0161 c4 = pw2 c4 (CS14 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wp0162 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wp0162 c4 = pw2 c4 (CS14 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wp0163 : Complete 4 → ⟪ (CCZ034 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ034 ∷ []) ⟫ʷ
wp0163 c4 = pw2 c4 (CCZ034 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0164 : Complete 4 → ⟪ (CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ []) ⟫ʷ
wp0164 c4 = pw2 c4 (CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03 ∷ []) tt tt Eq.refl

wp0165 : Complete 4 → ⟪ (CS03⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0165 c4 = pw2 c4 (CS03⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0166 : Complete 4 → ⟪ (CCZ034 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ CCZ034 ∷ []) ⟫ʷ
wp0166 c4 = pw2 c4 (CCZ034 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0167 : Complete 4 → ⟪ (CK10 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ []) ⟫ʷ
wp0167 c4 = pw2 c4 (CK10 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ []) tt tt Eq.refl

wp0168 : Complete 4 → ⟪ (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) ⟫ʷ
wp0168 c4 = pw2 c4 (CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ []) tt tt Eq.refl

wp0169 : Complete 4 → ⟪ (Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ []) ⟫ʷ
wp0169 c4 = pw3 c4 (Toff204 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0170 : Complete 4 → ⟪ (Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ []) ⟫ʷ
wp0170 c4 = pw3 c4 (Toff204 ∷ X1 ∷ S1 ∷ X1 ∷ []) (X1 ∷ S1 ∷ X1 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0171 : Complete 4 → ⟪ (CK10⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS14⁻ ∷ X1 ∷ CK10⁻ ∷ []) ⟫ʷ
wp0171 c4 = pw2 c4 (CK10⁻ ∷ X1 ∷ CS14⁻ ∷ X1 ∷ []) (X1 ∷ CS14⁻ ∷ X1 ∷ CK10⁻ ∷ []) tt tt Eq.refl

wp0172 : Complete 4 → ⟪ (CS14 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS14 ∷ []) ⟫ʷ
wp0172 c4 = pw2 c4 (CS14 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS14 ∷ []) tt tt Eq.refl

wp0173 : Complete 4 → ⟪ (CCZ024 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ024 ∷ []) ⟫ʷ
wp0173 c4 = pw1 c4 (CCZ024 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ []) (CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0174 : Complete 4 → ⟪ (CCZ014 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0174 c4 = pw2 c4 (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0175 : Complete 4 → ⟪ (CCZ012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS24 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
wp0175 c4 = pw3 c4 (CCZ012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ []) (Toff201 ∷ CS24 ∷ Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0176 : Complete 4 → ⟪ (CCZ012 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0176 c4 = pw3 c4 (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0177 : Complete 4 → ⟪ (CCZ012 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ012 ∷ []) ⟫ʷ
wp0177 c4 = pw3 c4 (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0178 : Complete 4 → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) ⟫ʷ
wp0178 c4 = pw0 c4 (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) tt tt Eq.refl

wp0179 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (S4⁻ ∷ []) ⟫ʷ
wp0179 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (S4⁻ ∷ []) tt tt Eq.refl

wp0180 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0180 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0181 : Complete 4 → ⟪ (S0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wp0181 c4 = pw1 c4 (S0 ∷ X0 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04⁻ ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wp0182 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0182 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ Toff204 ∷ X0 ∷ []) (X0 ∷ Toff204 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0183 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0183 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0184 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CX13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0184 c4 = pw2 c4 (CS04⁻ ∷ X0 ∷ CX13 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0185 : Complete 4 → ⟪ (CS04⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0185 c4 = pw1 c4 (CS04⁻ ∷ X0 ∷ CS23⁻ ∷ X0 ∷ []) (X0 ∷ CS23⁻ ∷ X0 ∷ CS04⁻ ∷ []) tt tt Eq.refl
