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

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0001 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0001 c4 L = pw2 c4 L (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0002 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0002 c4 L = pw1 c4 L (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0003 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0003 c4 L = pw1 c4 L (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0004 : Base 4 → WsL → ⟪ (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0004 c4 L = pw1 c4 L (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0005 : Base 4 → WsL → ⟪ (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0005 c4 L = pw1 c4 L (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0006 : Base 4 → WsL → ⟪ (Toff034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0006 c4 L = pw1 c4 L (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl

wp0007 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0007 c4 L = pw1 c4 L (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl

wp0008 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0008 c4 L = pw2 c4 L (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0009 : Base 4 → WsL → ⟪ (CZ01 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) ⟫ʷ
wp0009 c4 L = pw2 c4 L (CZ01 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0010 : Base 4 → WsL → ⟪ (Toff034 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff034 ∷ []) ⟫ʷ
wp0010 c4 L = pw1 c4 L (Toff034 ∷ X2 ∷ []) (X2 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0011 : Base 4 → WsL → ⟪ (CCZ012 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0011 c4 L = pw3 c4 L (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0012 : Base 4 → WsL → ⟪ (CCZ134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ134 ∷ []) ⟫ʷ
wp0012 c4 L = pw2 c4 L (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0013 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) ⟫ʷ
wp0013 c4 L = pw1 c4 L (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) tt tt Eq.refl

wp0014 : Base 4 → WsL → ⟪ (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp0014 c4 L = pw1 c4 L (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp0015 : Base 4 → WsL → ⟪ (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
wp0015 c4 L = pw1 c4 L (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0016 : Base 4 → WsL → ⟪ (CS04⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS04⁻ ∷ []) ⟫ʷ
wp0016 c4 L = pw2 c4 L (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0017 : Base 4 → WsL → ⟪ (CS04⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0017 c4 L = pw1 c4 L (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0018 : Base 4 → WsL → ⟪ (CS04⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS04⁻ ∷ []) ⟫ʷ
wp0018 c4 L = pw1 c4 L (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0019 : Base 4 → WsL → ⟪ (Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0019 c4 L = pw1 c4 L (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl

wp0020 : Base 4 → WsL → ⟪ (CCZ024 ∷ X4 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ024 ∷ []) ⟫ʷ
wp0020 c4 L = pw3 c4 L (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0021 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ024 ∷ []) ⟫ʷ
wp0021 c4 L = pw1 c4 L (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0022 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ024 ∷ []) ⟫ʷ
wp0022 c4 L = pw3 c4 L (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0023 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ024 ∷ []) ⟫ʷ
wp0023 c4 L = pw3 c4 L (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0024 : Base 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ
wp0024 c4 L = pw2 c4 L (CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ []) tt tt Eq.refl

wp0025 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) ⟫ʷ
wp0025 c4 L = pw1 c4 L (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0026 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ []) ⟫ʷ
wp0026 c4 L = pw1 c4 L (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ []) tt tt Eq.refl

wp0027 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
wp0027 c4 L = pw1 c4 L (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0028 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) ⟫ʷ
wp0028 c4 L = pw1 c4 L (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0029 : Base 4 → WsL → ⟪ (CS01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ []) ⟫ʷ
wp0029 c4 L = pw2 c4 L (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ []) tt tt Eq.refl

wp0030 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ013 ∷ []) ⟫ʷ
wp0030 c4 L = pw2 c4 L (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0031 : Base 4 → WsL → ⟪ (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0031 c4 L = pw2 c4 L (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0032 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0032 c4 L = pw1 c4 L (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0033 : Base 4 → WsL → ⟪ (CCZ024 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0033 c4 L = pw1 c4 L (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0034 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ024 ∷ []) ⟫ʷ
wp0034 c4 L = pw3 c4 L (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0035 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0035 c4 L = pw1 c4 L (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0036 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ024 ∷ []) ⟫ʷ
wp0036 c4 L = pw1 c4 L (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0037 : Base 4 → WsL → ⟪ (CCZ024 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ024 ∷ []) ⟫ʷ
wp0037 c4 L = pw1 c4 L (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0038 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0038 c4 L = pw3 c4 L (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0039 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ024 ∷ []) ⟫ʷ
wp0039 c4 L = pw3 c4 L (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0040 : Base 4 → WsL → ⟪ (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0040 c4 L = pw2 c4 L (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0041 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) ⟫ʷ
wp0041 c4 L = pw2 c4 L (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl

wp0042 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ024 ∷ []) ⟫ʷ
wp0042 c4 L = pw3 c4 L (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0043 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ CS03 ∷ []) ⟫ʷ
wp0043 c4 L = pw2 c4 L (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ []) tt tt Eq.refl

wp0044 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) ⟫ʷ
wp0044 c4 L = pw3 c4 L (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) tt tt Eq.refl

wp0045 : Base 4 → WsL → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0045 c4 L = pw2 c4 L (CS01 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0046 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) ⟫ʷ
wp0046 c4 L = pw2 c4 L (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) tt tt Eq.refl

wp0047 : Base 4 → WsL → ⟪ (CCZ023 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wp0047 c4 L = pw1 c4 L (CCZ023 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0048 : Base 4 → WsL → ⟪ (CCZ023 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ023 ∷ []) ⟫ʷ
wp0048 c4 L = pw1 c4 L (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0049 : Base 4 → WsL → ⟪ (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp0049 c4 L = pw2 c4 L (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp0050 : Base 4 → WsL → ⟪ (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0050 c4 L = pw2 c4 L (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0051 : Base 4 → WsL → ⟪ (Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0051 c4 L = pw2 c4 L (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl

wp0052 : Base 4 → WsL → ⟪ (CCZ014 ∷ X4 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ014 ∷ []) ⟫ʷ
wp0052 c4 L = pw2 c4 L (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (X4 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0053 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ014 ∷ []) ⟫ʷ
wp0053 c4 L = pw2 c4 L (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0054 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ014 ∷ []) ⟫ʷ
wp0054 c4 L = pw3 c4 L (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0055 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ014 ∷ []) ⟫ʷ
wp0055 c4 L = pw2 c4 L (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0056 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) ⟫ʷ
wp0056 c4 L = pw2 c4 L (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0057 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ []) ⟫ʷ
wp0057 c4 L = pw2 c4 L (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl

wp0058 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0058 c4 L = pw2 c4 L (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0059 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) ⟫ʷ
wp0059 c4 L = pw2 c4 L (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0060 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0060 c4 L = pw2 c4 L (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0061 : Base 4 → WsL → ⟪ (CCZ014 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0061 c4 L = pw2 c4 L (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0062 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ014 ∷ []) ⟫ʷ
wp0062 c4 L = pw3 c4 L (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0063 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0063 c4 L = pw2 c4 L (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0064 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ014 ∷ []) ⟫ʷ
wp0064 c4 L = pw2 c4 L (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0065 : Base 4 → WsL → ⟪ (CCZ014 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ014 ∷ []) ⟫ʷ
wp0065 c4 L = pw2 c4 L (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0066 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp0066 c4 L = pw3 c4 L (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0067 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ014 ∷ []) ⟫ʷ
wp0067 c4 L = pw3 c4 L (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0068 : Base 4 → WsL → ⟪ (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff023 ∷ []) ⟫ʷ
wp0068 c4 L = pw1 c4 L (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0069 : Base 4 → WsL → ⟪ (CS24⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0069 c4 L = pw1 c4 L (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0070 : Base 4 → WsL → ⟪ (CS24 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS24 ∷ []) ⟫ʷ
wp0070 c4 L = pw1 c4 L (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl

wp0071 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0071 c4 L = pw3 c4 L (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0072 : Base 4 → WsL → ⟪ (Toff023 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff023 ∷ []) ⟫ʷ
wp0072 c4 L = pw1 c4 L (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0073 : Base 4 → WsL → ⟪ (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wp0073 c4 L = pw1 c4 L (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wp0074 : Base 4 → WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) ⟫ʷ
wp0074 c4 L = pw3 c4 L (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0075 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) ⟫ʷ
wp0075 c4 L = pw1 c4 L (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl

wp0076 : Base 4 → WsL → ⟪ (CCZ013 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wp0076 c4 L = pw2 c4 L (CCZ013 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0077 : Base 4 → WsL → ⟪ (CCZ013 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ013 ∷ []) ⟫ʷ
wp0077 c4 L = pw2 c4 L (CCZ013 ∷ CS04 ∷ []) (CS04 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0078 : Base 4 → WsL → ⟪ (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp0078 c4 L = pw1 c4 L (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp0079 : Base 4 → WsL → ⟪ (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0079 c4 L = pw1 c4 L (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0080 : Base 4 → WsL → ⟪ (Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0080 c4 L = pw1 c4 L (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl

wp0081 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ024 ∷ []) ⟫ʷ
wp0081 c4 L = pw3 c4 L (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0082 : Base 4 → WsL → ⟪ (CCZ024 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ024 ∷ []) ⟫ʷ
wp0082 c4 L = pw1 c4 L (CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0083 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) ⟫ʷ
wp0083 c4 L = pw1 c4 L (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0084 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp0084 c4 L = pw1 c4 L (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp0085 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0085 c4 L = pw1 c4 L (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0086 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) ⟫ʷ
wp0086 c4 L = pw1 c4 L (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0087 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0087 c4 L = pw3 c4 L (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0088 : Base 4 → WsL → ⟪ (CCZ024 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0088 c4 L = pw3 c4 L (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0089 : Base 4 → WsL → ⟪ (CCZ024 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ024 ∷ []) ⟫ʷ
wp0089 c4 L = pw3 c4 L (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0090 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp0090 c4 L = pw1 c4 L (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0091 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0091 c4 L = pw1 c4 L (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0092 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ024 ∷ []) ⟫ʷ
wp0092 c4 L = pw1 c4 L (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0093 : Base 4 → WsL → ⟪ (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff013 ∷ []) ⟫ʷ
wp0093 c4 L = pw2 c4 L (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0094 : Base 4 → WsL → ⟪ (CS34⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0094 c4 L = pw2 c4 L (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0095 : Base 4 → WsL → ⟪ (CS34 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS34 ∷ []) ⟫ʷ
wp0095 c4 L = pw2 c4 L (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) tt tt Eq.refl

wp0096 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0096 c4 L = pw1 c4 L (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0097 : Base 4 → WsL → ⟪ (Toff013 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff013 ∷ []) ⟫ʷ
wp0097 c4 L = pw2 c4 L (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0098 : Base 4 → WsL → ⟪ (CS23 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) ⟫ʷ
wp0098 c4 L = pw1 c4 L (CS23 ∷ CCZ234 ∷ []) (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0099 : Base 4 → WsL → ⟪ (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wp0099 c4 L = pw2 c4 L (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wp0100 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ034 ∷ []) ⟫ʷ
wp0100 c4 L = pw2 c4 L (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0101 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ034 ∷ []) ⟫ʷ
wp0101 c4 L = pw1 c4 L (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0102 : Base 4 → WsL → ⟪ (CS14 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS14 ∷ []) ⟫ʷ
wp0102 c4 L = pw3 c4 L (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) tt tt Eq.refl

wp0103 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ034 ∷ []) ⟫ʷ
wp0103 c4 L = pw2 c4 L (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0104 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ034 ∷ []) ⟫ʷ
wp0104 c4 L = pw1 c4 L (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0105 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ []) ⟫ʷ
wp0105 c4 L = pw3 c4 L (CCZ024 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0106 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0106 c4 L = pw2 c4 L (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0107 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0107 c4 L = pw1 c4 L (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0108 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ034 ∷ []) ⟫ʷ
wp0108 c4 L = pw1 c4 L (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0109 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ024 ∷ []) ⟫ʷ
wp0109 c4 L = pw1 c4 L (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0110 : Base 4 → WsL → ⟪ (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wp0110 c4 L = pw1 c4 L (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wp0111 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0111 c4 L = pw1 c4 L (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0112 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0112 c4 L = pw1 c4 L (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0113 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) ⟫ʷ
wp0113 c4 L = pw1 c4 L (CCZ034 ∷ CZ34 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) tt tt Eq.refl

wp0114 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) ⟫ʷ
wp0114 c4 L = pw1 c4 L (CCZ034 ∷ []) (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0115 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) ⟫ʷ
wp0115 c4 L = pw1 c4 L (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl

wp0116 : Base 4 → WsL → ⟪ (CCZ012 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0116 c4 L = pw3 c4 L (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0117 : Base 4 → WsL → ⟪ (CCZ012 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ012 ∷ []) ⟫ʷ
wp0117 c4 L = pw3 c4 L (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0118 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) ⟫ʷ
wp0118 c4 L = pw1 c4 L (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0119 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ []) ⟫ʷ
wp0119 c4 L = pw1 c4 L (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl

wp0120 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0120 c4 L = pw2 c4 L (CCZ034 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0121 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ034 ∷ []) ⟫ʷ
wp0121 c4 L = pw2 c4 L (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (CX13 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0122 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) ⟫ʷ
wp0122 c4 L = pw3 c4 L (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0123 : Base 4 → WsL → ⟪ (CCZ034 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0123 c4 L = pw2 c4 L (CCZ034 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0124 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ
wp0124 c4 L = pw2 c4 L (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0125 : Base 4 → WsL → ⟪ (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wp0125 c4 L = pw2 c4 L (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wp0126 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ034 ∷ []) ⟫ʷ
wp0126 c4 L = pw1 c4 L (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0127 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ034 ∷ []) ⟫ʷ
wp0127 c4 L = pw2 c4 L (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0128 : Base 4 → WsL → ⟪ (CS24 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS24 ∷ []) ⟫ʷ
wp0128 c4 L = pw3 c4 L (CS24 ∷ Toff012 ∷ []) (Toff012 ∷ CS24 ∷ []) tt tt Eq.refl

wp0129 : Base 4 → WsL → ⟪ (CCZ034 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ034 ∷ []) ⟫ʷ
wp0129 c4 L = pw1 c4 L (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0130 : Base 4 → WsL → ⟪ (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0130 c4 L = pw3 c4 L (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0131 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0131 c4 L = pw1 c4 L (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0132 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0132 c4 L = pw1 c4 L (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0133 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) ⟫ʷ
wp0133 c4 L = pw1 c4 L (CCZ024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0134 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) ⟫ʷ
wp0134 c4 L = pw1 c4 L (CCZ024 ∷ []) (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0135 : Base 4 → WsL → ⟪ (CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0135 c4 L = pw1 c4 L (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl

wp0136 : Base 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) ⟫ʷ
wp0136 c4 L = pw3 c4 L (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) tt tt Eq.refl

wp0137 : Base 4 → WsL → ⟪ (CX41 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX41 ∷ []) ⟫ʷ
wp0137 c4 L = pw2 c4 L (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ []) tt tt Eq.refl

wp0138 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ012 ∷ []) ⟫ʷ
wp0138 c4 L = pw3 c4 L (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (CX41 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0139 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) ⟫ʷ
wp0139 c4 L = pw1 c4 L (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0140 : Base 4 → WsL → ⟪ (CCZ012 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0140 c4 L = pw3 c4 L (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0141 : Base 4 → WsL → ⟪ (CCZ012 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ012 ∷ []) ⟫ʷ
wp0141 c4 L = pw3 c4 L (CCZ012 ∷ CS24 ∷ []) (CS24 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0142 : Base 4 → WsL → ⟪ (CCZ012 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0142 c4 L = pw3 c4 L (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0143 : Base 4 → WsL → ⟪ (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp0143 c4 L = pw3 c4 L (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp0144 : Base 4 → WsL → ⟪ (CX14 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX14 ∷ Toff013 ∷ []) ⟫ʷ
wp0144 c4 L = pw2 c4 L (CX14 ∷ Toff034 ∷ []) (Toff034 ∷ CX14 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0145 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0145 c4 L = pw3 c4 L (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0146 : Base 4 → WsL → ⟪ (CS23 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS23 ∷ []) ⟫ʷ
wp0146 c4 L = pw1 c4 L (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ []) tt tt Eq.refl

wp0147 : Base 4 → WsL → ⟪ (CX31 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX31 ∷ []) ⟫ʷ
wp0147 c4 L = pw2 c4 L (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ []) tt tt Eq.refl

wp0148 : Base 4 → WsL → ⟪ (CX14 ∷ Toff013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0148 c4 L = pw2 c4 L (CX14 ∷ Toff013 ∷ Toff013 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0149 : Base 4 → WsL → ⟪ (CCZ013 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ034 ∷ []) ⟫ʷ
wp0149 c4 L = pw2 c4 L (CCZ013 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0150 : Base 4 → WsL → ⟪ (Sw14 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw14 ∷ []) ⟫ʷ
wp0150 c4 L = pw2 c4 L (Sw14 ∷ Toff034 ∷ []) (Toff013 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0151 : Base 4 → WsL → ⟪ (CCZ034 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ013 ∷ []) ⟫ʷ
wp0151 c4 L = pw2 c4 L (CCZ034 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0152 : Base 4 → WsL → ⟪ (Sw14 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw14 ∷ []) ⟫ʷ
wp0152 c4 L = pw2 c4 L (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0153 : Base 4 → WsL → ⟪ (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0153 c4 L = pw3 c4 L (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0154 : Base 4 → WsL → ⟪ (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0154 c4 L = pw2 c4 L (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0155 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ014 ∷ []) ⟫ʷ
wp0155 c4 L = pw3 c4 L (CCZ014 ∷ CS02 ∷ []) (CS02 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0156 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0156 c4 L = pw2 c4 L (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0157 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ014 ∷ []) ⟫ʷ
wp0157 c4 L = pw2 c4 L (CCZ014 ∷ CS03 ∷ []) (CS03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0158 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0158 c4 L = pw2 c4 L (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0159 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) ⟫ʷ
wp0159 c4 L = pw2 c4 L (CCZ014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0160 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) ⟫ʷ
wp0160 c4 L = pw2 c4 L (CCZ014 ∷ []) (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0161 : Base 4 → WsL → ⟪ (CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0161 c4 L = pw2 c4 L (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl

wp0162 : Base 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) ⟫ʷ
wp0162 c4 L = pw3 c4 L (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0163 : Base 4 → WsL → ⟪ (CX42 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX42 ∷ []) ⟫ʷ
wp0163 c4 L = pw1 c4 L (CX42 ∷ Toff034 ∷ []) (Toff034 ∷ CX42 ∷ []) tt tt Eq.refl

wp0164 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ012 ∷ []) ⟫ʷ
wp0164 c4 L = pw3 c4 L (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (CX42 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0165 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp0165 c4 L = pw2 c4 L (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp0166 : Base 4 → WsL → ⟪ (CCZ012 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp0166 c4 L = pw3 c4 L (CCZ012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0167 : Base 4 → WsL → ⟪ (CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp0167 c4 L = pw3 c4 L (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0168 : Base 4 → WsL → ⟪ (CX42 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp0168 c4 L = pw3 c4 L (CX42 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp0169 : Base 4 → WsL → ⟪ (CX24 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX24 ∷ Toff023 ∷ []) ⟫ʷ
wp0169 c4 L = pw1 c4 L (CX24 ∷ Toff034 ∷ []) (Toff034 ∷ CX24 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0170 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ012 ∷ []) ⟫ʷ
wp0170 c4 L = pw3 c4 L (CCZ012 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0171 : Base 4 → WsL → ⟪ (CS13 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS13 ∷ []) ⟫ʷ
wp0171 c4 L = pw2 c4 L (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ []) tt tt Eq.refl

wp0172 : Base 4 → WsL → ⟪ (CX32 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX32 ∷ []) ⟫ʷ
wp0172 c4 L = pw1 c4 L (CX32 ∷ Toff034 ∷ []) (Toff034 ∷ CX32 ∷ []) tt tt Eq.refl

wp0173 : Base 4 → WsL → ⟪ (Toff023 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff023 ∷ []) ⟫ʷ
wp0173 c4 L = pw1 c4 L (Toff023 ∷ Toff034 ∷ []) (Toff034 ∷ Toff023 ∷ []) tt tt Eq.refl

wp0174 : Base 4 → WsL → ⟪ (CX24 ∷ Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp0174 c4 L = pw1 c4 L (CX24 ∷ Toff023 ∷ Toff023 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp0175 : Base 4 → WsL → ⟪ (CCZ023 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ034 ∷ []) ⟫ʷ
wp0175 c4 L = pw1 c4 L (CCZ023 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0176 : Base 4 → WsL → ⟪ (Sw24 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw24 ∷ []) ⟫ʷ
wp0176 c4 L = pw1 c4 L (Sw24 ∷ Toff034 ∷ []) (Toff023 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0177 : Base 4 → WsL → ⟪ (CCZ034 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ CCZ023 ∷ []) ⟫ʷ
wp0177 c4 L = pw1 c4 L (CCZ034 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0178 : Base 4 → WsL → ⟪ (Sw24 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw24 ∷ []) ⟫ʷ
wp0178 c4 L = pw1 c4 L (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) tt tt Eq.refl

wp0179 : Base 4 → WsL → ⟪ (CCZ024 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp0179 c4 L = pw3 c4 L (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0180 : Base 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) ⟫ʷ
wp0180 c4 L = pw2 c4 L (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0181 : Base 4 → WsL → ⟪ (CX41 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX41 ∷ []) ⟫ʷ
wp0181 c4 L = pw3 c4 L (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ []) tt tt Eq.refl

wp0182 : Base 4 → WsL → ⟪ (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ CCZ013 ∷ []) ⟫ʷ
wp0182 c4 L = pw2 c4 L (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (CX41 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0183 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) ⟫ʷ
wp0183 c4 L = pw1 c4 L (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0184 : Base 4 → WsL → ⟪ (CCZ013 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS34⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wp0184 c4 L = pw2 c4 L (CCZ013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0185 : Base 4 → WsL → ⟪ (CCZ013 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CCZ013 ∷ []) ⟫ʷ
wp0185 c4 L = pw2 c4 L (CCZ013 ∷ CS34 ∷ []) (CS34 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0186 : Base 4 → WsL → ⟪ (CCZ013 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ013 ∷ []) ⟫ʷ
wp0186 c4 L = pw2 c4 L (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0187 : Base 4 → WsL → ⟪ (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp0187 c4 L = pw2 c4 L (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp0188 : Base 4 → WsL → ⟪ (CX14 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX14 ∷ Toff012 ∷ []) ⟫ʷ
wp0188 c4 L = pw3 c4 L (CX14 ∷ Toff024 ∷ []) (Toff024 ∷ CX14 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0189 : Base 4 → WsL → ⟪ (CCZ013 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ013 ∷ []) ⟫ʷ
wp0189 c4 L = pw2 c4 L (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0190 : Base 4 → WsL → ⟪ (CS23 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS23 ∷ []) ⟫ʷ
wp0190 c4 L = pw1 c4 L (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl

wp0191 : Base 4 → WsL → ⟪ (CX21 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX21 ∷ []) ⟫ʷ
wp0191 c4 L = pw3 c4 L (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ []) tt tt Eq.refl

wp0192 : Base 4 → WsL → ⟪ (Toff012 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff012 ∷ []) ⟫ʷ
wp0192 c4 L = pw3 c4 L (Toff012 ∷ Toff024 ∷ []) (Toff024 ∷ Toff012 ∷ []) tt tt Eq.refl

wp0193 : Base 4 → WsL → ⟪ (CX14 ∷ Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp0193 c4 L = pw3 c4 L (CX14 ∷ Toff012 ∷ Toff012 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp0194 : Base 4 → WsL → ⟪ (CCZ012 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ024 ∷ []) ⟫ʷ
wp0194 c4 L = pw3 c4 L (CCZ012 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0195 : Base 4 → WsL → ⟪ (Sw14 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw14 ∷ []) ⟫ʷ
wp0195 c4 L = pw3 c4 L (Sw14 ∷ Toff024 ∷ []) (Toff012 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0196 : Base 4 → WsL → ⟪ (CCZ024 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ012 ∷ []) ⟫ʷ
wp0196 c4 L = pw3 c4 L (CCZ024 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0197 : Base 4 → WsL → ⟪ (Sw14 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw14 ∷ []) ⟫ʷ
wp0197 c4 L = pw3 c4 L (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) tt tt Eq.refl

wp0198 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) ⟫ʷ
wp0198 c4 L = pw1 c4 L (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) tt tt Eq.refl

wp0199 : Base 4 → WsL → ⟪ (CCZ023 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ
wp0199 c4 L = pw1 c4 L (CCZ023 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0200 : Base 4 → WsL → ⟪ (CX13 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX13 ∷ Toff014 ∷ []) ⟫ʷ
wp0200 c4 L = pw2 c4 L (CX13 ∷ Toff034 ∷ []) (Toff034 ∷ CX13 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0201 : Base 4 → WsL → ⟪ (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ012 ∷ []) ⟫ʷ
wp0201 c4 L = pw3 c4 L (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0202 : Base 4 → WsL → ⟪ (CS24 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS24 ∷ []) ⟫ʷ
wp0202 c4 L = pw1 c4 L (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl

wp0203 : Base 4 → WsL → ⟪ (Toff014 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff014 ∷ []) ⟫ʷ
wp0203 c4 L = pw2 c4 L (Toff014 ∷ Toff034 ∷ []) (Toff034 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0204 : Base 4 → WsL → ⟪ (CX13 ∷ Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wp0204 c4 L = pw2 c4 L (CX13 ∷ Toff014 ∷ Toff014 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wp0205 : Base 4 → WsL → ⟪ (CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ
wp0205 c4 L = pw3 c4 L (CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0206 : Base 4 → WsL → ⟪ (CCZ014 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ034 ∷ []) ⟫ʷ
wp0206 c4 L = pw2 c4 L (CCZ014 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0207 : Base 4 → WsL → ⟪ (Sw13 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw13 ∷ []) ⟫ʷ
wp0207 c4 L = pw2 c4 L (Sw13 ∷ Toff034 ∷ []) (Toff014 ∷ Sw13 ∷ []) tt tt Eq.refl

wp0208 : Base 4 → WsL → ⟪ (CCZ034 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ CCZ014 ∷ []) ⟫ʷ
wp0208 c4 L = pw2 c4 L (CCZ034 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0209 : Base 4 → WsL → ⟪ (Sw13 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw13 ∷ []) ⟫ʷ
wp0209 c4 L = pw2 c4 L (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ []) tt tt Eq.refl

wp0210 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ []) ⟫ʷ
wp0210 c4 L = pw2 c4 L (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl

wp0211 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) ⟫ʷ
wp0211 c4 L = pw1 c4 L (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) tt tt Eq.refl

wp0212 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0212 c4 L = pw3 c4 L (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0213 : Base 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) ⟫ʷ
wp0213 c4 L = pw1 c4 L (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) tt tt Eq.refl

wp0214 : Base 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) ⟫ʷ
wp0214 c4 L = pw2 c4 L (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) tt tt Eq.refl

wp0215 : Base 4 → WsL → ⟪ (CCZ014 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ014 ∷ []) ⟫ʷ
wp0215 c4 L = pw3 c4 L (CCZ014 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0216 : Base 4 → WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) ⟫ʷ
wp0216 c4 L = pw1 c4 L (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0217 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) ⟫ʷ
wp0217 c4 L = pw2 c4 L (CCZ014 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) tt tt Eq.refl

wp0218 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) ⟫ʷ
wp0218 c4 L = pw3 c4 L (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) tt tt Eq.refl

wp0219 : Base 4 → WsL → ⟪ (K0 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K0 ∷ []) ⟫ʷ
wp0219 c4 L = pw1 c4 L (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl

wp0220 : Base 4 → WsL → ⟪ (K0⁻ ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ K0⁻ ∷ []) ⟫ʷ
wp0220 c4 L = pw1 c4 L (K0⁻ ∷ CCZ034 ∷ []) (Toff034 ∷ K0⁻ ∷ []) tt tt Eq.refl

wp0221 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0221 c4 L = pw2 c4 L (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0222 : Base 4 → WsL → ⟪ (CCZ034 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CCZ034 ∷ []) ⟫ʷ
wp0222 c4 L = pw1 c4 L (CCZ034 ∷ S0 ∷ []) (S0 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0223 : Base 4 → WsL → ⟪ (CCZ034 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0223 c4 L = pw1 c4 L (CCZ034 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0224 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ034 ∷ []) ⟫ʷ
wp0224 c4 L = pw2 c4 L (CCZ034 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0225 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ034 ∷ []) ⟫ʷ
wp0225 c4 L = pw2 c4 L (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0226 : Base 4 → WsL → ⟪ (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wp0226 c4 L = pw2 c4 L (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wp0227 : Base 4 → WsL → ⟪ (CCZ034 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ034 ∷ []) ⟫ʷ
wp0227 c4 L = pw1 c4 L (CCZ034 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0228 : Base 4 → WsL → ⟪ (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ034 ∷ []) ⟫ʷ
wp0228 c4 L = pw1 c4 L (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (CX20 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0229 : Base 4 → WsL → ⟪ (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wp0229 c4 L = pw1 c4 L (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ []) tt tt Eq.refl

wp0230 : Base 4 → WsL → ⟪ (CS03 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0230 c4 L = pw1 c4 L (CS03 ∷ Toff034 ∷ []) (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0231 : Base 4 → WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) ⟫ʷ
wp0231 c4 L = pw1 c4 L (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) tt tt Eq.refl

wp0232 : Base 4 → WsL → ⟪ (CCZ034 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0232 c4 L = pw1 c4 L (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0233 : Base 4 → WsL → ⟪ (CS34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS34 ∷ []) ⟫ʷ
wp0233 c4 L = pw1 c4 L (CS34 ∷ Toff034 ∷ []) (Toff034 ∷ CS34 ∷ []) tt tt Eq.refl

wp0234 : Base 4 → WsL → ⟪ (CS03 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
wp0234 c4 L = pw1 c4 L (CS03 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS03 ∷ []) tt tt Eq.refl

wp0235 : Base 4 → WsL → ⟪ (CS03⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0235 c4 L = pw1 c4 L (CS03⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0236 : Base 4 → WsL → ⟪ (CS34⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0236 c4 L = pw1 c4 L (CS34⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0237 : Base 4 → WsL → ⟪ (CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
wp0237 c4 L = pw1 c4 L (CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl

wp0238 : Base 4 → WsL → ⟪ (CZ03 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) ⟫ʷ
wp0238 c4 L = pw1 c4 L (CZ03 ∷ Toff034 ∷ []) (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0239 : Base 4 → WsL → ⟪ (CZ34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ34 ∷ []) ⟫ʷ
wp0239 c4 L = pw1 c4 L (CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0240 : Base 4 → WsL → ⟪ (CZ03 ∷ CZ34 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
wp0240 c4 L = pw1 c4 L (CZ03 ∷ CZ34 ∷ CZ34 ∷ []) (CZ03 ∷ []) tt tt Eq.refl

wp0241 : Base 4 → WsL → ⟪ (CS23⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS23⁻ ∷ []) ⟫ʷ
wp0241 c4 L = pw1 c4 L (CS23⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wp0242 : Base 4 → WsL → ⟪ (CX30 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX30 ∷ []) ⟫ʷ
wp0242 c4 L = pw1 c4 L (CX30 ∷ Toff034 ∷ []) (Toff034 ∷ CX30 ∷ []) tt tt Eq.refl

wp0243 : Base 4 → WsL → ⟪ (CS04 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) ⟫ʷ
wp0243 c4 L = pw1 c4 L (CS04 ∷ Toff034 ∷ []) (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0244 : Base 4 → WsL → ⟪ (CS04 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
wp0244 c4 L = pw1 c4 L (CS04 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS04 ∷ []) tt tt Eq.refl

wp0245 : Base 4 → WsL → ⟪ (CS04⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) ⟫ʷ
wp0245 c4 L = pw1 c4 L (CS04⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0246 : Base 4 → WsL → ⟪ (CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ []) ⟫ʷ
wp0246 c4 L = pw1 c4 L (CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl

wp0247 : Base 4 → WsL → ⟪ (CCZ012 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ CCZ012 ∷ []) ⟫ʷ
wp0247 c4 L = pw3 c4 L (CCZ012 ∷ CZ04 ∷ []) (CZ04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0248 : Base 4 → WsL → ⟪ (CZ04 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) ⟫ʷ
wp0248 c4 L = pw1 c4 L (CZ04 ∷ Toff034 ∷ []) (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) tt tt Eq.refl

wp0249 : Base 4 → WsL → ⟪ (CZ04 ∷ CZ34 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ []) ⟫ʷ
wp0249 c4 L = pw1 c4 L (CZ04 ∷ CZ34 ∷ CZ34 ∷ []) (CZ04 ∷ []) tt tt Eq.refl

wp0250 : Base 4 → WsL → ⟪ (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ012 ∷ []) ⟫ʷ
wp0250 c4 L = pw3 c4 L (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (CX40 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0251 : Base 4 → WsL → ⟪ (CS14 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS14 ∷ []) ⟫ʷ
wp0251 c4 L = pw2 c4 L (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl

wp0252 : Base 4 → WsL → ⟪ (CS24⁻ ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0252 c4 L = pw1 c4 L (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0253 : Base 4 → WsL → ⟪ (CX40 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX40 ∷ []) ⟫ʷ
wp0253 c4 L = pw1 c4 L (CX40 ∷ Toff034 ∷ []) (Toff034 ∷ CX40 ∷ []) tt tt Eq.refl

wp0254 : Base 4 → WsL → ⟪ (CX40 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ []) ⟫ʷ
wp0254 c4 L = pw3 c4 L (CX40 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX40 ∷ []) tt tt Eq.refl

wp0255 : Base 4 → WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) ⟫ʷ
wp0255 c4 L = pw1 c4 L (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp0256 : Base 4 → WsL → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) ⟫ʷ
wp0256 c4 L = pw1 c4 L (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl

wp0257 : Base 4 → WsL → ⟪ (S0 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
wp0257 c4 L = pw1 c4 L (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl

wp0258 : Base 4 → WsL → ⟪ (S0⁻ ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ
wp0258 c4 L = pw1 c4 L (S0⁻ ∷ CS04 ∷ []) (X4 ∷ CS04⁻ ∷ X4 ∷ []) tt tt Eq.refl

wp0259 : Base 4 → WsL → ⟪ (K0 ∷ CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
wp0259 c4 L = pw1 c4 L (K0 ∷ CK40⁻ ∷ []) (X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl
