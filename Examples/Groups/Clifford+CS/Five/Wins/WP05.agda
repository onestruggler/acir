------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP05 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0919 : Complete 4 → WsL → ⟪ (CCZ124 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ124 ∷ []) ⟫ʷ
wp0919 c4 L = pw3 c4 L (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0920 : Complete 4 → WsL → ⟪ (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ023 ∷ []) ⟫ʷ
wp0920 c4 L = pw1 c4 L (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (CX43 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0921 : Complete 4 → WsL → ⟪ (CCZ024 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ024 ∷ CCZ014 ∷ []) ⟫ʷ
wp0921 c4 L = pw3 c4 L (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0922 : Complete 4 → WsL → ⟪ (CX43 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wp0922 c4 L = pw1 c4 L (CX43 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wp0923 : Complete 4 → WsL → ⟪ (CS01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS01 ∷ []) ⟫ʷ
wp0923 c4 L = pw3 c4 L (CS01 ∷ Toff214 ∷ []) (Toff214 ∷ CS01 ∷ []) tt tt Eq.refl

wp0924 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp0924 c4 L = pw2 c4 L (CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp0925 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK40 ∷ []) ⟫ʷ
wp0925 c4 L = pw2 c4 L (CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK40 ∷ []) tt tt Eq.refl

wp0926 : Complete 4 → WsL → ⟪ (CCZ024 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0926 c4 L = pw1 c4 L (CCZ024 ∷ K0 ∷ []) (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0927 : Complete 4 → WsL → ⟪ (CCZ024 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ
wp0927 c4 L = pw3 c4 L (CCZ024 ∷ CK40 ∷ []) (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0928 : Complete 4 → WsL → ⟪ (K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ []) ⟫ʷ
wp0928 c4 L = pw3 c4 L (K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ []) tt tt Eq.refl

wp0929 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CK40 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0929 c4 L = pw2 c4 L (CCZ013 ∷ CK40 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0930 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS04 ∷ CCZ013 ∷ []) ⟫ʷ
wp0930 c4 L = pw2 c4 L (CCZ013 ∷ CS04 ∷ CS04 ∷ []) (CS04 ∷ CS04 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0931 : Complete 4 → WsL → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ []) ⟫ʷ
wp0931 c4 L = pw1 c4 L (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ []) tt tt Eq.refl

wp0932 : Complete 4 → WsL → ⟪ (CX40 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
wp0932 c4 L = pw2 c4 L (CX40 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0933 : Complete 4 → WsL → ⟪ (CCZ014 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ
wp0933 c4 L = pw2 c4 L (CCZ014 ∷ K1 ∷ []) (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0934 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) ⟫ʷ
wp0934 c4 L = pw2 c4 L (CCZ014 ∷ CK41 ∷ []) (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0935 : Complete 4 → WsL → ⟪ (K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ []) ⟫ʷ
wp0935 c4 L = pw2 c4 L (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ []) tt tt Eq.refl

wp0936 : Complete 4 → WsL → ⟪ (CCZ024 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ
wp0936 c4 L = pw1 c4 L (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0937 : Complete 4 → WsL → ⟪ (CCZ024 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) ⟫ʷ
wp0937 c4 L = pw1 c4 L (CCZ024 ∷ CK42 ∷ []) (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0938 : Complete 4 → WsL → ⟪ (K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ []) ⟫ʷ
wp0938 c4 L = pw1 c4 L (K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ []) tt tt Eq.refl

wp0939 : Complete 4 → WsL → ⟪ (CX34 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX34 ∷ []) ⟫ʷ
wp0939 c4 L = pw1 c4 L (CX34 ∷ Toff203 ∷ []) (Toff203 ∷ CX34 ∷ []) tt tt Eq.refl

wp0940 : Complete 4 → WsL → ⟪ (CX43 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX43 ∷ Toff204 ∷ []) ⟫ʷ
wp0940 c4 L = pw1 c4 L (CX43 ∷ Toff203 ∷ []) (Toff203 ∷ CX43 ∷ Toff204 ∷ []) tt tt Eq.refl

wp0941 : Complete 4 → WsL → ⟪ (CCZ124 ∷ Toff204 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ124 ∷ []) ⟫ʷ
wp0941 c4 L = pw3 c4 L (CCZ124 ∷ Toff204 ∷ CCZ014 ∷ []) (Toff204 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp0942 : Complete 4 → WsL → ⟪ (CX04 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX04 ∷ []) ⟫ʷ
wp0942 c4 L = pw1 c4 L (CX04 ∷ Toff203 ∷ []) (Toff203 ∷ CX04 ∷ []) tt tt Eq.refl

wp0943 : Complete 4 → WsL → ⟪ (Toff203 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff203 ∷ []) ⟫ʷ
wp0943 c4 L = pw1 c4 L (Toff203 ∷ Toff204 ∷ []) (Toff204 ∷ Toff203 ∷ []) tt tt Eq.refl

wp0944 : Complete 4 → WsL → ⟪ (CX43 ∷ Toff204 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wp0944 c4 L = pw1 c4 L (CX43 ∷ Toff204 ∷ Toff204 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wp0945 : Complete 4 → WsL → ⟪ (CX43 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX43 ∷ []) ⟫ʷ
wp0945 c4 L = pw1 c4 L (CX43 ∷ Toff204 ∷ []) (Toff204 ∷ CX43 ∷ []) tt tt Eq.refl

wp0946 : Complete 4 → WsL → ⟪ (CCZ124 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ
wp0946 c4 L = pw3 c4 L (CCZ124 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0947 : Complete 4 → WsL → ⟪ (CX34 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX34 ∷ Toff203 ∷ []) ⟫ʷ
wp0947 c4 L = pw1 c4 L (CX34 ∷ Toff204 ∷ []) (Toff204 ∷ CX34 ∷ Toff203 ∷ []) tt tt Eq.refl

wp0948 : Complete 4 → WsL → ⟪ (CS01 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS01 ∷ []) ⟫ʷ
wp0948 c4 L = pw3 c4 L (CS01 ∷ Toff204 ∷ []) (Toff204 ∷ CS01 ∷ []) tt tt Eq.refl

wp0949 : Complete 4 → WsL → ⟪ (CX03 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX03 ∷ []) ⟫ʷ
wp0949 c4 L = pw1 c4 L (CX03 ∷ Toff204 ∷ []) (Toff204 ∷ CX03 ∷ []) tt tt Eq.refl

wp0950 : Complete 4 → WsL → ⟪ (CX34 ∷ Toff203 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0950 c4 L = pw1 c4 L (CX34 ∷ Toff203 ∷ Toff203 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0951 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK41 ∷ []) ⟫ʷ
wp0951 c4 L = pw2 c4 L (CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK41 ∷ []) tt tt Eq.refl

wp0952 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CK41 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ []) ⟫ʷ
wp0952 c4 L = pw2 c4 L (CCZ013 ∷ CK41 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0953 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS14 ∷ CCZ013 ∷ []) ⟫ʷ
wp0953 c4 L = pw2 c4 L (CCZ013 ∷ CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0954 : Complete 4 → WsL → ⟪ (CX41 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
wp0954 c4 L = pw2 c4 L (CX41 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0955 : Complete 4 → WsL → ⟪ (CX43 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX43 ∷ Toff014 ∷ []) ⟫ʷ
wp0955 c4 L = pw2 c4 L (CX43 ∷ Toff013 ∷ []) (Toff013 ∷ CX43 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0956 : Complete 4 → WsL → ⟪ (CX43 ∷ Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wp0956 c4 L = pw2 c4 L (CX43 ∷ Toff014 ∷ Toff014 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wp0957 : Complete 4 → WsL → ⟪ (Sw34 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw34 ∷ []) ⟫ʷ
wp0957 c4 L = pw2 c4 L (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0958 : Complete 4 → WsL → ⟪ (CCZ013 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ014 ∷ []) ⟫ʷ
wp0958 c4 L = pw2 c4 L (CCZ013 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0959 : Complete 4 → WsL → ⟪ (Sw34 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw34 ∷ []) ⟫ʷ
wp0959 c4 L = pw2 c4 L (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0960 : Complete 4 → WsL → ⟪ (CX43 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX43 ∷ []) ⟫ʷ
wp0960 c4 L = pw2 c4 L (CX43 ∷ Toff014 ∷ []) (Toff014 ∷ CX43 ∷ []) tt tt Eq.refl

wp0961 : Complete 4 → WsL → ⟪ (CX34 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX34 ∷ Toff013 ∷ []) ⟫ʷ
wp0961 c4 L = pw2 c4 L (CX34 ∷ Toff014 ∷ []) (Toff014 ∷ CX34 ∷ Toff013 ∷ []) tt tt Eq.refl

wp0962 : Complete 4 → WsL → ⟪ (CS12 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS12 ∷ []) ⟫ʷ
wp0962 c4 L = pw3 c4 L (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) tt tt Eq.refl

wp0963 : Complete 4 → WsL → ⟪ (CX13 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX13 ∷ []) ⟫ʷ
wp0963 c4 L = pw2 c4 L (CX13 ∷ Toff014 ∷ []) (Toff014 ∷ CX13 ∷ []) tt tt Eq.refl

wp0964 : Complete 4 → WsL → ⟪ (CX34 ∷ Toff013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wp0964 c4 L = pw2 c4 L (CX34 ∷ Toff013 ∷ Toff013 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wp0965 : Complete 4 → WsL → ⟪ (Sw34 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw34 ∷ []) ⟫ʷ
wp0965 c4 L = pw2 c4 L (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0966 : Complete 4 → WsL → ⟪ (Sw34 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw34 ∷ []) ⟫ʷ
wp0966 c4 L = pw2 c4 L (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ []) tt tt Eq.refl

wp0967 : Complete 4 → WsL → ⟪ (CCZ023 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ023 ∷ CCZ234 ∷ []) ⟫ʷ
wp0967 c4 L = pw1 c4 L (CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ023 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp0968 : Complete 4 → WsL → ⟪ (CX12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX12 ∷ Toff014 ∷ []) ⟫ʷ
wp0968 c4 L = pw3 c4 L (CX12 ∷ Toff024 ∷ []) (Toff024 ∷ CX12 ∷ Toff014 ∷ []) tt tt Eq.refl

wp0969 : Complete 4 → WsL → ⟪ (CCZ013 ∷ Toff014 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ013 ∷ []) ⟫ʷ
wp0969 c4 L = pw2 c4 L (CCZ013 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0970 : Complete 4 → WsL → ⟪ (CS34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS34 ∷ []) ⟫ʷ
wp0970 c4 L = pw1 c4 L (CS34 ∷ Toff024 ∷ []) (Toff024 ∷ CS34 ∷ []) tt tt Eq.refl

wp0971 : Complete 4 → WsL → ⟪ (CX12 ∷ Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wp0971 c4 L = pw3 c4 L (CX12 ∷ Toff014 ∷ Toff014 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wp0972 : Complete 4 → WsL → ⟪ (Sw12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw12 ∷ []) ⟫ʷ
wp0972 c4 L = pw3 c4 L (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) tt tt Eq.refl

wp0973 : Complete 4 → WsL → ⟪ (Sw12 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw12 ∷ []) ⟫ʷ
wp0973 c4 L = pw3 c4 L (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) tt tt Eq.refl

wp0974 : Complete 4 → WsL → ⟪ (CX14 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX14 ∷ []) ⟫ʷ
wp0974 c4 L = pw3 c4 L (CX14 ∷ Toff012 ∷ []) (Toff012 ∷ CX14 ∷ []) tt tt Eq.refl

wp0975 : Complete 4 → WsL → ⟪ (CX41 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX41 ∷ Toff024 ∷ []) ⟫ʷ
wp0975 c4 L = pw3 c4 L (CX41 ∷ Toff012 ∷ []) (Toff012 ∷ CX41 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0976 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff024 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ034 ∷ []) ⟫ʷ
wp0976 c4 L = pw1 c4 L (CCZ034 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0977 : Complete 4 → WsL → ⟪ (CX24 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX24 ∷ []) ⟫ʷ
wp0977 c4 L = pw3 c4 L (CX24 ∷ Toff012 ∷ []) (Toff012 ∷ CX24 ∷ []) tt tt Eq.refl

wp0978 : Complete 4 → WsL → ⟪ (CX41 ∷ Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp0978 c4 L = pw3 c4 L (CX41 ∷ Toff024 ∷ Toff024 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp0979 : Complete 4 → WsL → ⟪ (CCZ034 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ
wp0979 c4 L = pw1 c4 L (CCZ034 ∷ K3 ∷ []) (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0980 : Complete 4 → WsL → ⟪ (CCZ034 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) ⟫ʷ
wp0980 c4 L = pw1 c4 L (CCZ034 ∷ CK43 ∷ []) (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0981 : Complete 4 → WsL → ⟪ (CCZ034 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ034 ∷ []) ⟫ʷ
wp0981 c4 L = pw1 c4 L (CCZ034 ∷ S4 ∷ []) (S4 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp0982 : Complete 4 → WsL → ⟪ (K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ []) ⟫ʷ
wp0982 c4 L = pw1 c4 L (K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ []) tt tt Eq.refl

wp0983 : Complete 4 → WsL → ⟪ (CX23 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX23 ∷ Toff024 ∷ []) ⟫ʷ
wp0983 c4 L = pw1 c4 L (CX23 ∷ Toff034 ∷ []) (Toff034 ∷ CX23 ∷ Toff024 ∷ []) tt tt Eq.refl

wp0984 : Complete 4 → WsL → ⟪ (CCZ012 ∷ Toff024 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0984 c4 L = pw3 c4 L (CCZ012 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0985 : Complete 4 → WsL → ⟪ (CX23 ∷ Toff024 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wp0985 c4 L = pw1 c4 L (CX23 ∷ Toff024 ∷ Toff024 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wp0986 : Complete 4 → WsL → ⟪ (Sw23 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw23 ∷ []) ⟫ʷ
wp0986 c4 L = pw1 c4 L (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0987 : Complete 4 → WsL → ⟪ (Sw23 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw23 ∷ []) ⟫ʷ
wp0987 c4 L = pw1 c4 L (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) tt tt Eq.refl

wp0988 : Complete 4 → WsL → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) ⟫ʷ
wp0988 c4 L = pw2 c4 L (CCZ013 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0989 : Complete 4 → WsL → ⟪ (CCZ023 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ023 ∷ CCZ024 ∷ []) ⟫ʷ
wp0989 c4 L = pw1 c4 L (CCZ023 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ023 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0990 : Complete 4 → WsL → ⟪ (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ013 ∷ []) ⟫ʷ
wp0990 c4 L = pw2 c4 L (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp0991 : Complete 4 → WsL → ⟪ (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp0991 c4 L = pw3 c4 L (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp0992 : Complete 4 → WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) ⟫ʷ
wp0992 c4 L = pw1 c4 L (CCZ023 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) tt tt Eq.refl

wp0993 : Complete 4 → WsL → ⟪ (CCZ023 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) ⟫ʷ
wp0993 c4 L = pw1 c4 L (CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0994 : Complete 4 → WsL → ⟪ (CCZ234 ∷ CCZ023 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ023 ∷ []) ⟫ʷ
wp0994 c4 L = pw1 c4 L (CCZ234 ∷ CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp0995 : Complete 4 → WsL → ⟪ (CS14⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS14⁻ ∷ []) ⟫ʷ
wp0995 c4 L = pw3 c4 L (CS14⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wp0996 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp0996 c4 L = pw3 c4 L (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp0997 : Complete 4 → WsL → ⟪ (CCZ013 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) ⟫ʷ
wp0997 c4 L = pw2 c4 L (CCZ013 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0998 : Complete 4 → WsL → ⟪ (CS04 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS04 ∷ []) ⟫ʷ
wp0998 c4 L = pw2 c4 L (CS04 ∷ Toff314 ∷ []) (Toff314 ∷ CS04 ∷ []) tt tt Eq.refl

wp0999 : Complete 4 → WsL → ⟪ (CX03 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff324 ∷ CX03 ∷ []) ⟫ʷ
wp0999 c4 L = pw1 c4 L (CX03 ∷ Toff024 ∷ []) (Toff024 ∷ Toff324 ∷ CX03 ∷ []) tt tt Eq.refl

wp1000 : Complete 4 → WsL → ⟪ (CCZ124 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ124 ∷ []) ⟫ʷ
wp1000 c4 L = pw3 c4 L (CCZ124 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1001 : Complete 4 → WsL → ⟪ (Toff024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff024 ∷ []) ⟫ʷ
wp1001 c4 L = pw1 c4 L (Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff024 ∷ []) tt tt Eq.refl

wp1002 : Complete 4 → WsL → ⟪ (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp1002 c4 L = pw1 c4 L (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp1003 : Complete 4 → WsL → ⟪ (CCZ134 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ134 ∷ []) ⟫ʷ
wp1003 c4 L = pw2 c4 L (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1004 : Complete 4 → WsL → ⟪ (Toff024 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) ⟫ʷ
wp1004 c4 L = pw1 c4 L (Toff024 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) tt tt Eq.refl

wp1005 : Complete 4 → WsL → ⟪ (CS24⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS24⁻ ∷ []) ⟫ʷ
wp1005 c4 L = pw1 c4 L (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp1006 : Complete 4 → WsL → ⟪ (CS24 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS24 ∷ []) ⟫ʷ
wp1006 c4 L = pw1 c4 L (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) tt tt Eq.refl

wp1007 : Complete 4 → WsL → ⟪ (Toff302 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff302 ∷ []) ⟫ʷ
wp1007 c4 L = pw1 c4 L (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1008 : Complete 4 → WsL → ⟪ (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp1008 c4 L = pw1 c4 L (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp1009 : Complete 4 → WsL → ⟪ (CX03 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX03 ∷ []) ⟫ʷ
wp1009 c4 L = pw1 c4 L (CX03 ∷ Toff324 ∷ []) (Toff324 ∷ CX03 ∷ []) tt tt Eq.refl

wp1010 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ014 ∷ []) ⟫ʷ
wp1010 c4 L = pw2 c4 L (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (CX30 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1011 : Complete 4 → WsL → ⟪ (CX30 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wp1011 c4 L = pw2 c4 L (CX30 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wp1012 : Complete 4 → WsL → ⟪ (CX30 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX30 ∷ Toff024 ∷ []) ⟫ʷ
wp1012 c4 L = pw1 c4 L (CX30 ∷ Toff324 ∷ []) (Toff324 ∷ CX30 ∷ Toff024 ∷ []) tt tt Eq.refl

wp1013 : Complete 4 → WsL → ⟪ (CX30 ∷ Toff024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX30 ∷ []) ⟫ʷ
wp1013 c4 L = pw1 c4 L (CX30 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ CX30 ∷ []) tt tt Eq.refl

wp1014 : Complete 4 → WsL → ⟪ (CCZ134 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CCZ014 ∷ []) ⟫ʷ
wp1014 c4 L = pw2 c4 L (CCZ134 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1015 : Complete 4 → WsL → ⟪ (Sw03 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw03 ∷ []) ⟫ʷ
wp1015 c4 L = pw2 c4 L (Sw03 ∷ Toff014 ∷ []) (Toff314 ∷ Sw03 ∷ []) tt tt Eq.refl

wp1016 : Complete 4 → WsL → ⟪ (Sw03 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw03 ∷ []) ⟫ʷ
wp1016 c4 L = pw1 c4 L (Sw03 ∷ Toff324 ∷ []) (Toff024 ∷ Sw03 ∷ []) tt tt Eq.refl

wp1017 : Complete 4 → WsL → ⟪ (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ034 ∷ []) ⟫ʷ
wp1017 c4 L = pw1 c4 L (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (CX24 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1018 : Complete 4 → WsL → ⟪ (CX24 ∷ CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp1018 c4 L = pw1 c4 L (CX24 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp1019 : Complete 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ012 ∷ CX24 ∷ []) ⟫ʷ
wp1019 c4 L = pw3 c4 L (CCZ012 ∷ []) (CX24 ∷ CCZ012 ∷ CX24 ∷ []) tt tt Eq.refl

wp1020 : Complete 4 → WsL → ⟪ (CCZ034 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ034 ∷ []) ⟫ʷ
wp1020 c4 L = pw1 c4 L (CCZ034 ∷ CX42 ∷ []) (CX42 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1021 : Complete 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ014 ∷ CX42 ∷ []) ⟫ʷ
wp1021 c4 L = pw3 c4 L (CCZ014 ∷ []) (CX42 ∷ CCZ014 ∷ CX42 ∷ []) tt tt Eq.refl

wp1022 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp1022 c4 L = pw3 c4 L (CCZ012 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1023 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ
wp1023 c4 L = pw3 c4 L (CCZ014 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1024 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wp1024 c4 L = pw3 c4 L (CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wp1025 : Complete 4 → WsL → ⟪ (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff024 ∷ []) ⟫ʷ
wp1025 c4 L = pw1 c4 L (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ []) tt tt Eq.refl

wp1026 : Complete 4 → WsL → ⟪ (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp1026 c4 L = pw1 c4 L (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp1027 : Complete 4 → WsL → ⟪ (CCZ134 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ134 ∷ []) ⟫ʷ
wp1027 c4 L = pw2 c4 L (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1028 : Complete 4 → WsL → ⟪ (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ []) ⟫ʷ
wp1028 c4 L = pw1 c4 L (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl

wp1029 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) ⟫ʷ
wp1029 c4 L = pw1 c4 L (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1030 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CS02 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) ⟫ʷ
wp1030 c4 L = pw3 c4 L (CCZ014 ∷ CS02 ∷ Toff214 ∷ []) (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1031 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ
wp1031 c4 L = pw2 c4 L (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1032 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
wp1032 c4 L = pw3 c4 L (CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl

wp1033 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
wp1033 c4 L = pw1 c4 L (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1034 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CZ04 ∷ CCZ034 ∷ []) ⟫ʷ
wp1034 c4 L = pw1 c4 L (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CZ04 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1035 : Complete 4 → WsL → ⟪ (K2 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ K2 ∷ []) ⟫ʷ
wp1035 c4 L = pw1 c4 L (K2 ∷ Toff304 ∷ []) (Toff304 ∷ K2 ∷ []) tt tt Eq.refl

wp1036 : Complete 4 → WsL → ⟪ (CS24⁻ ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS24⁻ ∷ []) ⟫ʷ
wp1036 c4 L = pw1 c4 L (CS24⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp1037 : Complete 4 → WsL → ⟪ (CS14 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS14 ∷ []) ⟫ʷ
wp1037 c4 L = pw2 c4 L (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ []) tt tt Eq.refl

wp1038 : Complete 4 → WsL → ⟪ (K2⁻ ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ K2⁻ ∷ []) ⟫ʷ
wp1038 c4 L = pw1 c4 L (K2⁻ ∷ Toff304 ∷ []) (Toff304 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp1039 : Complete 4 → WsL → ⟪ (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ134 ∷ []) ⟫ʷ
wp1039 c4 L = pw2 c4 L (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1040 : Complete 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) ⟫ʷ
wp1040 c4 L = pw2 c4 L (CCZ014 ∷ []) (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1041 : Complete 4 → WsL → ⟪ (CS04 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS04 ∷ []) ⟫ʷ
wp1041 c4 L = pw1 c4 L (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ []) tt tt Eq.refl

wp1042 : Complete 4 → WsL → ⟪ (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) ⟫ʷ
wp1042 c4 L = pw3 c4 L (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1043 : Complete 4 → WsL → ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1043 c4 L = pw3 c4 L (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1044 : Complete 4 → WsL → ⟪ (CCZ014 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ []) ⟫ʷ
wp1044 c4 L = pw2 c4 L (CCZ014 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1045 : Complete 4 → WsL → ⟪ (CCZ034 ∷ CCZ234 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ034 ∷ []) ⟫ʷ
wp1045 c4 L = pw1 c4 L (CCZ034 ∷ CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1046 : Complete 4 → WsL → ⟪ (CCZ023 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) ⟫ʷ
wp1046 c4 L = pw1 c4 L (CCZ023 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1047 : Complete 4 → WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1047 c4 L = pw3 c4 L (CCZ124 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1048 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp1048 c4 L = pw2 c4 L (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp1049 : Complete 4 → WsL → ⟪ (CX24 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX24 ∷ []) ⟫ʷ
wp1049 c4 L = pw1 c4 L (CX24 ∷ Toff302 ∷ []) (Toff302 ∷ CX24 ∷ []) tt tt Eq.refl

wp1050 : Complete 4 → WsL → ⟪ (CX42 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX42 ∷ Toff304 ∷ []) ⟫ʷ
wp1050 c4 L = pw1 c4 L (CX42 ∷ Toff302 ∷ []) (Toff302 ∷ CX42 ∷ Toff304 ∷ []) tt tt Eq.refl

wp1051 : Complete 4 → WsL → ⟪ (CCZ134 ∷ Toff304 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ134 ∷ []) ⟫ʷ
wp1051 c4 L = pw2 c4 L (CCZ134 ∷ Toff304 ∷ CCZ014 ∷ []) (Toff304 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1052 : Complete 4 → WsL → ⟪ (CX04 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX04 ∷ []) ⟫ʷ
wp1052 c4 L = pw1 c4 L (CX04 ∷ Toff302 ∷ []) (Toff302 ∷ CX04 ∷ []) tt tt Eq.refl

wp1053 : Complete 4 → WsL → ⟪ (Toff302 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff302 ∷ []) ⟫ʷ
wp1053 c4 L = pw1 c4 L (Toff302 ∷ Toff304 ∷ []) (Toff304 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1054 : Complete 4 → WsL → ⟪ (CX42 ∷ Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp1054 c4 L = pw1 c4 L (CX42 ∷ Toff304 ∷ Toff304 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp1055 : Complete 4 → WsL → ⟪ (CX42 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX42 ∷ []) ⟫ʷ
wp1055 c4 L = pw1 c4 L (CX42 ∷ Toff304 ∷ []) (Toff304 ∷ CX42 ∷ []) tt tt Eq.refl

wp1056 : Complete 4 → WsL → ⟪ (CCZ134 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) ⟫ʷ
wp1056 c4 L = pw2 c4 L (CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1057 : Complete 4 → WsL → ⟪ (CX24 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX24 ∷ Toff302 ∷ []) ⟫ʷ
wp1057 c4 L = pw1 c4 L (CX24 ∷ Toff304 ∷ []) (Toff304 ∷ CX24 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1058 : Complete 4 → WsL → ⟪ (CS01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS01 ∷ []) ⟫ʷ
wp1058 c4 L = pw2 c4 L (CS01 ∷ Toff304 ∷ []) (Toff304 ∷ CS01 ∷ []) tt tt Eq.refl

wp1059 : Complete 4 → WsL → ⟪ (CX02 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX02 ∷ []) ⟫ʷ
wp1059 c4 L = pw1 c4 L (CX02 ∷ Toff304 ∷ []) (Toff304 ∷ CX02 ∷ []) tt tt Eq.refl

wp1060 : Complete 4 → WsL → ⟪ (CX24 ∷ Toff302 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ []) ⟫ʷ
wp1060 c4 L = pw1 c4 L (CX24 ∷ Toff302 ∷ Toff302 ∷ []) (CX24 ∷ []) tt tt Eq.refl

wp1061 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ []) ⟫ʷ
wp1061 c4 L = pw3 c4 L (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK41 ∷ []) tt tt Eq.refl

wp1062 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ []) ⟫ʷ
wp1062 c4 L = pw3 c4 L (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1063 : Complete 4 → WsL → ⟪ (CCZ234 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ234 ∷ CCZ024 ∷ []) ⟫ʷ
wp1063 c4 L = pw1 c4 L (CCZ234 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ234 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1064 : Complete 4 → WsL → ⟪ (CX14 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX14 ∷ Toff301 ∷ []) ⟫ʷ
wp1064 c4 L = pw2 c4 L (CX14 ∷ Toff304 ∷ []) (Toff304 ∷ CX14 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1065 : Complete 4 → WsL → ⟪ (CS02 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS02 ∷ []) ⟫ʷ
wp1065 c4 L = pw1 c4 L (CS02 ∷ Toff304 ∷ []) (Toff304 ∷ CS02 ∷ []) tt tt Eq.refl

wp1066 : Complete 4 → WsL → ⟪ (Toff301 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff301 ∷ []) ⟫ʷ
wp1066 c4 L = pw2 c4 L (Toff301 ∷ Toff304 ∷ []) (Toff304 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1067 : Complete 4 → WsL → ⟪ (CX14 ∷ Toff301 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wp1067 c4 L = pw2 c4 L (CX14 ∷ Toff301 ∷ Toff301 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wp1068 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wp1068 c4 L = pw1 c4 L (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wp1069 : Complete 4 → WsL → ⟪ (CX14 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX14 ∷ []) ⟫ʷ
wp1069 c4 L = pw2 c4 L (CX14 ∷ Toff301 ∷ []) (Toff301 ∷ CX14 ∷ []) tt tt Eq.refl

wp1070 : Complete 4 → WsL → ⟪ (CX41 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX41 ∷ Toff304 ∷ []) ⟫ʷ
wp1070 c4 L = pw2 c4 L (CX41 ∷ Toff301 ∷ []) (Toff301 ∷ CX41 ∷ Toff304 ∷ []) tt tt Eq.refl

wp1071 : Complete 4 → WsL → ⟪ (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ234 ∷ []) ⟫ʷ
wp1071 c4 L = pw1 c4 L (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1072 : Complete 4 → WsL → ⟪ (CX04 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX04 ∷ []) ⟫ʷ
wp1072 c4 L = pw2 c4 L (CX04 ∷ Toff301 ∷ []) (Toff301 ∷ CX04 ∷ []) tt tt Eq.refl

wp1073 : Complete 4 → WsL → ⟪ (CX41 ∷ Toff304 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wp1073 c4 L = pw2 c4 L (CX41 ∷ Toff304 ∷ Toff304 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wp1074 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK42 ∷ []) ⟫ʷ
wp1074 c4 L = pw3 c4 L (CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK42 ∷ []) tt tt Eq.refl

wp1075 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK42 ∷ CCZ012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ []) ⟫ʷ
wp1075 c4 L = pw3 c4 L (CCZ012 ∷ CK42 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1076 : Complete 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) ⟫ʷ
wp1076 c4 L = pw3 c4 L (CCZ014 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wp1077 : Complete 4 → WsL → ⟪ (CCZ134 ∷ CX04 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ134 ∷ []) ⟫ʷ
wp1077 c4 L = pw2 c4 L (CCZ134 ∷ CX04 ∷ CCZ013 ∷ []) (CX04 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1078 : Complete 4 → WsL → ⟪ (CX04 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ []) ⟫ʷ
wp1078 c4 L = pw2 c4 L (CX04 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX04 ∷ []) tt tt Eq.refl

wp1079 : Complete 4 → WsL → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ012 ∷ CX04 ∷ []) ⟫ʷ
wp1079 c4 L = pw3 c4 L (CCZ012 ∷ []) (CX04 ∷ CCZ012 ∷ CX04 ∷ []) tt tt Eq.refl

wp1080 : Complete 4 → WsL → ⟪ (CX40 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX40 ∷ Toff324 ∷ []) ⟫ʷ
wp1080 c4 L = pw1 c4 L (CX40 ∷ Toff302 ∷ []) (Toff302 ∷ CX40 ∷ Toff324 ∷ []) tt tt Eq.refl

wp1081 : Complete 4 → WsL → ⟪ (CCZ134 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ134 ∷ []) ⟫ʷ
wp1081 c4 L = pw2 c4 L (CCZ134 ∷ CX40 ∷ []) (CX40 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1082 : Complete 4 → WsL → ⟪ (CX40 ∷ Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ []) ⟫ʷ
wp1082 c4 L = pw1 c4 L (CX40 ∷ Toff324 ∷ Toff324 ∷ []) (CX40 ∷ []) tt tt Eq.refl

wp1083 : Complete 4 → WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ124 ∷ CX40 ∷ []) ⟫ʷ
wp1083 c4 L = pw3 c4 L (CCZ124 ∷ []) (CX40 ∷ CCZ124 ∷ CX40 ∷ []) tt tt Eq.refl

wp1084 : Complete 4 → WsL → ⟪ (CX04 ∷ CX40 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw04 ∷ []) ⟫ʷ
wp1084 c4 L = pw1 c4 L (CX04 ∷ CX40 ∷ CX04 ∷ []) (Sw04 ∷ []) tt tt Eq.refl

wp1085 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ
wp1085 c4 L = pw3 c4 L (CCZ012 ∷ CX40 ∷ []) (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1086 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ012 ∷ []) ⟫ʷ
wp1086 c4 L = pw3 c4 L (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1087 : Complete 4 → WsL → ⟪ (CCZ124 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ
wp1087 c4 L = pw3 c4 L (CCZ124 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1088 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wp1088 c4 L = pw3 c4 L (CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl

wp1089 : Complete 4 → WsL → ⟪ (CCZ234 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Sw04 ∷ CCZ023 ∷ []) ⟫ʷ
wp1089 c4 L = pw1 c4 L (CCZ234 ∷ Sw04 ∷ []) (Sw04 ∷ CCZ023 ∷ []) tt tt Eq.refl

wp1090 : Complete 4 → WsL → ⟪ (Sw04 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sw04 ∷ []) ⟫ʷ
wp1090 c4 L = pw1 c4 L (Sw04 ∷ Toff302 ∷ []) (Toff324 ∷ Sw04 ∷ []) tt tt Eq.refl

wp1091 : Complete 4 → WsL → ⟪ (CCZ023 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Sw04 ∷ CCZ234 ∷ []) ⟫ʷ
wp1091 c4 L = pw1 c4 L (CCZ023 ∷ Sw04 ∷ []) (Sw04 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1092 : Complete 4 → WsL → ⟪ (Sw04 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw04 ∷ []) ⟫ʷ
wp1092 c4 L = pw1 c4 L (Sw04 ∷ Toff234 ∷ []) (Toff203 ∷ Sw04 ∷ []) tt tt Eq.refl

wp1093 : Complete 4 → WsL → ⟪ (Sw04 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1093 c4 L = pw1 c4 L (Sw04 ∷ Sw04 ∷ []) [] tt tt Eq.refl

wp1094 : Complete 4 → WsL → ⟪ (CX40 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX40 ∷ []) ⟫ʷ
wp1094 c4 L = pw1 c4 L (CX40 ∷ Toff324 ∷ []) (Toff324 ∷ CX40 ∷ []) tt tt Eq.refl

wp1095 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CX40 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ CCZ013 ∷ []) ⟫ʷ
wp1095 c4 L = pw2 c4 L (CCZ013 ∷ CX40 ∷ CCZ134 ∷ []) (CX40 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1096 : Complete 4 → WsL → ⟪ (CX40 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX40 ∷ []) ⟫ʷ
wp1096 c4 L = pw2 c4 L (CX40 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX40 ∷ []) tt tt Eq.refl

wp1097 : Complete 4 → WsL → ⟪ (CX04 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX04 ∷ Toff302 ∷ []) ⟫ʷ
wp1097 c4 L = pw1 c4 L (CX04 ∷ Toff324 ∷ []) (Toff324 ∷ CX04 ∷ Toff302 ∷ []) tt tt Eq.refl

wp1098 : Complete 4 → WsL → ⟪ (CCZ013 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ013 ∷ []) ⟫ʷ
wp1098 c4 L = pw2 c4 L (CCZ013 ∷ CX04 ∷ []) (CX04 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1099 : Complete 4 → WsL → ⟪ (CX20 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX20 ∷ []) ⟫ʷ
wp1099 c4 L = pw1 c4 L (CX20 ∷ Toff324 ∷ []) (Toff324 ∷ CX20 ∷ []) tt tt Eq.refl

wp1100 : Complete 4 → WsL → ⟪ (CX04 ∷ Toff302 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ []) ⟫ʷ
wp1100 c4 L = pw1 c4 L (CX04 ∷ Toff302 ∷ Toff302 ∷ []) (CX04 ∷ []) tt tt Eq.refl

wp1101 : Complete 4 → WsL → ⟪ (CX40 ∷ CX04 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw04 ∷ []) ⟫ʷ
wp1101 c4 L = pw1 c4 L (CX40 ∷ CX04 ∷ CX40 ∷ []) (Sw04 ∷ []) tt tt Eq.refl

wp1102 : Complete 4 → WsL → ⟪ (CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
wp1102 c4 L = pw3 c4 L (CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl

wp1103 : Complete 4 → WsL → ⟪ (Sw04 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw04 ∷ []) ⟫ʷ
wp1103 c4 L = pw1 c4 L (Sw04 ∷ Toff324 ∷ []) (Toff302 ∷ Sw04 ∷ []) tt tt Eq.refl

wp1104 : Complete 4 → WsL → ⟪ (Sw04 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Sw04 ∷ []) ⟫ʷ
wp1104 c4 L = pw1 c4 L (Sw04 ∷ Toff203 ∷ []) (Toff234 ∷ Sw04 ∷ []) tt tt Eq.refl

wp1105 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK40 ∷ []) ⟫ʷ
wp1105 c4 L = pw3 c4 L (CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK40 ∷ []) tt tt Eq.refl

wp1106 : Complete 4 → WsL → ⟪ (CCZ034 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ []) ⟫ʷ
wp1106 c4 L = pw1 c4 L (CCZ034 ∷ K0 ∷ []) (K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1107 : Complete 4 → WsL → ⟪ (CCZ034 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CK40 ∷ CZ03 ∷ CCZ034 ∷ []) ⟫ʷ
wp1107 c4 L = pw1 c4 L (CCZ034 ∷ CK40 ∷ []) (CZ03 ∷ CK40 ∷ CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1108 : Complete 4 → WsL → ⟪ (K0 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ []) ⟫ʷ
wp1108 c4 L = pw1 c4 L (K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ []) tt tt Eq.refl

wp1109 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK40 ∷ CCZ012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ []) ⟫ʷ
wp1109 c4 L = pw3 c4 L (CCZ012 ∷ CK40 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1110 : Complete 4 → WsL → ⟪ (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff104 ∷ []) ⟫ʷ
wp1110 c4 L = pw2 c4 L (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ []) tt tt Eq.refl

wp1111 : Complete 4 → WsL → ⟪ (S4 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ S4 ∷ []) ⟫ʷ
wp1111 c4 L = pw1 c4 L (S4 ∷ Toff302 ∷ []) (Toff302 ∷ S4 ∷ []) tt tt Eq.refl

wp1112 : Complete 4 → WsL → ⟪ (Toff014 ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ CCZ012 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ []) ⟫ʷ
wp1112 c4 L = pw3 c4 L (Toff014 ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ []) tt tt Eq.refl

wp1113 : Complete 4 → WsL → ⟪ (CX42 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CX42 ∷ Toff014 ∷ []) ⟫ʷ
wp1113 c4 L = pw3 c4 L (CX42 ∷ Toff012 ∷ []) (Toff012 ∷ CX42 ∷ Toff014 ∷ []) tt tt Eq.refl

wp1114 : Complete 4 → WsL → ⟪ (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ034 ∷ []) ⟫ʷ
wp1114 c4 L = pw2 c4 L (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ034 ∷ []) tt tt Eq.refl

wp1115 : Complete 4 → WsL → ⟪ (CX42 ∷ Toff014 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (CX42 ∷ []) ⟫ʷ
wp1115 c4 L = pw3 c4 L (CX42 ∷ Toff014 ∷ Toff014 ∷ []) (CX42 ∷ []) tt tt Eq.refl

wp1116 : Complete 4 → WsL → ⟪ (Sw24 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw24 ∷ []) ⟫ʷ
wp1116 c4 L = pw3 c4 L (Sw24 ∷ Toff012 ∷ []) (Toff014 ∷ Sw24 ∷ []) tt tt Eq.refl

wp1117 : Complete 4 → WsL → ⟪ (Sw24 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Sw24 ∷ []) ⟫ʷ
wp1117 c4 L = pw3 c4 L (Sw24 ∷ Toff104 ∷ []) (Toff102 ∷ Sw24 ∷ []) tt tt Eq.refl

wp1118 : Complete 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ []) ⟫ʷ
wp1118 c4 L = pw3 c4 L (CCZ024 ∷ []) (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ []) tt tt Eq.refl

wp1119 : Complete 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
wp1119 c4 L = pw3 c4 L (CCZ024 ∷ []) (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) tt tt Eq.refl

wp1120 : Complete 4 → WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
wp1120 c4 L = pw1 c4 L (CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl

wp1121 : Complete 4 → WsL → ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) ⟫ʷ
wp1121 c4 L = pw3 c4 L (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) (CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1122 : Complete 4 → WsL → ⟪ (CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wp1122 c4 L = pw3 c4 L (CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ []) (S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
