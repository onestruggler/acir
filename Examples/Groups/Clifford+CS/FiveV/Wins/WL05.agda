------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WL05 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0930 : Complete 4 → ⟪ (CCZ012 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) ⟫ʷ
wl0930 c4 = lw4 c4 (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) tt tt Eq.refl

wl0931 : Complete 4 → ⟪ (CCZ012 ∷ CZ01 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
wl0931 c4 = lw4 c4 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ []) tt tt Eq.refl

wl0932 : Complete 4 → ⟪ (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
wl0932 c4 = lw0 c4 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0933 : Complete 4 → ⟪ (CCZ234 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff234 ∷ []) ⟫ʷ
wl0933 c4 = lw0 c4 (CCZ234 ∷ CZ34 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff234 ∷ []) tt tt Eq.refl

wl0934 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ CCZ234 ∷ CZ34 ∷ []) ⟫ʷ
wl0934 c4 = lw0 c4 (CCZ234 ∷ []) (CZ34 ∷ CCZ234 ∷ CZ34 ∷ []) tt tt Eq.refl

wl0935 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) ⟫ʷ
wl0935 c4 = lw4 c4 (CCZ012 ∷ []) (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) tt tt Eq.refl

wl0936 : Complete 4 → ⟪ (CCZ234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) ⟫ʷ
wl0936 c4 = lw0 c4 (CCZ234 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) tt tt Eq.refl

wl0937 : Complete 4 → ⟪ (CCZ234 ∷ CZ34 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
wl0937 c4 = lw0 c4 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ []) tt tt Eq.refl

wl0938 : Complete 4 → ⟪ (CX41 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX41 ∷ []) ⟫ʷ
wl0938 c4 = lw0 c4 (CX41 ∷ Toff234 ∷ []) (Toff234 ∷ CX41 ∷ []) tt tt Eq.refl

wl0939 : Complete 4 → ⟪ (CX14 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX14 ∷ Toff213 ∷ []) ⟫ʷ
wl0939 c4 = lw0 c4 (CX14 ∷ Toff234 ∷ []) (Toff234 ∷ CX14 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0940 : Complete 4 → ⟪ (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ012 ∷ []) ⟫ʷ
wl0940 c4 = lw4 c4 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (Toff213 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0941 : Complete 4 → ⟪ (CX31 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CX31 ∷ []) ⟫ʷ
wl0941 c4 = lw0 c4 (CX31 ∷ Toff234 ∷ []) (Toff234 ∷ CX31 ∷ []) tt tt Eq.refl

wl0942 : Complete 4 → ⟪ (Toff213 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff213 ∷ []) ⟫ʷ
wl0942 c4 = lw0 c4 (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0943 : Complete 4 → ⟪ (CX14 ∷ Toff213 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wl0943 c4 = lw0 c4 (CX14 ∷ Toff213 ∷ Toff213 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wl0944 : Complete 4 → ⟪ (CX14 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX14 ∷ []) ⟫ʷ
wl0944 c4 = lw0 c4 (CX14 ∷ Toff213 ∷ []) (Toff213 ∷ CX14 ∷ []) tt tt Eq.refl

wl0945 : Complete 4 → ⟪ (CCZ012 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
wl0945 c4 = lw4 c4 (CCZ012 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0946 : Complete 4 → ⟪ (CX41 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX41 ∷ Toff234 ∷ []) ⟫ʷ
wl0946 c4 = lw0 c4 (CX41 ∷ Toff213 ∷ []) (Toff213 ∷ CX41 ∷ Toff234 ∷ []) tt tt Eq.refl

wl0947 : Complete 4 → ⟪ (CX34 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX34 ∷ []) ⟫ʷ
wl0947 c4 = lw0 c4 (CX34 ∷ Toff213 ∷ []) (Toff213 ∷ CX34 ∷ []) tt tt Eq.refl

wl0948 : Complete 4 → ⟪ (CX41 ∷ Toff234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wl0948 c4 = lw0 c4 (CX41 ∷ Toff234 ∷ Toff234 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wl0949 : Complete 4 → ⟪ (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
wl0949 c4 = lw4 c4 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0950 : Complete 4 → ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff201 ∷ []) ⟫ʷ
wl0950 c4 = lw4 c4 (CCZ012 ∷ CZ01 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0951 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ CZ01 ∷ []) ⟫ʷ
wl0951 c4 = lw4 c4 (CCZ012 ∷ []) (CZ01 ∷ CCZ012 ∷ CZ01 ∷ []) tt tt Eq.refl

wl0952 : Complete 4 → ⟪ (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wl0952 c4 = lw4 c4 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl

wl0953 : Complete 4 → ⟪ (Toff213 ∷ CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wl0953 c4 = lw4 c4 (Toff213 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff213 ∷ []) tt tt Eq.refl

wl0954 : Complete 4 → ⟪ (CCZ134 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ134 ∷ []) ⟫ʷ
wl0954 c4 = lw0 c4 (CCZ134 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0955 : Complete 4 → ⟪ (CX03 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX03 ∷ []) ⟫ʷ
wl0955 c4 = lw4 c4 (CX03 ∷ Toff201 ∷ []) (Toff201 ∷ CX03 ∷ []) tt tt Eq.refl

wl0956 : Complete 4 → ⟪ (CX30 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX30 ∷ Toff213 ∷ []) ⟫ʷ
wl0956 c4 = lw4 c4 (CX30 ∷ Toff201 ∷ []) (Toff201 ∷ CX30 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0957 : Complete 4 → ⟪ (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ234 ∷ []) ⟫ʷ
wl0957 c4 = lw0 c4 (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) (Toff213 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0958 : Complete 4 → ⟪ (CX13 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX13 ∷ []) ⟫ʷ
wl0958 c4 = lw4 c4 (CX13 ∷ Toff201 ∷ []) (Toff201 ∷ CX13 ∷ []) tt tt Eq.refl

wl0959 : Complete 4 → ⟪ (CX30 ∷ Toff213 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wl0959 c4 = lw4 c4 (CX30 ∷ Toff213 ∷ Toff213 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wl0960 : Complete 4 → ⟪ (CCZ134 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ134 ∷ []) ⟫ʷ
wl0960 c4 = lw0 c4 (CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0961 : Complete 4 → ⟪ (CX03 ∷ CX30 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ []) ⟫ʷ
wl0961 c4 = lw4 c4 (CX03 ∷ CX30 ∷ CX03 ∷ []) (Sw03 ∷ []) tt tt Eq.refl

wl0962 : Complete 4 → ⟪ (Sw03 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw03 ∷ []) ⟫ʷ
wl0962 c4 = lw4 c4 (Sw03 ∷ Toff201 ∷ []) (Toff213 ∷ Sw03 ∷ []) tt tt Eq.refl

wl0963 : Complete 4 → ⟪ (Sw03 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Sw03 ∷ []) ⟫ʷ
wl0963 c4 = lw4 c4 (Sw03 ∷ Toff123 ∷ []) (Toff102 ∷ Sw03 ∷ []) tt tt Eq.refl

wl0964 : Complete 4 → ⟪ (CS12 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) ⟫ʷ
wl0964 c4 = lw4 c4 (CS12 ∷ Toff213 ∷ []) (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0965 : Complete 4 → ⟪ (CCZ123 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
wl0965 c4 = lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0966 : Complete 4 → ⟪ (CS13 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS13 ∷ []) ⟫ʷ
wl0966 c4 = lw4 c4 (CS13 ∷ Toff213 ∷ []) (Toff213 ∷ CS13 ∷ []) tt tt Eq.refl

wl0967 : Complete 4 → ⟪ (CS12 ∷ CS13 ∷ CCZ123 ∷ CS13 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wl0967 c4 = lw4 c4 (CS12 ∷ CS13 ∷ CCZ123 ∷ CS13 ∷ CZ13 ∷ CCZ123 ∷ []) (CS12 ∷ []) tt tt Eq.refl

wl0968 : Complete 4 → ⟪ (CS12⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0968 c4 = lw4 c4 (CS12⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0969 : Complete 4 → ⟪ (CS13⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0969 c4 = lw4 c4 (CS13⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0970 : Complete 4 → ⟪ (CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ CS13⁻ ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
wl0970 c4 = lw4 c4 (CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ CS13⁻ ∷ CZ13 ∷ CCZ123 ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl

wl0971 : Complete 4 → ⟪ (CZ13 ∷ CCZ123 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
wl0971 c4 = lw4 c4 (CZ13 ∷ CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0972 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0972 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0973 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ CCZ124 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ []) ⟫ʷ
wl0973 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0974 : Complete 4 → ⟪ (CCZ124 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ124 ∷ []) ⟫ʷ
wl0974 c4 = lw0 c4 (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0975 : Complete 4 → ⟪ (CX31 ∷ Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff134 ∷ []) ⟫ʷ
wl0975 c4 = lw0 c4 (CX31 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0976 : Complete 4 → ⟪ (CX31 ∷ CX32 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX31 ∷ []) ⟫ʷ
wl0976 c4 = lw4 c4 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX31 ∷ []) tt tt Eq.refl

wl0977 : Complete 4 → ⟪ (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff134 ∷ []) ⟫ʷ
wl0977 c4 = lw0 c4 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0978 : Complete 4 → ⟪ (CX31 ∷ CX32 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wl0978 c4 = lw4 c4 (CX31 ∷ CX32 ∷ CX32 ∷ []) (CX31 ∷ []) tt tt Eq.refl

wl0979 : Complete 4 → ⟪ (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wl0979 c4 = lw0 c4 (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wl0980 : Complete 4 → ⟪ (CS12 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12 ∷ []) ⟫ʷ
wl0980 c4 = lw0 c4 (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ []) tt tt Eq.refl

wl0981 : Complete 4 → ⟪ (CS03⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0981 c4 = lw4 c4 (CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0982 : Complete 4 → ⟪ (CS12 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS12 ∷ []) ⟫ʷ
wl0982 c4 = lw0 c4 (CS12 ∷ Toff314 ∷ []) (Toff314 ∷ CS12 ∷ []) tt tt Eq.refl

wl0983 : Complete 4 → ⟪ (CS03 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS03 ∷ []) ⟫ʷ
wl0983 c4 = lw4 c4 (CS03 ∷ CS12 ∷ []) (CS12 ∷ CS03 ∷ []) tt tt Eq.refl

wl0984 : Complete 4 → ⟪ (CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0984 c4 = lw0 c4 (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0985 : Complete 4 → ⟪ (CS12⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0985 c4 = lw0 c4 (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0986 : Complete 4 → ⟪ (CS03 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS03 ∷ []) ⟫ʷ
wl0986 c4 = lw4 c4 (CS03 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03 ∷ []) tt tt Eq.refl

wl0987 : Complete 4 → ⟪ (CX13 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX13 ∷ Toff012 ∷ []) ⟫ʷ
wl0987 c4 = lw4 c4 (CX13 ∷ Toff023 ∷ []) (Toff023 ∷ CX13 ∷ Toff012 ∷ []) tt tt Eq.refl

wl0988 : Complete 4 → ⟪ (CX13 ∷ Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
wl0988 c4 = lw4 c4 (CX13 ∷ Toff012 ∷ Toff012 ∷ []) (CX13 ∷ []) tt tt Eq.refl

wl0989 : Complete 4 → ⟪ (Sw13 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw13 ∷ []) ⟫ʷ
wl0989 c4 = lw4 c4 (Sw13 ∷ Toff023 ∷ []) (Toff012 ∷ Sw13 ∷ []) tt tt Eq.refl

wl0990 : Complete 4 → ⟪ (Sw13 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw13 ∷ []) ⟫ʷ
wl0990 c4 = lw4 c4 (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ []) tt tt Eq.refl

wl0991 : Complete 4 → ⟪ (CCZ012 ∷ CCZ123 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ012 ∷ []) ⟫ʷ
wl0991 c4 = lw4 c4 (CCZ012 ∷ CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0992 : Complete 4 → ⟪ (CCZ012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wl0992 c4 = lw4 c4 (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0993 : Complete 4 → ⟪ (CCZ012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ012 ∷ []) ⟫ʷ
wl0993 c4 = lw3 c4 (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0994 : Complete 4 → ⟪ (CX12 ∷ Toff214 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff214 ∷ []) ⟫ʷ
wl0994 c4 = lw0 c4 (CX12 ∷ Toff214 ∷ X4 ∷ []) (X4 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0995 : Complete 4 → ⟪ (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ []) ⟫ʷ
wl0995 c4 = lw0 c4 (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0996 : Complete 4 → ⟪ (Toff214 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX12 ∷ Toff214 ∷ []) ⟫ʷ
wl0996 c4 = lw0 c4 (Toff214 ∷ X4 ∷ []) (X4 ∷ CX12 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0997 : Complete 4 → ⟪ (CS02 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ []) ⟫ʷ
wl0997 c4 = lw3 c4 (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ []) tt tt Eq.refl

wl0998 : Complete 4 → ⟪ (CS02⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0998 c4 = lw3 c4 (CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0999 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0999 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1000 : Complete 4 → ⟪ (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) ⟫ʷ
wl1000 c4 = lw0 c4 (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1001 : Complete 4 → ⟪ (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ
wl1001 c4 = lw0 c4 (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ []) tt tt Eq.refl

wl1002 : Complete 4 → ⟪ (CX20 ∷ CX23 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX23 ∷ []) ⟫ʷ
wl1002 c4 = lw4 c4 (CX20 ∷ CX23 ∷ Toff023 ∷ []) (Toff023 ∷ CX23 ∷ []) tt tt Eq.refl

wl1003 : Complete 4 → ⟪ (CX20 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX20 ∷ []) ⟫ʷ
wl1003 c4 = lw4 c4 (CX20 ∷ Toff023 ∷ []) (Toff023 ∷ CX20 ∷ []) tt tt Eq.refl

wl1004 : Complete 4 → ⟪ (CCZ124 ∷ CX23 ∷ CCZ124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff324 ∷ []) ⟫ʷ
wl1004 c4 = lw0 c4 (CCZ124 ∷ CX23 ∷ CCZ124 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ []) tt tt Eq.refl

wl1005 : Complete 4 → ⟪ (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13 ∷ []) ⟫ʷ
wl1005 c4 = lw0 c4 (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wl1006 : Complete 4 → ⟪ (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wl1006 c4 = lw0 c4 (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1007 : Complete 4 → ⟪ (CCZ013 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
wl1007 c4 = lw4 c4 (CCZ013 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1008 : Complete 4 → ⟪ (CCZ123 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CCZ123 ∷ []) ⟫ʷ
wl1008 c4 = lw0 c4 (CCZ123 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1009 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl1009 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl1010 : Complete 4 → ⟪ (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1010 c4 = lw0 c4 (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ []) (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1011 : Complete 4 → ⟪ (CCZ124 ∷ CS13 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ
wl1011 c4 = lw0 c4 (CCZ124 ∷ CS13 ∷ Toff324 ∷ []) (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1012 : Complete 4 → ⟪ (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ
wl1012 c4 = lw0 c4 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wl1013 : Complete 4 → ⟪ (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wl1013 c4 = lw0 c4 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wl1014 : Complete 4 → ⟪ (K1⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K1⁻ ∷ []) ⟫ʷ
wl1014 c4 = lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl

wl1015 : Complete 4 → ⟪ (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
wl1015 c4 = lw0 c4 (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl1016 : Complete 4 → ⟪ (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl1016 c4 = lw0 c4 (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1017 : Complete 4 → ⟪ (CS12⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1017 c4 = lw4 c4 (CS12⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1018 : Complete 4 → ⟪ (CX23 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX23 ∷ Toff012 ∷ []) ⟫ʷ
wl1018 c4 = lw4 c4 (CX23 ∷ Toff013 ∷ []) (Toff013 ∷ CX23 ∷ Toff012 ∷ []) tt tt Eq.refl

wl1019 : Complete 4 → ⟪ (CX23 ∷ Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wl1019 c4 = lw4 c4 (CX23 ∷ Toff012 ∷ Toff012 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wl1020 : Complete 4 → ⟪ (CX32 ∷ CX23 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ []) ⟫ʷ
wl1020 c4 = lw4 c4 (CX32 ∷ CX23 ∷ CX32 ∷ []) (Sw23 ∷ []) tt tt Eq.refl

wl1021 : Complete 4 → ⟪ (CCZ134 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ134 ∷ []) ⟫ʷ
wl1021 c4 = lw0 c4 (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl1022 : Complete 4 → ⟪ (CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wl1022 c4 = lw0 c4 (CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wl1023 : Complete 4 → ⟪ (Sw23 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw23 ∷ []) ⟫ʷ
wl1023 c4 = lw4 c4 (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1024 : Complete 4 → ⟪ (Sw23 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw23 ∷ []) ⟫ʷ
wl1024 c4 = lw4 c4 (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) tt tt Eq.refl

wl1025 : Complete 4 → ⟪ (Toff134 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) ⟫ʷ
wl1025 c4 = lw0 c4 (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) tt tt Eq.refl

wl1026 : Complete 4 → ⟪ (CZ13 ∷ CCZ013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
wl1026 c4 = lw4 c4 (CZ13 ∷ CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1027 : Complete 4 → ⟪ (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ []) ⟫ʷ
wl1027 c4 = lw0 c4 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wl1028 : Complete 4 → ⟪ (CX10 ∷ CX13 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX13 ∷ []) ⟫ʷ
wl1028 c4 = lw4 c4 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (Toff013 ∷ CX13 ∷ []) tt tt Eq.refl

wl1029 : Complete 4 → ⟪ (CX10 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX10 ∷ []) ⟫ʷ
wl1029 c4 = lw4 c4 (CX10 ∷ Toff013 ∷ []) (Toff013 ∷ CX10 ∷ []) tt tt Eq.refl

wl1030 : Complete 4 → ⟪ (CCZ124 ∷ CX13 ∷ CCZ124 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Toff314 ∷ []) ⟫ʷ
wl1030 c4 = lw0 c4 (CCZ124 ∷ CX13 ∷ CCZ124 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wl1031 : Complete 4 → ⟪ (CCZ123 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1031 c4 = lw0 c4 (CCZ123 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1032 : Complete 4 → ⟪ (CCZ234 ∷ CS12 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff134 ∷ CCZ234 ∷ []) ⟫ʷ
wl1032 c4 = lw0 c4 (CCZ234 ∷ CS12 ∷ Toff134 ∷ []) (CS12 ∷ Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1033 : Complete 4 → ⟪ (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ
wl1033 c4 = lw0 c4 (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX23 ∷ Toff324 ∷ []) tt tt Eq.refl

wl1034 : Complete 4 → ⟪ (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13 ∷ []) ⟫ʷ
wl1034 c4 = lw0 c4 (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13 ∷ []) tt tt Eq.refl

wl1035 : Complete 4 → ⟪ (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wl1035 c4 = lw0 c4 (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1036 : Complete 4 → ⟪ (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl1036 c4 = lw0 c4 (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1037 : Complete 4 → ⟪ (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) ⟫ʷ
wl1037 c4 = lw0 c4 (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1038 : Complete 4 → ⟪ (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ
wl1038 c4 = lw0 c4 (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wl1039 : Complete 4 → ⟪ (CX30 ∷ CX31 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX31 ∷ []) ⟫ʷ
wl1039 c4 = lw4 c4 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (Toff013 ∷ CX31 ∷ []) tt tt Eq.refl

wl1040 : Complete 4 → ⟪ (CX30 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX30 ∷ []) ⟫ʷ
wl1040 c4 = lw4 c4 (CX30 ∷ Toff013 ∷ []) (Toff013 ∷ CX30 ∷ []) tt tt Eq.refl

wl1041 : Complete 4 → ⟪ (CCZ234 ∷ CX31 ∷ CCZ234 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff134 ∷ []) ⟫ʷ
wl1041 c4 = lw0 c4 (CCZ234 ∷ CX31 ∷ CCZ234 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wl1042 : Complete 4 → ⟪ (CS12 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12 ∷ []) ⟫ʷ
wl1042 c4 = lw0 c4 (CS12 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12 ∷ []) tt tt Eq.refl

wl1043 : Complete 4 → ⟪ (CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wl1043 c4 = lw0 c4 (CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1044 : Complete 4 → ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ
wl1044 c4 = lw0 c4 (CS14 ∷ S4 ∷ []) (S4 ∷ CS14 ∷ []) tt tt Eq.refl

wl1045 : Complete 4 → ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ
wl1045 c4 = lw0 c4 (CS24 ∷ S4 ∷ []) (S4 ∷ CS24 ∷ []) tt tt Eq.refl

wl1046 : Complete 4 → ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ
wl1046 c4 = lw0 c4 (CS34 ∷ S4 ∷ []) (S4 ∷ CS34 ∷ []) tt tt Eq.refl

wl1047 : Complete 4 → ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ
wl1047 c4 = lw0 c4 (CK41 ∷ S4 ∷ []) (S4 ∷ CK41 ∷ []) tt tt Eq.refl

wl1048 : Complete 4 → ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ
wl1048 c4 = lw0 c4 (CK42 ∷ S4 ∷ []) (S4 ∷ CK42 ∷ []) tt tt Eq.refl

wl1049 : Complete 4 → ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ
wl1049 c4 = lw0 c4 (CK43 ∷ S4 ∷ []) (S4 ∷ CK43 ∷ []) tt tt Eq.refl

wl1050 : Complete 4 → ⟪ (S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S4 ∷ []) ⟫ʷ
wl1050 c4 = lw0 c4 (S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S4 ∷ []) tt tt Eq.refl

wl1051 : Complete 4 → ⟪ (S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S4 ∷ []) ⟫ʷ
wl1051 c4 = lw0 c4 (S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S4 ∷ []) tt tt Eq.refl

wl1052 : Complete 4 → ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ
wl1052 c4 = lw0 c4 (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) tt tt Eq.refl

wl1053 : Complete 4 → ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ
wl1053 c4 = lw0 c4 (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) tt tt Eq.refl

wl1054 : Complete 4 → ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ
wl1054 c4 = lw0 c4 (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ []) tt tt Eq.refl

wl1055 : Complete 4 → ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ
wl1055 c4 = lw0 c4 (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ []) tt tt Eq.refl

wl1056 : Complete 4 → ⟪ (CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS14 ∷ []) ⟫ʷ
wl1056 c4 = lw0 c4 (CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS14 ∷ []) tt tt Eq.refl

wl1057 : Complete 4 → ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ
wl1057 c4 = lw0 c4 (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ []) tt tt Eq.refl

wl1058 : Complete 4 → ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ
wl1058 c4 = lw0 c4 (CK41 ∷ CS24 ∷ []) (CS24 ∷ CK41 ∷ []) tt tt Eq.refl

wl1059 : Complete 4 → ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ
wl1059 c4 = lw0 c4 (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ []) tt tt Eq.refl

wl1060 : Complete 4 → ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ
wl1060 c4 = lw0 c4 (CK41 ∷ CS34 ∷ []) (CS34 ∷ CK41 ∷ []) tt tt Eq.refl

wl1061 : Complete 4 → ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ
wl1061 c4 = lw0 c4 (CK42 ∷ CS34 ∷ []) (CS34 ∷ CK42 ∷ []) tt tt Eq.refl

wl1062 : Complete 4 → ⟪ (CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ []) ⟫ʷ
wl1062 c4 = lw0 c4 (CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ []) tt tt Eq.refl

wl1063 : Complete 4 → ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ
wl1063 c4 = lw0 c4 (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ []) tt tt Eq.refl

wl1064 : Complete 4 → ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ
wl1064 c4 = lw0 c4 (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ []) tt tt Eq.refl

wl1065 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ123 ∷ CZ01 ∷ []) ⟫ʷ
wl1065 c4 = lw4 c4 (CCZ123 ∷ []) (CZ01 ∷ CCZ123 ∷ CZ01 ∷ []) tt tt Eq.refl

wl1066 : Complete 4 → ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) ⟫ʷ
wl1066 c4 = lw0 c4 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) tt tt Eq.refl

wl1067 : Complete 4 → ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ
wl1067 c4 = lw0 c4 (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ []) tt tt Eq.refl

wl1068 : Complete 4 → ⟪ (CK42 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CK42 ∷ []) ⟫ʷ
wl1068 c4 = lw0 c4 (CK42 ∷ Toff314 ∷ []) (Toff314 ∷ CK42 ∷ []) tt tt Eq.refl

wl1069 : Complete 4 → ⟪ (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ234 ∷ []) ⟫ʷ
wl1069 c4 = lw0 c4 (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) (CK43 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1070 : Complete 4 → ⟪ (CZ23 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) ⟫ʷ
wl1070 c4 = lw4 c4 (CZ23 ∷ Toff201 ∷ []) (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1071 : Complete 4 → ⟪ (CCZ234 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ234 ∷ []) ⟫ʷ
wl1071 c4 = lw0 c4 (CCZ234 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1072 : Complete 4 → ⟪ (CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CK43 ∷ []) ⟫ʷ
wl1072 c4 = lw0 c4 (CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ []) (CZ23 ∷ CK43 ∷ []) tt tt Eq.refl

wl1073 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ013 ∷ CZ23 ∷ []) ⟫ʷ
wl1073 c4 = lw4 c4 (CCZ013 ∷ []) (CZ23 ∷ CCZ013 ∷ CZ23 ∷ []) tt tt Eq.refl

wl1074 : Complete 4 → ⟪ (CZ03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) ⟫ʷ
wl1074 c4 = lw4 c4 (CZ03 ∷ Toff012 ∷ []) (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1075 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ123 ∷ CZ03 ∷ []) ⟫ʷ
wl1075 c4 = lw4 c4 (CCZ123 ∷ []) (CZ03 ∷ CCZ123 ∷ CZ03 ∷ []) tt tt Eq.refl

wl1076 : Complete 4 → ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) ⟫ʷ
wl1076 c4 = lw0 c4 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) tt tt Eq.refl

wl1077 : Complete 4 → ⟪ (CS03⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1077 c4 = lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl

wl1078 : Complete 4 → ⟪ (CS03 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1078 c4 = lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl

wl1079 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1079 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl

wl1080 : Complete 4 → ⟪ (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1080 c4 = lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl

wl1081 : Complete 4 → ⟪ (CS01 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) ⟫ʷ
wl1081 c4 = lw4 c4 (CS01 ∷ Toff013 ∷ []) (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1082 : Complete 4 → ⟪ (CS01 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wl1082 c4 = lw4 c4 (CS01 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS01 ∷ []) tt tt Eq.refl

wl1083 : Complete 4 → ⟪ (X4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1083 c4 = lw0 c4 (X4 ∷ X4 ∷ []) [] tt tt Eq.refl

wl1084 : Complete 4 → ⟪ (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff012 ∷ []) ⟫ʷ
wl1084 c4 = lw4 c4 (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (Toff301 ∷ Toff012 ∷ []) tt tt Eq.refl

wl1085 : Complete 4 → ⟪ (Toff012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff012 ∷ []) ⟫ʷ
wl1085 c4 = lw4 c4 (Toff012 ∷ Toff312 ∷ []) (Toff312 ∷ Toff012 ∷ []) tt tt Eq.refl

wl1086 : Complete 4 → ⟪ (CCZ013 ∷ X3 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CCZ013 ∷ []) ⟫ʷ
wl1086 c4 = lw4 c4 (CCZ013 ∷ X3 ∷ CZ01 ∷ []) (X3 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1087 : Complete 4 → ⟪ (CCZ013 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ013 ∷ []) ⟫ʷ
wl1087 c4 = lw4 c4 (CCZ013 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1088 : Complete 4 → ⟪ (X3 ∷ CZ01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
wl1088 c4 = lw4 c4 (X3 ∷ CZ01 ∷ CZ01 ∷ []) (X3 ∷ []) tt tt Eq.refl

wl1089 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CCZ124 ∷ X3 ∷ []) ⟫ʷ
wl1089 c4 = lw0 c4 (CCZ124 ∷ []) (X3 ∷ CCZ124 ∷ X3 ∷ []) tt tt Eq.refl

wl1090 : Complete 4 → ⟪ (CCZ124 ∷ CK34 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34 ∷ []) ⟫ʷ
wl1090 c4 = lw0 c4 (CCZ124 ∷ CK34 ∷ CCZ124 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34 ∷ []) tt tt Eq.refl

wl1091 : Complete 4 → ⟪ (CCZ124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CCZ124 ∷ []) ⟫ʷ
wl1091 c4 = lw0 c4 (CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1092 : Complete 4 → ⟪ (K4 ∷ CK34 ∷ S3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK34 ∷ []) ⟫ʷ
wl1092 c4 = lw0 c4 (K4 ∷ CK34 ∷ S3 ∷ X3 ∷ []) (X3 ∷ CK34 ∷ []) tt tt Eq.refl

wl1093 : Complete 4 → ⟪ (CCZ124 ∷ CK34 ∷ CCZ124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ []) ⟫ʷ
wl1093 c4 = lw0 c4 (CCZ124 ∷ CK34 ∷ CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1094 : Complete 4 → ⟪ (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34⁻ ∷ []) ⟫ʷ
wl1094 c4 = lw0 c4 (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34⁻ ∷ []) tt tt Eq.refl

wl1095 : Complete 4 → ⟪ (K4 ∷ CK34 ∷ ι ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK34⁻ ∷ []) ⟫ʷ
wl1095 c4 = lw1 c4 (K4 ∷ CK34 ∷ ι ∷ X3 ∷ []) (X3 ∷ CK34⁻ ∷ []) tt tt Eq.refl

wl1096 : Complete 4 → ⟪ (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ []) ⟫ʷ
wl1096 c4 = lw0 c4 (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1097 : Complete 4 → ⟪ (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ234 ∷ []) ⟫ʷ
wl1097 c4 = lw0 c4 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (CX12 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl1098 : Complete 4 → ⟪ (CX12 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wl1098 c4 = lw0 c4 (CX12 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wl1099 : Complete 4 → ⟪ (CX21 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX21 ∷ Toff302 ∷ []) ⟫ʷ
wl1099 c4 = lw4 c4 (CX21 ∷ Toff301 ∷ []) (Toff301 ∷ CX21 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1100 : Complete 4 → ⟪ (Toff301 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff301 ∷ []) ⟫ʷ
wl1100 c4 = lw4 c4 (Toff301 ∷ Toff302 ∷ []) (Toff302 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1101 : Complete 4 → ⟪ (CX21 ∷ Toff302 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wl1101 c4 = lw4 c4 (CX21 ∷ Toff302 ∷ Toff302 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wl1102 : Complete 4 → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1102 c4 = lw0 c4 (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) [] tt tt Eq.refl

wl1103 : Complete 4 → ⟪ (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1103 c4 = lw0 c4 (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) [] tt tt Eq.refl

wl1104 : Complete 4 → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1104 c4 = lw0 c4 (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) [] tt tt Eq.refl

wl1105 : Complete 4 → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1105 c4 = lw0 c4 (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) [] tt tt Eq.refl

wl1106 : Complete 4 → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl1106 c4 = lw0 c4 (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl1107 : Complete 4 → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl1107 c4 = lw0 c4 (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl1108 : Complete 4 → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl1108 c4 = lw0 c4 (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl1109 : Complete 4 → ⟪ (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl1109 c4 = lw0 c4 (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl1110 : Complete 4 → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl1110 c4 = lw0 c4 (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl1111 : Complete 4 → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl1111 c4 = lw0 c4 (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl1112 : Complete 4 → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1112 c4 = lw4 c4 [] [] tt tt Eq.refl

wl1113 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1113 c4 = lw0 c4 (CCZ124 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1114 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1114 c4 = lw0 c4 (CCZ234 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1115 : Complete 4 → ⟪ (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) ⟫ʷ
wl1115 c4 = lw0 c4 (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ []) tt tt Eq.refl

wl1116 : Complete 4 → ⟪ (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) ⟫ʷ
wl1116 c4 = lw0 c4 (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ []) tt tt Eq.refl

wl1117 : Complete 4 → ⟪ (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) ⟫ʷ
wl1117 c4 = lw0 c4 (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) tt tt Eq.refl

wl1118 : Complete 4 → ⟪ (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) ⟫ʷ
wl1118 c4 = lw0 c4 (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) tt tt Eq.refl

wl1119 : Complete 4 → ⟪ (CCZ023 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ023 ∷ CCZ013 ∷ []) ⟫ʷ
wl1119 c4 = lw4 c4 (CCZ023 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ023 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1120 : Complete 4 → ⟪ (CX43 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX43 ∷ Toff214 ∷ []) ⟫ʷ
wl1120 c4 = lw0 c4 (CX43 ∷ Toff213 ∷ []) (Toff213 ∷ CX43 ∷ Toff214 ∷ []) tt tt Eq.refl

wl1121 : Complete 4 → ⟪ (CX43 ∷ Toff214 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wl1121 c4 = lw0 c4 (CX43 ∷ Toff214 ∷ Toff214 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wl1122 : Complete 4 → ⟪ (CCZ124 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ123 ∷ []) ⟫ʷ
wl1122 c4 = lw0 c4 (CCZ124 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1123 : Complete 4 → ⟪ (Sw34 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw34 ∷ []) ⟫ʷ
wl1123 c4 = lw0 c4 (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ []) tt tt Eq.refl

wl1124 : Complete 4 → ⟪ (CCZ123 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ124 ∷ []) ⟫ʷ
wl1124 c4 = lw0 c4 (CCZ123 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1125 : Complete 4 → ⟪ (Sw34 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw34 ∷ []) ⟫ʷ
wl1125 c4 = lw0 c4 (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ []) tt tt Eq.refl

wl1126 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) ⟫ʷ
wl1126 c4 = lw4 c4 (CCZ023 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) tt tt Eq.refl

wl1127 : Complete 4 → ⟪ (CCZ124 ∷ X4 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ124 ∷ []) ⟫ʷ
wl1127 c4 = lw0 c4 (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (X4 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1128 : Complete 4 → ⟪ (CZ12 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CZ12 ∷ CCZ013 ∷ []) ⟫ʷ
wl1128 c4 = lw4 c4 (CZ12 ∷ Toff203 ∷ []) (Toff203 ∷ CZ12 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1129 : Complete 4 → ⟪ (CCZ124 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ124 ∷ []) ⟫ʷ
wl1129 c4 = lw0 c4 (CCZ124 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl1130 : Complete 4 → ⟪ (X4 ∷ CZ12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wl1130 c4 = lw0 c4 (X4 ∷ CZ12 ∷ CZ12 ∷ []) (X4 ∷ []) tt tt Eq.refl

wl1131 : Complete 4 → ⟪ (CCZ013 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ013 ∷ []) ⟫ʷ
wl1131 c4 = lw4 c4 (CCZ013 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1132 : Complete 4 → ⟪ (CX43 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX43 ∷ []) ⟫ʷ
wl1132 c4 = lw0 c4 (CX43 ∷ Toff214 ∷ []) (Toff214 ∷ CX43 ∷ []) tt tt Eq.refl

wl1133 : Complete 4 → ⟪ (CX34 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX34 ∷ Toff213 ∷ []) ⟫ʷ
wl1133 c4 = lw0 c4 (CX34 ∷ Toff214 ∷ []) (Toff214 ∷ CX34 ∷ Toff213 ∷ []) tt tt Eq.refl

wl1134 : Complete 4 → ⟪ (CCZ023 ∷ Toff213 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ023 ∷ []) ⟫ʷ
wl1134 c4 = lw4 c4 (CCZ023 ∷ Toff213 ∷ CCZ013 ∷ []) (Toff213 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl1135 : Complete 4 → ⟪ (CX13 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX13 ∷ []) ⟫ʷ
wl1135 c4 = lw0 c4 (CX13 ∷ Toff214 ∷ []) (Toff214 ∷ CX13 ∷ []) tt tt Eq.refl

wl1136 : Complete 4 → ⟪ (CX34 ∷ Toff213 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ []) ⟫ʷ
wl1136 c4 = lw0 c4 (CX34 ∷ Toff213 ∷ Toff213 ∷ []) (CX34 ∷ []) tt tt Eq.refl

wl1137 : Complete 4 → ⟪ (Sw34 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw34 ∷ []) ⟫ʷ
wl1137 c4 = lw0 c4 (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) tt tt Eq.refl

wl1138 : Complete 4 → ⟪ (Sw34 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw34 ∷ []) ⟫ʷ
wl1138 c4 = lw0 c4 (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ []) tt tt Eq.refl

wl1139 : Complete 4 → ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK41 ∷ []) ⟫ʷ
wl1139 c4 = lw0 c4 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK41 ∷ []) tt tt Eq.refl
