------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WL01 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0001 : Complete 4 → ⟪ (CS03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS03 ∷ []) ⟫ʷ
wl0001 c4 = lw4 c4 (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) tt tt Eq.refl

wl0002 : Complete 4 → ⟪ (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) ⟫ʷ
wl0002 c4 = lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl

wl0003 : Complete 4 → ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0003 c4 = lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl

wl0004 : Complete 4 → ⟪ (Sw34 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0004 c4 = lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl

wl0005 : Complete 4 → ⟪ (CS24 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS14 ∷ []) ⟫ʷ
wl0005 c4 = lw0 c4 (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) tt tt Eq.refl

wl0006 : Complete 4 → ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0006 c4 = lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl

wl0007 : Complete 4 → ⟪ (CS24⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0007 c4 = lw0 c4 (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0008 : Complete 4 → ⟪ (CS34 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS24 ∷ []) ⟫ʷ
wl0008 c4 = lw0 c4 (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) tt tt Eq.refl

wl0009 : Complete 4 → ⟪ (CS34⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0009 c4 = lw0 c4 (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0010 : Complete 4 → ⟪ (CX03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX03 ∷ []) ⟫ʷ
wl0010 c4 = lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl

wl0011 : Complete 4 → ⟪ (CS24 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS34 ∷ []) ⟫ʷ
wl0011 c4 = lw0 c4 (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) tt tt Eq.refl

wl0012 : Complete 4 → ⟪ (CS24⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0012 c4 = lw0 c4 (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0013 : Complete 4 → ⟪ (CS14 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS24 ∷ []) ⟫ʷ
wl0013 c4 = lw0 c4 (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) tt tt Eq.refl

wl0014 : Complete 4 → ⟪ (CS14⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0014 c4 = lw0 c4 (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0015 : Complete 4 → ⟪ (CS03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13 ∷ []) ⟫ʷ
wl0015 c4 = lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl

wl0016 : Complete 4 → ⟪ (CX03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ []) ⟫ʷ
wl0016 c4 = lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl

wl0017 : Complete 4 → ⟪ (CS14 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS14 ∷ []) ⟫ʷ
wl0017 c4 = lw0 c4 (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) tt tt Eq.refl

wl0018 : Complete 4 → ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0018 c4 = lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl

wl0019 : Complete 4 → ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ
wl0019 c4 = lw4 c4 (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) tt tt Eq.refl

wl0020 : Complete 4 → ⟪ (CX24 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX34 ∷ []) ⟫ʷ
wl0020 c4 = lw0 c4 (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) tt tt Eq.refl

wl0021 : Complete 4 → ⟪ (CX34 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX24 ∷ []) ⟫ʷ
wl0021 c4 = lw0 c4 (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) tt tt Eq.refl

wl0022 : Complete 4 → ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ
wl0022 c4 = lw4 c4 (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) tt tt Eq.refl

wl0023 : Complete 4 → ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0023 c4 = lw4 c4 (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0024 : Complete 4 → ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ
wl0024 c4 = lw4 c4 (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) tt tt Eq.refl

wl0025 : Complete 4 → ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wl0025 c4 = lw4 c4 (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) tt tt Eq.refl

wl0026 : Complete 4 → ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ
wl0026 c4 = lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl

wl0027 : Complete 4 → ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wl0027 c4 = lw4 c4 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl

wl0028 : Complete 4 → ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ
wl0028 c4 = lw4 c4 (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wl0029 : Complete 4 → ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0029 c4 = lw4 c4 (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0030 : Complete 4 → ⟪ (CCZ023 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ123 ∷ []) ⟫ʷ
wl0030 c4 = lw4 c4 (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0031 : Complete 4 → ⟪ (Sw01 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Sw01 ∷ []) ⟫ʷ
wl0031 c4 = lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0032 : Complete 4 → ⟪ (CZ14 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ24 ∷ []) ⟫ʷ
wl0032 c4 = lw0 c4 (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) tt tt Eq.refl

wl0033 : Complete 4 → ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ
wl0033 c4 = lw4 c4 (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) tt tt Eq.refl

wl0034 : Complete 4 → ⟪ (CZ24 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CZ34 ∷ []) ⟫ʷ
wl0034 c4 = lw0 c4 (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) tt tt Eq.refl

wl0035 : Complete 4 → ⟪ (CZ34 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CZ24 ∷ []) ⟫ʷ
wl0035 c4 = lw0 c4 (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) tt tt Eq.refl

wl0036 : Complete 4 → ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ
wl0036 c4 = lw4 c4 (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0037 : Complete 4 → ⟪ (CCZ134 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ234 ∷ []) ⟫ʷ
wl0037 c4 = lw0 c4 (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0038 : Complete 4 → ⟪ (Sw12 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw12 ∷ []) ⟫ʷ
wl0038 c4 = lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0039 : Complete 4 → ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ
wl0039 c4 = lw4 c4 (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl

wl0040 : Complete 4 → ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ
wl0040 c4 = lw4 c4 (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) tt tt Eq.refl

wl0041 : Complete 4 → ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wl0041 c4 = lw4 c4 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl

wl0042 : Complete 4 → ⟪ (CS03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0042 c4 = lw4 c4 (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0043 : Complete 4 → ⟪ (CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0043 c4 = lw4 c4 (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0044 : Complete 4 → ⟪ (CCZ234 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ134 ∷ []) ⟫ʷ
wl0044 c4 = lw0 c4 (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0045 : Complete 4 → ⟪ (Sw12 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sw12 ∷ []) ⟫ʷ
wl0045 c4 = lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0046 : Complete 4 → ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ
wl0046 c4 = lw4 c4 (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) tt tt Eq.refl

wl0047 : Complete 4 → ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ
wl0047 c4 = lw4 c4 (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) tt tt Eq.refl

wl0048 : Complete 4 → ⟪ (CS14⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0048 c4 = lw0 c4 (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0049 : Complete 4 → ⟪ (CZ03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ13 ∷ []) ⟫ʷ
wl0049 c4 = lw4 c4 (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0050 : Complete 4 → ⟪ (CX14 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX24 ∷ []) ⟫ʷ
wl0050 c4 = lw0 c4 (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ []) tt tt Eq.refl

wl0051 : Complete 4 → ⟪ (CX24 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX14 ∷ []) ⟫ʷ
wl0051 c4 = lw0 c4 (CX24 ∷ Sw12 ∷ []) (Sw12 ∷ CX14 ∷ []) tt tt Eq.refl

wl0052 : Complete 4 → ⟪ (Sw01 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw01 ∷ []) ⟫ʷ
wl0052 c4 = lw4 c4 (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0053 : Complete 4 → ⟪ (CZ24 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ14 ∷ []) ⟫ʷ
wl0053 c4 = lw0 c4 (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) tt tt Eq.refl

wl0054 : Complete 4 → ⟪ (Sw12 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw12 ∷ []) ⟫ʷ
wl0054 c4 = lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0055 : Complete 4 → ⟪ (Sw23 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ Sw23 ∷ []) ⟫ʷ
wl0055 c4 = lw0 c4 (Sw23 ∷ Sw34 ∷ []) (Sw24 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0056 : Complete 4 → ⟪ (Sw23 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Sw23 ∷ []) ⟫ʷ
wl0056 c4 = lw0 c4 (Sw23 ∷ Sw24 ∷ []) (Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0057 : Complete 4 → ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ
wl0057 c4 = lw4 c4 (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) tt tt Eq.refl

wl0058 : Complete 4 → ⟪ (CX42 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX43 ∷ []) ⟫ʷ
wl0058 c4 = lw0 c4 (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) tt tt Eq.refl

wl0059 : Complete 4 → ⟪ (CX43 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX42 ∷ []) ⟫ʷ
wl0059 c4 = lw0 c4 (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) tt tt Eq.refl

wl0060 : Complete 4 → ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ
wl0060 c4 = lw4 c4 (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) tt tt Eq.refl

wl0061 : Complete 4 → ⟪ (CZ23 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CZ23 ∷ []) ⟫ʷ
wl0061 c4 = lw0 c4 (CZ23 ∷ Sw14 ∷ []) (Sw14 ∷ CZ23 ∷ []) tt tt Eq.refl

wl0062 : Complete 4 → ⟪ (CZ14 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CZ14 ∷ []) ⟫ʷ
wl0062 c4 = lw0 c4 (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) tt tt Eq.refl

wl0063 : Complete 4 → ⟪ (Sw01 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw01 ∷ []) ⟫ʷ
wl0063 c4 = lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0064 : Complete 4 → ⟪ (K3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K2 ∷ []) ⟫ʷ
wl0064 c4 = lw4 c4 (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) tt tt Eq.refl

wl0065 : Complete 4 → ⟪ (K4 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ K3 ∷ []) ⟫ʷ
wl0065 c4 = lw0 c4 (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) tt tt Eq.refl

wl0066 : Complete 4 → ⟪ (K3 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ K4 ∷ []) ⟫ʷ
wl0066 c4 = lw0 c4 (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) tt tt Eq.refl

wl0067 : Complete 4 → ⟪ (K2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ K3 ∷ []) ⟫ʷ
wl0067 c4 = lw4 c4 (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) tt tt Eq.refl

wl0068 : Complete 4 → ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wl0068 c4 = lw4 c4 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) tt tt Eq.refl

wl0069 : Complete 4 → ⟪ (CX41 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX42 ∷ []) ⟫ʷ
wl0069 c4 = lw0 c4 (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) tt tt Eq.refl

wl0070 : Complete 4 → ⟪ (CX41 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX41 ∷ []) ⟫ʷ
wl0070 c4 = lw0 c4 (CX41 ∷ Sw23 ∷ []) (Sw23 ∷ CX41 ∷ []) tt tt Eq.refl

wl0071 : Complete 4 → ⟪ (CX14 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX14 ∷ []) ⟫ʷ
wl0071 c4 = lw0 c4 (CX14 ∷ Sw23 ∷ []) (Sw23 ∷ CX14 ∷ []) tt tt Eq.refl

wl0072 : Complete 4 → ⟪ (Sw12 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ Sw12 ∷ []) ⟫ʷ
wl0072 c4 = lw0 c4 (Sw12 ∷ Sw24 ∷ []) (Sw14 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0073 : Complete 4 → ⟪ (K1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K2 ∷ []) ⟫ʷ
wl0073 c4 = lw4 c4 (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) tt tt Eq.refl

wl0074 : Complete 4 → ⟪ (Sw14 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw14 ∷ []) ⟫ʷ
wl0074 c4 = lw0 c4 (Sw14 ∷ Sw23 ∷ []) (Sw23 ∷ Sw14 ∷ []) tt tt Eq.refl

wl0075 : Complete 4 → ⟪ (Sw12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw13 ∷ Sw12 ∷ []) ⟫ʷ
wl0075 c4 = lw4 c4 (Sw12 ∷ Sw23 ∷ []) (Sw13 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0076 : Complete 4 → ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ
wl0076 c4 = lw4 c4 (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0077 : Complete 4 → ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ
wl0077 c4 = lw4 c4 (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) tt tt Eq.refl

wl0078 : Complete 4 → ⟪ (CX30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ []) ⟫ʷ
wl0078 c4 = lw4 c4 (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) tt tt Eq.refl

wl0079 : Complete 4 → ⟪ (CZ03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ03 ∷ []) ⟫ʷ
wl0079 c4 = lw4 c4 (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) tt tt Eq.refl

wl0080 : Complete 4 → ⟪ (CX30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX30 ∷ []) ⟫ʷ
wl0080 c4 = lw4 c4 (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) tt tt Eq.refl

wl0081 : Complete 4 → ⟪ (CK30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK31 ∷ []) ⟫ʷ
wl0081 c4 = lw4 c4 (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) tt tt Eq.refl

wl0082 : Complete 4 → ⟪ (CK30⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK31⁻ ∷ []) ⟫ʷ
wl0082 c4 = lw4 c4 (CK30⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK31⁻ ∷ []) tt tt Eq.refl

wl0083 : Complete 4 → ⟪ (Sw12 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Sw12 ∷ []) ⟫ʷ
wl0083 c4 = lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0084 : Complete 4 → ⟪ (Sw12 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sw12 ∷ []) ⟫ʷ
wl0084 c4 = lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0085 : Complete 4 → ⟪ (Sw12 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw12 ∷ []) ⟫ʷ
wl0085 c4 = lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0086 : Complete 4 → ⟪ (CZ12 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CZ12 ∷ []) ⟫ʷ
wl0086 c4 = lw4 c4 (CZ12 ∷ Sw03 ∷ []) (Sw03 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0087 : Complete 4 → ⟪ (CK41 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK42 ∷ []) ⟫ʷ
wl0087 c4 = lw0 c4 (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) tt tt Eq.refl

wl0088 : Complete 4 → ⟪ (CK30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK30 ∷ []) ⟫ʷ
wl0088 c4 = lw4 c4 (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) tt tt Eq.refl

wl0089 : Complete 4 → ⟪ (CX42 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX41 ∷ []) ⟫ʷ
wl0089 c4 = lw0 c4 (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ []) tt tt Eq.refl

wl0090 : Complete 4 → ⟪ (CK42 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CK43 ∷ []) ⟫ʷ
wl0090 c4 = lw0 c4 (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) tt tt Eq.refl

wl0091 : Complete 4 → ⟪ (CK43 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CK42 ∷ []) ⟫ʷ
wl0091 c4 = lw0 c4 (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) tt tt Eq.refl

wl0092 : Complete 4 → ⟪ (CK42 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK41 ∷ []) ⟫ʷ
wl0092 c4 = lw0 c4 (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) tt tt Eq.refl

wl0093 : Complete 4 → ⟪ (Sw12 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw24 ∷ Sw12 ∷ []) ⟫ʷ
wl0093 c4 = lw0 c4 (Sw12 ∷ Sw14 ∷ []) (Sw24 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0094 : Complete 4 → ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ
wl0094 c4 = lw4 c4 (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ []) tt tt Eq.refl

wl0095 : Complete 4 → ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ
wl0095 c4 = lw4 c4 (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) tt tt Eq.refl

wl0096 : Complete 4 → ⟪ (Sw12 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ []) ⟫ʷ
wl0096 c4 = lw4 c4 (Sw12 ∷ Sw13 ∷ []) (Sw23 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0097 : Complete 4 → ⟪ (Sw03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw03 ∷ []) ⟫ʷ
wl0097 c4 = lw4 c4 (Sw03 ∷ Sw12 ∷ []) (Sw12 ∷ Sw03 ∷ []) tt tt Eq.refl

wl0098 : Complete 4 → ⟪ (Sw01 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ Sw01 ∷ []) ⟫ʷ
wl0098 c4 = lw4 c4 (Sw01 ∷ Sw13 ∷ []) (Sw03 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0099 : Complete 4 → ⟪ (CK41 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CK41 ∷ []) ⟫ʷ
wl0099 c4 = lw0 c4 (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) tt tt Eq.refl

wl0100 : Complete 4 → ⟪ (Sw01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw02 ∷ Sw01 ∷ []) ⟫ʷ
wl0100 c4 = lw4 c4 (Sw01 ∷ Sw12 ∷ []) (Sw02 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0101 : Complete 4 → ⟪ (CCZ012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ012 ∷ []) ⟫ʷ
wl0101 c4 = lw4 c4 (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0102 : Complete 4 → ⟪ (Sw12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw12 ∷ []) ⟫ʷ
wl0102 c4 = lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0103 : Complete 4 → ⟪ (CCZ012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ012 ∷ []) ⟫ʷ
wl0103 c4 = lw4 c4 (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0104 : Complete 4 → ⟪ (Sw01 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Sw01 ∷ []) ⟫ʷ
wl0104 c4 = lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0105 : Complete 4 → ⟪ (CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0105 c4 = lw4 c4 (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0106 : Complete 4 → ⟪ (CS13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS03 ∷ []) ⟫ʷ
wl0106 c4 = lw4 c4 (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) tt tt Eq.refl

wl0107 : Complete 4 → ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ
wl0107 c4 = lw4 c4 (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) tt tt Eq.refl

wl0108 : Complete 4 → ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wl0108 c4 = lw4 c4 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl

wl0109 : Complete 4 → ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ
wl0109 c4 = lw4 c4 (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) tt tt Eq.refl

wl0110 : Complete 4 → ⟪ (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wl0110 c4 = lw4 c4 (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) tt tt Eq.refl

wl0111 : Complete 4 → ⟪ (Sw23 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sw23 ∷ []) ⟫ʷ
wl0111 c4 = lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0112 : Complete 4 → ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0112 c4 = lw4 c4 (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0113 : Complete 4 → ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ
wl0113 c4 = lw4 c4 (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) tt tt Eq.refl

wl0114 : Complete 4 → ⟪ (CZ12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ12 ∷ []) ⟫ʷ
wl0114 c4 = lw4 c4 (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0115 : Complete 4 → ⟪ (CX10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX01 ∷ []) ⟫ʷ
wl0115 c4 = lw4 c4 (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) tt tt Eq.refl

wl0116 : Complete 4 → ⟪ (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wl0116 c4 = lw4 c4 (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) tt tt Eq.refl

wl0117 : Complete 4 → ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ
wl0117 c4 = lw4 c4 (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) tt tt Eq.refl

wl0118 : Complete 4 → ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ Sw01 ∷ []) ⟫ʷ
wl0118 c4 = lw4 c4 (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0119 : Complete 4 → ⟪ (Sw12 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ Sw12 ∷ []) ⟫ʷ
wl0119 c4 = lw4 c4 (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0120 : Complete 4 → ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wl0120 c4 = lw4 c4 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ []) tt tt Eq.refl

wl0121 : Complete 4 → ⟪ (Sw01 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw01 ∷ []) ⟫ʷ
wl0121 c4 = lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0122 : Complete 4 → ⟪ (CCZ124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ124 ∷ []) ⟫ʷ
wl0122 c4 = lw0 c4 (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0123 : Complete 4 → ⟪ (Sw12 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw12 ∷ []) ⟫ʷ
wl0123 c4 = lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0124 : Complete 4 → ⟪ (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wl0124 c4 = lw4 c4 (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) tt tt Eq.refl

wl0125 : Complete 4 → ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) ⟫ʷ
wl0125 c4 = lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) tt tt Eq.refl

wl0126 : Complete 4 → ⟪ (Sw23 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw23 ∷ []) ⟫ʷ
wl0126 c4 = lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0127 : Complete 4 → ⟪ (Sw12 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw12 ∷ []) ⟫ʷ
wl0127 c4 = lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0128 : Complete 4 → ⟪ (CS34⁻ ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0128 c4 = lw0 c4 (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0129 : Complete 4 → ⟪ (CS34 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CS34 ∷ []) ⟫ʷ
wl0129 c4 = lw0 c4 (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) tt tt Eq.refl

wl0130 : Complete 4 → ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) ⟫ʷ
wl0130 c4 = lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl

wl0131 : Complete 4 → ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wl0131 c4 = lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) tt tt Eq.refl

wl0132 : Complete 4 → ⟪ (CCZ023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ023 ∷ []) ⟫ʷ
wl0132 c4 = lw4 c4 (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0133 : Complete 4 → ⟪ (Sw23 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw23 ∷ []) ⟫ʷ
wl0133 c4 = lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0134 : Complete 4 → ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wl0134 c4 = lw4 c4 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl

wl0135 : Complete 4 → ⟪ (CCZ123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ023 ∷ []) ⟫ʷ
wl0135 c4 = lw4 c4 (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0136 : Complete 4 → ⟪ (Sw01 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw01 ∷ []) ⟫ʷ
wl0136 c4 = lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0137 : Complete 4 → ⟪ (CCZ123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ123 ∷ []) ⟫ʷ
wl0137 c4 = lw4 c4 (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0138 : Complete 4 → ⟪ (Sw12 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw12 ∷ []) ⟫ʷ
wl0138 c4 = lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0139 : Complete 4 → ⟪ (CCZ123 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ123 ∷ []) ⟫ʷ
wl0139 c4 = lw4 c4 (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0140 : Complete 4 → ⟪ (Sw23 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw23 ∷ []) ⟫ʷ
wl0140 c4 = lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0141 : Complete 4 → ⟪ (CCZ134 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ134 ∷ []) ⟫ʷ
wl0141 c4 = lw0 c4 (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0142 : Complete 4 → ⟪ (Sw34 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw34 ∷ []) ⟫ʷ
wl0142 c4 = lw0 c4 (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) tt tt Eq.refl

wl0143 : Complete 4 → ⟪ (Sw23 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw23 ∷ []) ⟫ʷ
wl0143 c4 = lw4 c4 (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0144 : Complete 4 → ⟪ (Sw12 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw12 ∷ []) ⟫ʷ
wl0144 c4 = lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0145 : Complete 4 → ⟪ (CZ12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ02 ∷ []) ⟫ʷ
wl0145 c4 = lw4 c4 (CZ12 ∷ Sw01 ∷ []) (Sw01 ∷ CZ02 ∷ []) tt tt Eq.refl

wl0146 : Complete 4 → ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ
wl0146 c4 = lw4 c4 (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) tt tt Eq.refl

wl0147 : Complete 4 → ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0147 c4 = lw4 c4 (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0148 : Complete 4 → ⟪ (Sw01 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ Sw01 ∷ []) ⟫ʷ
wl0148 c4 = lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl

wl0149 : Complete 4 → ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wl0149 c4 = lw4 c4 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) tt tt Eq.refl

wl0150 : Complete 4 → ⟪ (Sw12 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw12 ∷ []) ⟫ʷ
wl0150 c4 = lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0151 : Complete 4 → ⟪ (CZ13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ03 ∷ []) ⟫ʷ
wl0151 c4 = lw4 c4 (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) tt tt Eq.refl

wl0152 : Complete 4 → ⟪ (CK03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK13 ∷ []) ⟫ʷ
wl0152 c4 = lw4 c4 (CK03 ∷ Sw01 ∷ []) (Sw01 ∷ CK13 ∷ []) tt tt Eq.refl

wl0153 : Complete 4 → ⟪ (CK02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK12 ∷ []) ⟫ʷ
wl0153 c4 = lw4 c4 (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) tt tt Eq.refl

wl0154 : Complete 4 → ⟪ (CK03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK03 ∷ []) ⟫ʷ
wl0154 c4 = lw4 c4 (CK03 ∷ Sw12 ∷ []) (Sw12 ∷ CK03 ∷ []) tt tt Eq.refl

wl0155 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) ⟫ʷ
wl0155 c4 = lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl

wl0156 : Complete 4 → ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wl0156 c4 = lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl

wl0157 : Complete 4 → ⟪ (K0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0157 c4 = lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl

wl0158 : Complete 4 → ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
wl0158 c4 = lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0159 : Complete 4 → ⟪ (S0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0159 c4 = lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl

wl0160 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) ⟫ʷ
wl0160 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0161 : Complete 4 → ⟪ (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wl0161 c4 = lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl

wl0162 : Complete 4 → ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0162 c4 = lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl

wl0163 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
wl0163 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0164 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wl0164 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0165 : Complete 4 → ⟪ (CCZ012 ∷ X2 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CCZ012 ∷ []) ⟫ʷ
wl0165 c4 = lw4 c4 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (X2 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0166 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) ⟫ʷ
wl0166 c4 = lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) tt tt Eq.refl

wl0167 : Complete 4 → ⟪ (CCZ012 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ012 ∷ []) ⟫ʷ
wl0167 c4 = lw4 c4 (CCZ012 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0168 : Complete 4 → ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
wl0168 c4 = lw4 c4 (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0169 : Complete 4 → ⟪ (X2 ∷ CZ01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wl0169 c4 = lw4 c4 (X2 ∷ CZ01 ∷ CZ01 ∷ []) (X2 ∷ []) tt tt Eq.refl

wl0170 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CCZ134 ∷ X2 ∷ []) ⟫ʷ
wl0170 c4 = lw0 c4 (CCZ134 ∷ []) (X2 ∷ CCZ134 ∷ X2 ∷ []) tt tt Eq.refl

wl0171 : Complete 4 → ⟪ (CCZ123 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ123 ∷ []) ⟫ʷ
wl0171 c4 = lw4 c4 (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0172 : Complete 4 → ⟪ (CCZ123 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0172 c4 = lw0 c4 (CCZ123 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0173 : Complete 4 → ⟪ (CCZ123 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ123 ∷ []) ⟫ʷ
wl0173 c4 = lw0 c4 (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0174 : Complete 4 → ⟪ (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wl0174 c4 = lw4 c4 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (Toff213 ∷ []) tt tt Eq.refl

wl0175 : Complete 4 → ⟪ (K2⁻ ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0175 c4 = lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl

wl0176 : Complete 4 → ⟪ (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
wl0176 c4 = lw4 c4 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0177 : Complete 4 → ⟪ (CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wl0177 c4 = lw4 c4 (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0178 : Complete 4 → ⟪ (CS13⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0178 c4 = lw4 c4 (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0179 : Complete 4 → ⟪ (S2⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0179 c4 = lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl

wl0180 : Complete 4 → ⟪ (Toff213 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0180 c4 = lw4 c4 (Toff213 ∷ Toff213 ∷ []) [] tt tt Eq.refl

wl0181 : Complete 4 → ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0181 c4 = lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl

wl0182 : Complete 4 → ⟪ (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wl0182 c4 = lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl

wl0183 : Complete 4 → ⟪ (CZ02 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) ⟫ʷ
wl0183 c4 = lw4 c4 (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0184 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) ⟫ʷ
wl0184 c4 = lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) tt tt Eq.refl

wl0185 : Complete 4 → ⟪ (X4 ∷ CZ02 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wl0185 c4 = lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl

wl0186 : Complete 4 → ⟪ (CCZ013 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ013 ∷ []) ⟫ʷ
wl0186 c4 = lw4 c4 (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0187 : Complete 4 → ⟪ (Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX13 ∷ Toff314 ∷ []) ⟫ʷ
wl0187 c4 = lw0 c4 (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0188 : Complete 4 → ⟪ (CS03 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) ⟫ʷ
wl0188 c4 = lw4 c4 (CS03 ∷ CX13 ∷ []) (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) tt tt Eq.refl

wl0189 : Complete 4 → ⟪ (CX13 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX13 ∷ []) ⟫ʷ
wl0189 c4 = lw0 c4 (CX13 ∷ Toff314 ∷ []) (Toff314 ∷ CX13 ∷ []) tt tt Eq.refl

wl0190 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl0190 c4 = lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl0191 : Complete 4 → ⟪ (CS03⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0191 c4 = lw4 c4 (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0192 : Complete 4 → ⟪ (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff213 ∷ []) ⟫ʷ
wl0192 c4 = lw0 c4 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0193 : Complete 4 → ⟪ (CS01 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS01 ∷ []) ⟫ʷ
wl0193 c4 = lw4 c4 (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) tt tt Eq.refl

wl0194 : Complete 4 → ⟪ (CS14⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0194 c4 = lw0 c4 (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0195 : Complete 4 → ⟪ (CS14 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS14 ∷ []) ⟫ʷ
wl0195 c4 = lw0 c4 (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) tt tt Eq.refl

wl0196 : Complete 4 → ⟪ (CS03 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS03 ∷ []) ⟫ʷ
wl0196 c4 = lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl

wl0197 : Complete 4 → ⟪ (Toff213 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff213 ∷ []) ⟫ʷ
wl0197 c4 = lw0 c4 (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0198 : Complete 4 → ⟪ (Toff214 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl0198 c4 = lw0 c4 (Toff214 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl0199 : Complete 4 → ⟪ (CCZ023 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ023 ∷ []) ⟫ʷ
wl0199 c4 = lw4 c4 (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0200 : Complete 4 → ⟪ (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ []) ⟫ʷ
wl0200 c4 = lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl

wl0201 : Complete 4 → ⟪ (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
wl0201 c4 = lw4 c4 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0202 : Complete 4 → ⟪ (CS14⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wl0202 c4 = lw0 c4 (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0203 : Complete 4 → ⟪ (Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0203 c4 = lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl

wl0204 : Complete 4 → ⟪ (CCZ023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0204 c4 = lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl

wl0205 : Complete 4 → ⟪ (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
wl0205 c4 = lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl

wl0206 : Complete 4 → ⟪ (CZ01 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) ⟫ʷ
wl0206 c4 = lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0207 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wl0207 c4 = lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl

wl0208 : Complete 4 → ⟪ (X4 ∷ CZ01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ []) ⟫ʷ
wl0208 c4 = lw2 c4 (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) tt tt Eq.refl

wl0209 : Complete 4 → ⟪ (CCZ123 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ123 ∷ []) ⟫ʷ
wl0209 c4 = lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0210 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ X4 ∷ []) ⟫ʷ
wl0210 c4 = lw0 c4 (CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ []) tt tt Eq.refl

wl0211 : Complete 4 → ⟪ (Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ
wl0211 c4 = lw0 c4 (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0212 : Complete 4 → ⟪ (CS13 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) ⟫ʷ
wl0212 c4 = lw4 c4 (CS13 ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) tt tt Eq.refl

wl0213 : Complete 4 → ⟪ (CX23 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX23 ∷ []) ⟫ʷ
wl0213 c4 = lw0 c4 (CX23 ∷ Toff324 ∷ []) (Toff324 ∷ CX23 ∷ []) tt tt Eq.refl

wl0214 : Complete 4 → ⟪ (CS12 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS12 ∷ []) ⟫ʷ
wl0214 c4 = lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl

wl0215 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ123 ∷ []) ⟫ʷ
wl0215 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0216 : Complete 4 → ⟪ (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX23 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0216 c4 = lw0 c4 (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (X4 ∷ CX23 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0217 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl0217 c4 = lw0 c4 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl0218 : Complete 4 → ⟪ (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) ⟫ʷ
wl0218 c4 = lw0 c4 (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0219 : Complete 4 → ⟪ (CS13⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0219 c4 = lw4 c4 (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0220 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) ⟫ʷ
wl0220 c4 = lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) tt tt Eq.refl

wl0221 : Complete 4 → ⟪ (CS12 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS12 ∷ []) ⟫ʷ
wl0221 c4 = lw4 c4 (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) tt tt Eq.refl

wl0222 : Complete 4 → ⟪ (CS13 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS13 ∷ []) ⟫ʷ
wl0222 c4 = lw4 c4 (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) tt tt Eq.refl

wl0223 : Complete 4 → ⟪ (CCZ124 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS12 ∷ CS13 ∷ []) ⟫ʷ
wl0223 c4 = lw0 c4 (CCZ124 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ []) tt tt Eq.refl

wl0224 : Complete 4 → ⟪ (CS12 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0224 c4 = lw0 c4 (CS12 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0225 : Complete 4 → ⟪ (CCZ013 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ013 ∷ []) ⟫ʷ
wl0225 c4 = lw4 c4 (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0226 : Complete 4 → ⟪ (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
wl0226 c4 = lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl

wl0227 : Complete 4 → ⟪ (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
wl0227 c4 = lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0228 : Complete 4 → ⟪ (CS13⁻ ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wl0228 c4 = lw0 c4 (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0229 : Complete 4 → ⟪ (Toff013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0229 c4 = lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl

wl0230 : Complete 4 → ⟪ (CCZ013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0230 c4 = lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl

wl0231 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) ⟫ʷ
wl0231 c4 = lw4 c4 (CCZ013 ∷ []) (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) tt tt Eq.refl

wl0232 : Complete 4 → ⟪ (CZ02 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) ⟫ʷ
wl0232 c4 = lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0233 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) ⟫ʷ
wl0233 c4 = lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) tt tt Eq.refl

wl0234 : Complete 4 → ⟪ (CCZ123 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ123 ∷ []) ⟫ʷ
wl0234 c4 = lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0235 : Complete 4 → ⟪ (Toff134 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX31 ∷ Toff134 ∷ []) ⟫ʷ
wl0235 c4 = lw0 c4 (Toff134 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ Toff134 ∷ []) tt tt Eq.refl

wl0236 : Complete 4 → ⟪ (CS12 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) ⟫ʷ
wl0236 c4 = lw4 c4 (CS12 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) tt tt Eq.refl

wl0237 : Complete 4 → ⟪ (CX31 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CX31 ∷ []) ⟫ʷ
wl0237 c4 = lw0 c4 (CX31 ∷ Toff134 ∷ []) (Toff134 ∷ CX31 ∷ []) tt tt Eq.refl

wl0238 : Complete 4 → ⟪ (CS23 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS23 ∷ []) ⟫ʷ
wl0238 c4 = lw0 c4 (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ []) tt tt Eq.refl

wl0239 : Complete 4 → ⟪ (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ123 ∷ []) ⟫ʷ
wl0239 c4 = lw0 c4 (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0240 : Complete 4 → ⟪ (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX31 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) ⟫ʷ
wl0240 c4 = lw0 c4 (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (X4 ∷ CX31 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0241 : Complete 4 → ⟪ (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ []) ⟫ʷ
wl0241 c4 = lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl

wl0242 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) ⟫ʷ
wl0242 c4 = lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl

wl0243 : Complete 4 → ⟪ (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) ⟫ʷ
wl0243 c4 = lw0 c4 (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0244 : Complete 4 → ⟪ (CS12⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0244 c4 = lw4 c4 (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0245 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) ⟫ʷ
wl0245 c4 = lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl

wl0246 : Complete 4 → ⟪ (CS23 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS23 ∷ []) ⟫ʷ
wl0246 c4 = lw4 c4 (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) tt tt Eq.refl
