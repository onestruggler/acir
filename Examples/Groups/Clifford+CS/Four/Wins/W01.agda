------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation, through the tables of Four.Lits),
-- stated over the macro letters as Four/D uses it.  Written by
-- scratchpad/four/winlib4.py, restated by winmac4.py and wintable4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W01 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)

wn00001 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ
wn00001 b = lw0 b [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00002 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX20 ∷ CX20 ∷ []) ⟫ʷ
wn00002 b = lw3 b [] (CX20 ∷ CX20 ∷ []) tt tt Eq.refl
wn00003 : Base 3 → ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00003 b = lw0 b (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl
wn00004 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ
wn00004 b = lw3 b [] (CCZ012 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00005 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ
wn00005 b = lw3 b [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00006 : Base 3 → ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ
wn00006 b = lw3 b (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) tt tt Eq.refl
wn00007 : Base 3 → ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ
wn00007 b = lw3 b (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) tt tt Eq.refl
wn00008 : Base 3 → ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ
wn00008 b = lw3 b (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) tt tt Eq.refl
wn00009 : Base 3 → ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00009 b = lw3 b (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00010 : Base 3 → ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ
wn00010 b = lw3 b (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) tt tt Eq.refl
wn00011 : Base 3 → ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00011 b = lw3 b (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl
wn00012 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ
wn00012 b = lw3 b [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00013 : Base 3 → ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ
wn00013 b = lw0 b (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) tt tt Eq.refl
wn00014 : Base 3 → ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00014 b = lw3 b (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl
wn00015 : Base 3 → ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00015 b = lw3 b (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00016 : Base 3 → ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ
wn00016 b = lw3 b (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) tt tt Eq.refl
wn00017 : Base 3 → ⟪ (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00017 b = lw3 b (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl
wn00018 : Base 3 → ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ
wn00018 b = lw3 b (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00019 : Base 3 → ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00019 b = lw3 b (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00020 : Base 3 → ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ
wn00020 b = lw0 b (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00021 : Base 3 → ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00021 b = lw0 b (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00022 : Base 3 → ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wn00022 b = lw0 b (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00023 : Base 3 → ⟪ (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ
wn00023 b = lw0 b (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00024 : Base 3 → ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ
wn00024 b = lw3 b (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00025 : Base 3 → ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ
wn00025 b = lw3 b (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00026 : Base 3 → ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00026 b = lw0 b (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00027 : Base 3 → ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ
wn00027 b = lw3 b (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00028 : Base 3 → ⟪ (Sw01 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sw01 ∷ []) ⟫ʷ
wn00028 b = lw3 b (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00029 : Base 3 → ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00029 b = lw3 b (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00030 : Base 3 → ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ
wn00030 b = lw3 b (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00031 : Base 3 → ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00031 b = lw3 b (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl
wn00032 : Base 3 → ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00032 b = lw3 b (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl
wn00033 : Base 3 → ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00033 b = lw0 b (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl
wn00034 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00034 b = lw0 b (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00035 : Base 3 → ⟪ (CS12 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CS12 ∷ []) ⟫ʷ
wn00035 b = lw3 b (CS12 ∷ CX20 ∷ []) (CX20 ∷ CS12 ∷ []) tt tt Eq.refl
wn00036 : Base 3 → ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ
wn00036 b = lw0 b (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) tt tt Eq.refl
wn00037 : Base 3 → ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ
wn00037 b = lw0 b (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) tt tt Eq.refl
wn00038 : Base 3 → ⟪ (CS23⁻ ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00038 b = lw0 b (CS23⁻ ∷ CX31 ∷ []) (CX31 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn00039 : Base 3 → ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ
wn00039 b = lw3 b (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00040 : Base 3 → ⟪ (CS23 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23 ∷ []) ⟫ʷ
wn00040 b = lw0 b (CS23 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ []) tt tt Eq.refl
wn00041 : Base 3 → ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00041 b = lw0 b (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn00042 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ
wn00042 b = lw0 b [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl
wn00043 : Base 3 → ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00043 b = lw3 b (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl
wn00044 : Base 3 → ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ
wn00044 b = lw0 b (CX23 ∷ Sw23 ∷ []) (Sw23 ∷ CX32 ∷ []) tt tt Eq.refl
wn00045 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ
wn00045 b = lw3 b [] (Toff012 ∷ Toff012 ∷ []) tt tt Eq.refl
wn00046 : Base 3 → ⟪ (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00046 b = lw3 b (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) tt tt Eq.refl
wn00047 : Base 3 → ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00047 b = lw0 b (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) tt tt Eq.refl
wn00048 : Base 3 → ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ
wn00048 b = lw0 b (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00049 : Base 3 → ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ
wn00049 b = lw0 b (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00050 : Base 3 → ⟪ (Sw12 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Sw12 ∷ []) ⟫ʷ
wn00050 b = lw3 b (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00051 : Base 3 → ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00051 b = lw0 b (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl
wn00052 : Base 3 → ⟪ (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00052 b = lw0 b (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00053 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn00053 b = lw3 b (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn00054 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0 ∷ []) ⟫ʷ
wn00054 b = lw3 b [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl
wn00055 : Base 3 → ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00055 b = lw3 b (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl
wn00056 : Base 3 → ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00056 b = lw3 b (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) tt tt Eq.refl
wn00057 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ
wn00057 b = lw3 b (Toff012 ∷ []) (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn00058 : Base 3 → ⟪ (CX23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CX23 ∷ []) ⟫ʷ
wn00058 b = lw0 b (CX23 ∷ CX21 ∷ []) (CX21 ∷ CX23 ∷ []) tt tt Eq.refl
wn00059 : Base 3 → ⟪ (CX23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX23 ∷ []) ⟫ʷ
wn00059 b = lw0 b (CX23 ∷ CS12 ∷ []) (CS12 ∷ CX23 ∷ []) tt tt Eq.refl
wn00060 : Base 3 → ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00060 b = lw0 b (CX23 ∷ CX23 ∷ []) [] tt tt Eq.refl
wn00061 : Base 3 → ⟪ (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00061 b = lw3 b (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl
wn00062 : Base 3 → ⟪ (Sw23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Sw23 ∷ []) ⟫ʷ
wn00062 b = lw0 b (Sw23 ∷ CX21 ∷ []) (CX31 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00063 : Base 3 → ⟪ (Sw23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw23 ∷ []) ⟫ʷ
wn00063 b = lw0 b (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00064 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ
wn00064 b = lw3 b (Toff012 ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn00065 : Base 3 → ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ
wn00065 b = lw0 b (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) tt tt Eq.refl
wn00066 : Base 3 → ⟪ (CS13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00066 b = lw0 b (CS13 ∷ CX12 ∷ []) (CX12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00067 : Base 3 → ⟪ (CS12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS12 ∷ []) ⟫ʷ
wn00067 b = lw3 b (CS12 ∷ CS01 ∷ []) (CS01 ∷ CS12 ∷ []) tt tt Eq.refl
wn00068 : Base 3 → ⟪ (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00068 b = lw3 b (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl
wn00069 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX10 ∷ CX10 ∷ []) ⟫ʷ
wn00069 b = lw3 b [] (CX10 ∷ CX10 ∷ []) tt tt Eq.refl
wn00070 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ
wn00070 b = lw0 b [] (CCZ123 ∷ CCZ123 ∷ []) tt tt Eq.refl
wn00071 : Base 3 → ⟪ (Sw23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw23 ∷ []) ⟫ʷ
wn00071 b = lw0 b (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00072 : Base 3 → ⟪ (Sw23 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00072 b = lw0 b (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00073 : Base 3 → ⟪ (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00073 b = lw0 b (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00074 : Base 3 → ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ
wn00074 b = lw3 b (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) tt tt Eq.refl
wn00075 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ
wn00075 b = lw0 b (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl
wn00076 : Base 3 → ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00076 b = lw3 b (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00077 : Base 3 → ⟪ (CS23 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00077 b = lw0 b (CS23 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn00078 : Base 3 → ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ
wn00078 b = lw0 b (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) tt tt Eq.refl
wn00079 : Base 3 → ⟪ (CS12⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00079 b = lw3 b (CS12⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00080 : Base 3 → ⟪ (CS12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00080 b = lw3 b (CS12 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00081 : Base 3 → ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00081 b = lw0 b (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn00082 : Base 3 → ⟪ (CS23 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00082 b = lw0 b (CS23 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS23 ∷ []) tt tt Eq.refl
wn00083 : Base 3 → ⟪ (CX21 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CX21 ∷ []) ⟫ʷ
wn00083 b = lw3 b (CX21 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CX21 ∷ []) tt tt Eq.refl
wn00084 : Base 3 → ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00084 b = lw0 b (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) tt tt Eq.refl
wn00085 : Base 3 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ
wn00085 b = lw3 b (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl
wn00086 : Base 3 → ⟪ (CS12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00086 b = lw0 b (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00087 : Base 3 → ⟪ (CS01⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn00087 b = lw3 b (CS01⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn00088 : Base 3 → ⟪ (CS01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01 ∷ []) ⟫ʷ
wn00088 b = lw3 b (CS01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01 ∷ []) tt tt Eq.refl
wn00089 : Base 3 → ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00089 b = lw3 b (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl
wn00090 : Base 3 → ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
wn00090 b = lw3 b (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) tt tt Eq.refl
wn00091 : Base 3 → ⟪ (CS23 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS23 ∷ []) ⟫ʷ
wn00091 b = lw0 b (CS23 ∷ CS13 ∷ []) (CS13 ∷ CS23 ∷ []) tt tt Eq.refl
wn00092 : Base 3 → ⟪ (CX21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX21 ∷ []) ⟫ʷ
wn00092 b = lw3 b (CX21 ∷ CS02 ∷ []) (CS02 ∷ CX21 ∷ []) tt tt Eq.refl
wn00093 : Base 3 → ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ
wn00093 b = lw0 b (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ []) tt tt Eq.refl
wn00094 : Base 3 → ⟪ (CS01⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00094 b = lw3 b (CS01⁻ ∷ CS02 ∷ []) (CS02 ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn00095 : Base 3 → ⟪ (CS01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01 ∷ []) ⟫ʷ
wn00095 b = lw3 b (CS01 ∷ CS02 ∷ []) (CS02 ∷ CS01 ∷ []) tt tt Eq.refl
wn00096 : Base 3 → ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ
wn00096 b = lw0 b (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) tt tt Eq.refl
wn00097 : Base 3 → ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ
wn00097 b = lw0 b (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) tt tt Eq.refl
wn00098 : Base 3 → ⟪ (CZ13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CZ13 ∷ []) ⟫ʷ
wn00098 b = lw0 b (CZ13 ∷ CX12 ∷ []) (CX12 ∷ CZ13 ∷ []) tt tt Eq.refl
wn00099 : Base 3 → ⟪ (CZ12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CZ12 ∷ []) ⟫ʷ
wn00099 b = lw3 b (CZ12 ∷ CS01 ∷ []) (CS01 ∷ CZ12 ∷ []) tt tt Eq.refl
wn00100 : Base 3 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ
wn00100 b = lw3 b (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) tt tt Eq.refl
wn00101 : Base 3 → ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ
wn00101 b = lw0 b (CS13 ∷ CS12 ∷ []) (CS12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00102 : Base 3 → ⟪ (CS01⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00102 b = lw3 b (CS01⁻ ∷ CS12 ∷ []) (CS12 ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn00103 : Base 3 → ⟪ (CS01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS01 ∷ []) ⟫ʷ
wn00103 b = lw3 b (CS01 ∷ CS12 ∷ []) (CS12 ∷ CS01 ∷ []) tt tt Eq.refl
wn00104 : Base 3 → ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00104 b = lw3 b (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl
wn00105 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX32 ∷ CX32 ∷ []) ⟫ʷ
wn00105 b = lw0 b [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl
wn00106 : Base 3 → ⟪ (CS12 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS12 ∷ []) ⟫ʷ
wn00106 b = lw0 b (CS12 ∷ CZ13 ∷ []) (CZ13 ∷ CS12 ∷ []) tt tt Eq.refl
wn00107 : Base 3 → ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ
wn00107 b = lw0 b (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00108 : Base 3 → ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ
wn00108 b = lw0 b (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00109 : Base 3 → ⟪ (CS01⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00109 b = lw3 b (CS01⁻ ∷ CZ12 ∷ []) (CZ12 ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn00110 : Base 3 → ⟪ (CS01 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS01 ∷ []) ⟫ʷ
wn00110 b = lw3 b (CS01 ∷ CZ12 ∷ []) (CZ12 ∷ CS01 ∷ []) tt tt Eq.refl
wn00111 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX31 ∷ CX31 ∷ []) ⟫ʷ
wn00111 b = lw0 b [] (CX31 ∷ CX31 ∷ []) tt tt Eq.refl
wn00112 : Base 3 → ⟪ (CX20 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CX20 ∷ []) ⟫ʷ
wn00112 b = lw3 b (CX20 ∷ CX21 ∷ []) (CX21 ∷ CX20 ∷ []) tt tt Eq.refl
wn00113 : Base 3 → ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ
wn00113 b = lw0 b (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00114 : Base 3 → ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ
wn00114 b = lw0 b (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00115 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX13 ∷ CX13 ∷ []) ⟫ʷ
wn00115 b = lw0 b [] (CX13 ∷ CX13 ∷ []) tt tt Eq.refl
wn00116 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn00116 b = lw3 b [] (K0 ∷ K0⁻ ∷ []) tt tt Eq.refl
wn00117 : Base 3 → ⟪ (K0⁻ ∷ CK10 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
wn00117 b = lw3 b (K0⁻ ∷ CK10 ∷ K0 ∷ []) (CK10 ∷ []) tt tt Eq.refl
wn00118 : Base 3 → ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ
wn00118 b = lw3 b (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl
wn00119 : Base 3 → ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ
wn00119 b = lw3 b (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn00120 : Base 3 → ⟪ (K1⁻ ∷ CCZ123 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn00120 b = lw0 b (K1⁻ ∷ CCZ123 ∷ K1 ∷ []) (Toff123 ∷ []) tt tt Eq.refl
wn00121 : Base 3 → ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ
wn00121 b = lw3 b (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00122 : Base 3 → ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wn00122 b = lw3 b (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) tt tt Eq.refl
wn00123 : Base 3 → ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ
wn00123 b = lw3 b (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00124 : Base 3 → ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ Sw01 ∷ []) ⟫ʷ
wn00124 b = lw3 b (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00125 : Base 3 → ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00125 b = lw0 b (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl
wn00126 : Base 3 → ⟪ (K0⁻ ∷ CK10⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
wn00126 b = lw3 b (K0⁻ ∷ CK10⁻ ∷ K0 ∷ []) (CK10⁻ ∷ []) tt tt Eq.refl
wn00127 : Base 3 → ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ
wn00127 b = lw3 b (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) tt tt Eq.refl
wn00128 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) ⟫ʷ
wn00128 b = lw0 b (Toff123 ∷ []) (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) tt tt Eq.refl
wn00129 : Base 3 → ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00129 b = lw3 b (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00130 : Base 3 → ⟪ (Sw12 ∷ CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wn00130 b = lw0 b (Sw12 ∷ CS23 ∷ Sw12 ∷ []) (CS13 ∷ []) tt tt Eq.refl
wn00131 : Base 3 → ⟪ (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
wn00131 b = lw3 b (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) (CS01⁻ ∷ []) tt tt Eq.refl
wn00132 : Base 3 → ⟪ (Sw12 ∷ CS02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn00132 b = lw3 b (Sw12 ∷ CS02 ∷ Sw12 ∷ []) (CS01 ∷ []) tt tt Eq.refl
wn00133 : Base 3 → ⟪ (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
wn00133 b = lw3 b (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) (CK20⁻ ∷ []) tt tt Eq.refl
wn00134 : Base 3 → ⟪ (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
wn00134 b = lw3 b (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (CK20 ∷ []) tt tt Eq.refl
wn00135 : Base 3 → ⟪ (Sw23 ∷ CS13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn00135 b = lw0 b (Sw23 ∷ CS13 ∷ Sw23 ∷ []) (CS12 ∷ []) tt tt Eq.refl
wn00136 : Base 3 → ⟪ (Sw23 ∷ CX31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wn00136 b = lw0 b (Sw23 ∷ CX31 ∷ Sw23 ∷ []) (CX21 ∷ []) tt tt Eq.refl
wn00137 : Base 3 → ⟪ (CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21⁻ ∷ []) ⟫ʷ
wn00137 b = lw3 b (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) tt tt Eq.refl
wn00138 : Base 3 → ⟪ (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
wn00138 b = lw0 b (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (CK31⁻ ∷ []) tt tt Eq.refl
wn00139 : Base 3 → ⟪ (Sw01 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00139 b = lw3 b (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) tt tt Eq.refl
wn00140 : Base 3 → ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ
wn00140 b = lw3 b (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) tt tt Eq.refl
wn00141 : Base 3 → ⟪ (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
wn00141 b = lw0 b (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (CK31 ∷ []) tt tt Eq.refl
wn00142 : Base 3 → ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ
wn00142 b = lw3 b (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00143 : Base 3 → ⟪ (Sw12 ∷ CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn00143 b = lw3 b (Sw12 ∷ CS12 ∷ Sw12 ∷ []) (CS12 ∷ []) tt tt Eq.refl
wn00144 : Base 3 → ⟪ (Sw12 ∷ CX20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wn00144 b = lw3 b (Sw12 ∷ CX20 ∷ Sw12 ∷ []) (CX10 ∷ []) tt tt Eq.refl
wn00145 : Base 3 → ⟪ (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn00145 b = lw3 b (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl
wn00146 : Base 3 → ⟪ (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wn00146 b = lw3 b (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (CS02 ∷ []) tt tt Eq.refl
wn00147 : Base 3 → ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00147 b = lw3 b (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl
wn00148 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn00148 b = lw3 b [] (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) tt tt Eq.refl
wn00149 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00149 b = lw3 b (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ []) tt tt Eq.refl
wn00150 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CX20 ∷ S2 ∷ []) ⟫ʷ
wn00150 b = lw3 b (K0⁻ ∷ S0 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK20 ∷ CX20 ∷ S2 ∷ []) tt tt Eq.refl
wn00151 : Base 3 → ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ
wn00151 b = lw0 b (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00152 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) ⟫ʷ
wn00152 b = lw3 b (K0⁻ ∷ S0 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) tt tt Eq.refl
wn00153 : Base 3 → ⟪ (Sw23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00153 b = lw0 b (Sw23 ∷ S2⁻ ∷ []) (S3⁻ ∷ Sw23 ∷ []) tt tt Eq.refl
wn00154 : Base 3 → ⟪ (S3 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00154 b = lw0 b (S3 ∷ S3⁻ ∷ []) [] tt tt Eq.refl
wn00155 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ
wn00155 b = lw3 b (Toff012 ∷ []) (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) tt tt Eq.refl
wn00156 : Base 3 → ⟪ (CX31 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) ⟫ʷ
wn00156 b = lw0 b (CX31 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ []) (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) tt tt Eq.refl
wn00157 : Base 3 → ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ
wn00157 b = lw0 b (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00158 : Base 3 → ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ
wn00158 b = lw0 b (Sw12 ∷ CX23 ∷ []) (CX13 ∷ Sw12 ∷ []) tt tt Eq.refl
wn00159 : Base 3 → ⟪ (CX31 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) ⟫ʷ
wn00159 b = lw0 b (CX31 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ []) (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) tt tt Eq.refl
wn00160 : Base 3 → ⟪ (CX20 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) ⟫ʷ
wn00160 b = lw3 b (CX20 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) tt tt Eq.refl
wn00161 : Base 3 → ⟪ (CX20 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00161 b = lw3 b (CX20 ∷ CX20 ∷ []) [] tt tt Eq.refl
wn00162 : Base 3 → ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00162 b = lw3 b (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) (Toff012 ∷ []) tt tt Eq.refl
wn00163 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ
wn00163 b = lw0 b (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) tt tt Eq.refl
wn00164 : Base 3 → ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ
wn00164 b = lw3 b (CZ01 ∷ CS02 ∷ []) (CS02 ∷ CZ01 ∷ []) tt tt Eq.refl
wn00165 : Base 3 → ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ
wn00165 b = lw3 b (CZ01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CZ01 ∷ []) tt tt Eq.refl
wn00166 : Base 3 → ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00166 b = lw0 b (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl
wn00167 : Base 3 → ⟪ (CZ01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CZ01 ∷ []) ⟫ʷ
wn00167 b = lw3 b (CZ01 ∷ CS12 ∷ []) (CS12 ∷ CZ01 ∷ []) tt tt Eq.refl
wn00168 : Base 3 → ⟪ (CZ01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CZ01 ∷ []) ⟫ʷ
wn00168 b = lw3 b (CZ01 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CZ01 ∷ []) tt tt Eq.refl
wn00169 : Base 3 → ⟪ (CS12 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00169 b = lw3 b (CS12 ∷ CK10⁻ ∷ []) (CK10⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00170 : Base 3 → ⟪ (CS12⁻ ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00170 b = lw3 b (CS12⁻ ∷ CK10⁻ ∷ []) (CK10⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00171 : Base 3 → ⟪ (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00171 b = lw3 b (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) (Toff012 ∷ []) tt tt Eq.refl
wn00172 : Base 3 → ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
wn00172 b = lw3 b (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00173 : Base 3 → ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ
wn00173 b = lw0 b (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) tt tt Eq.refl
wn00174 : Base 3 → ⟪ (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00174 b = lw3 b (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) tt tt Eq.refl
wn00175 : Base 3 → ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ
wn00175 b = lw0 b (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) tt tt Eq.refl
wn00176 : Base 3 → ⟪ (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00176 b = lw3 b (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00177 : Base 3 → ⟪ (CCZ012 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00177 b = lw3 b (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00178 : Base 3 → ⟪ (CCZ012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00178 b = lw3 b (CCZ012 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00179 : Base 3 → ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00179 b = lw0 b (CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00180 : Base 3 → ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00180 b = lw3 b (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00181 : Base 3 → ⟪ (CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00181 b = lw0 b (CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00182 : Base 3 → ⟪ (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00182 b = lw3 b (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) tt tt Eq.refl
wn00183 : Base 3 → ⟪ (S0 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0 ∷ []) ⟫ʷ
wn00183 b = lw3 b (S0 ∷ CS02 ∷ []) (CS02 ∷ S0 ∷ []) tt tt Eq.refl
wn00184 : Base 3 → ⟪ (S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0 ∷ []) ⟫ʷ
wn00184 b = lw3 b (S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0 ∷ []) tt tt Eq.refl
wn00185 : Base 3 → ⟪ (S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0⁻ ∷ []) ⟫ʷ
wn00185 b = lw3 b (S0⁻ ∷ CS02 ∷ []) (CS02 ∷ S0⁻ ∷ []) tt tt Eq.refl
wn00186 : Base 3 → ⟪ (S0⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn00186 b = lw3 b (S0⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0⁻ ∷ []) tt tt Eq.refl
wn00187 : Base 3 → ⟪ (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00187 b = lw3 b (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ []) tt tt Eq.refl
wn00188 : Base 3 → ⟪ (CCZ012 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ012 ∷ []) ⟫ʷ
wn00188 b = lw3 b (CCZ012 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00189 : Base 3 → ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ
wn00189 b = lw3 b (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) tt tt Eq.refl
wn00190 : Base 3 → ⟪ (CS13 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS13 ∷ []) ⟫ʷ
wn00190 b = lw0 b (CS13 ∷ CZ12 ∷ []) (CZ12 ∷ CS13 ∷ []) tt tt Eq.refl
wn00191 : Base 3 → ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ
wn00191 b = lw3 b (Sw01 ∷ CZ12 ∷ []) (CZ02 ∷ Sw01 ∷ []) tt tt Eq.refl
wn00192 : Base 3 → ⟪ (CS01⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00192 b = lw3 b (CS01⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn00193 : Base 3 → ⟪ (CS01 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS01 ∷ []) ⟫ʷ
wn00193 b = lw3 b (CS01 ∷ CZ02 ∷ []) (CZ02 ∷ CS01 ∷ []) tt tt Eq.refl
wn00194 : Base 3 → ⟪ (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00194 b = lw3 b (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ []) tt tt Eq.refl
wn00195 : Base 3 → ⟪ (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00195 b = lw3 b (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ []) tt tt Eq.refl
wn00196 : Base 3 → ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00196 b = lw3 b (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) tt tt Eq.refl
wn00197 : Base 3 → ⟪ (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00197 b = lw3 b (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) tt tt Eq.refl
wn00198 : Base 3 → ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00198 b = lw0 b (CS13 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS13 ∷ []) tt tt Eq.refl
wn00199 : Base 3 → ⟪ (CS01⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn00199 b = lw3 b (CS01⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl
wn00200 : Base 3 → ⟪ (CS01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS01 ∷ []) ⟫ʷ
wn00200 b = lw3 b (CS01 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS01 ∷ []) tt tt Eq.refl
wn00201 : Base 3 → ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ
wn00201 b = lw3 b (Toff102 ∷ S0 ∷ []) (S0 ∷ Toff102 ∷ []) tt tt Eq.refl
wn00202 : Base 3 → ⟪ (Toff102 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff102 ∷ []) ⟫ʷ
wn00202 b = lw3 b (Toff102 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff102 ∷ []) tt tt Eq.refl
wn00203 : Base 3 → ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ
wn00203 b = lw3 b (CS12 ∷ S0 ∷ []) (S0 ∷ CS12 ∷ []) tt tt Eq.refl
wn00204 : Base 3 → ⟪ (CS12 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00204 b = lw3 b (CS12 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12 ∷ []) tt tt Eq.refl
wn00205 : Base 3 → ⟪ (CS12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS12 ∷ []) ⟫ʷ
wn00205 b = lw3 b (CS12 ∷ CS02 ∷ []) (CS02 ∷ CS12 ∷ []) tt tt Eq.refl
wn00206 : Base 3 → ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00206 b = lw3 b (CS12⁻ ∷ S0 ∷ []) (S0 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00207 : Base 3 → ⟪ (CS12⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00207 b = lw3 b (CS12⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00208 : Base 3 → ⟪ (CS12⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00208 b = lw3 b (CS12⁻ ∷ CS02 ∷ []) (CS02 ∷ CS12⁻ ∷ []) tt tt Eq.refl
wn00209 : Base 3 → ⟪ (Toff102 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00209 b = lw3 b (Toff102 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff102 ∷ []) tt tt Eq.refl
wn00210 : Base 3 → ⟪ (S2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2 ∷ []) ⟫ʷ
wn00210 b = lw0 b (S2 ∷ CS13 ∷ []) (CS13 ∷ S2 ∷ []) tt tt Eq.refl
wn00211 : Base 3 → ⟪ (S2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2 ∷ []) ⟫ʷ
wn00211 b = lw0 b (S2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2 ∷ []) tt tt Eq.refl
wn00212 : Base 3 → ⟪ (S2⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2⁻ ∷ []) ⟫ʷ
wn00212 b = lw0 b (S2⁻ ∷ CS13 ∷ []) (CS13 ∷ S2⁻ ∷ []) tt tt Eq.refl
wn00213 : Base 3 → ⟪ (S2⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ
wn00213 b = lw0 b (S2⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl
wn00214 : Base 3 → ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00214 b = lw3 b (CCZ012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl
wn00215 : Base 3 → ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ
wn00215 b = lw3 b (X2 ∷ Sw12 ∷ []) (Sw12 ∷ X1 ∷ []) tt tt Eq.refl
