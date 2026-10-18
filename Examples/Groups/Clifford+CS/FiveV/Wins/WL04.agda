------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Wins.WL04 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0701 : Complete 4 → ⟪ (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ013 ∷ []) ⟫ʷ
wl0701 c4 = lw4 c4 (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (CX23 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0702 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) ⟫ʷ
wl0702 c4 = lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) tt tt Eq.refl

wl0703 : Complete 4 → ⟪ (CCZ013 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl0703 c4 = lw4 c4 (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0704 : Complete 4 → ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ
wl0704 c4 = lw4 c4 (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0705 : Complete 4 → ⟪ (CX23 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
wl0705 c4 = lw4 c4 (CX23 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX23 ∷ []) tt tt Eq.refl

wl0706 : Complete 4 → ⟪ (CCZ013 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CCZ013 ∷ []) ⟫ʷ
wl0706 c4 = lw4 c4 (CCZ013 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0707 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) ⟫ʷ
wl0707 c4 = lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl

wl0708 : Complete 4 → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0708 c4 = lw0 c4 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0709 : Complete 4 → ⟪ (X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S4⁻ ∷ X4 ∷ []) ⟫ʷ
wl0709 c4 = lw1 c4 (X4 ∷ S4 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ []) tt tt Eq.refl

wl0710 : Complete 4 → ⟪ (S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ ι ∷ S4⁻ ∷ []) ⟫ʷ
wl0710 c4 = lw1 c4 (S4 ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ []) tt tt Eq.refl

wl0711 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ []) ⟫ʷ
wl0711 c4 = lw0 c4 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0712 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0712 c4 = lw0 c4 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0713 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0713 c4 = lw0 c4 (CS14 ∷ X4 ∷ []) (X4 ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0714 : Complete 4 → ⟪ (S2 ∷ CS24⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ []) ⟫ʷ
wl0714 c4 = lw0 c4 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0715 : Complete 4 → ⟪ (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0715 c4 = lw0 c4 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (Toff314 ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0716 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0716 c4 = lw0 c4 (CS24 ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0717 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ []) ⟫ʷ
wl0717 c4 = lw0 c4 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0718 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0718 c4 = lw0 c4 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0719 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0719 c4 = lw0 c4 (CS34 ∷ X4 ∷ []) (X4 ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0720 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ []) ⟫ʷ
wl0720 c4 = lw0 c4 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0721 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wl0721 c4 = lw0 c4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (Toff214 ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wl0722 : Complete 4 → ⟪ (CCZ023 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ023 ∷ []) ⟫ʷ
wl0722 c4 = lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0723 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wl0723 c4 = lw0 c4 (CK41 ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wl0724 : Complete 4 → ⟪ (CK42 ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0724 c4 = lw0 c4 (CK42 ∷ []) (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0725 : Complete 4 → ⟪ (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ []) ⟫ʷ
wl0725 c4 = lw0 c4 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0726 : Complete 4 → ⟪ (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
wl0726 c4 = lw0 c4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (Toff314 ∷ K2 ∷ CK42 ∷ S4 ∷ []) tt tt Eq.refl

wl0727 : Complete 4 → ⟪ (S4 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ S4 ∷ []) ⟫ʷ
wl0727 c4 = lw0 c4 (S4 ∷ Toff213 ∷ []) (Toff213 ∷ S4 ∷ []) tt tt Eq.refl

wl0728 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
wl0728 c4 = lw0 c4 (CK42 ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ []) tt tt Eq.refl

wl0729 : Complete 4 → ⟪ (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ []) ⟫ʷ
wl0729 c4 = lw0 c4 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0730 : Complete 4 → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wl0730 c4 = lw0 c4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (Toff234 ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wl0731 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wl0731 c4 = lw0 c4 (CK43 ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wl0732 : Complete 4 → ⟪ (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S2 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0732 c4 = lw0 c4 (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0733 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0733 c4 = lw0 c4 (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0734 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wl0734 c4 = lw0 c4 (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wl0735 : Complete 4 → ⟪ (K1 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ K1 ∷ []) ⟫ʷ
wl0735 c4 = lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl

wl0736 : Complete 4 → ⟪ (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
wl0736 c4 = lw0 c4 (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) tt tt Eq.refl

wl0737 : Complete 4 → ⟪ (CCZ013 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ013 ∷ []) ⟫ʷ
wl0737 c4 = lw4 c4 (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0738 : Complete 4 → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wl0738 c4 = lw0 c4 (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wl0739 : Complete 4 → ⟪ (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S1 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0739 c4 = lw0 c4 (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S1 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0740 : Complete 4 → ⟪ (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S3 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0740 c4 = lw0 c4 (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0741 : Complete 4 → ⟪ (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
wl0741 c4 = lw0 c4 (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) tt tt Eq.refl

wl0742 : Complete 4 → ⟪ (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
wl0742 c4 = lw0 c4 (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) tt tt Eq.refl

wl0743 : Complete 4 → ⟪ (K2 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ K2 ∷ []) ⟫ʷ
wl0743 c4 = lw4 c4 (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ []) tt tt Eq.refl

wl0744 : Complete 4 → ⟪ (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
wl0744 c4 = lw0 c4 (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ []) tt tt Eq.refl

wl0745 : Complete 4 → ⟪ (CX13 ∷ Toff314 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff314 ∷ []) ⟫ʷ
wl0745 c4 = lw0 c4 (CX13 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0746 : Complete 4 → ⟪ (CX12 ∷ CX13 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX13 ∷ []) ⟫ʷ
wl0746 c4 = lw4 c4 (CX12 ∷ CX13 ∷ Toff213 ∷ []) (Toff213 ∷ CX13 ∷ []) tt tt Eq.refl

wl0747 : Complete 4 → ⟪ (Toff213 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) ⟫ʷ
wl0747 c4 = lw0 c4 (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0748 : Complete 4 → ⟪ (CX12 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX12 ∷ []) ⟫ʷ
wl0748 c4 = lw4 c4 (CX12 ∷ Toff213 ∷ []) (Toff213 ∷ CX12 ∷ []) tt tt Eq.refl

wl0749 : Complete 4 → ⟪ (CCZ134 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) ⟫ʷ
wl0749 c4 = lw0 c4 (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) tt tt Eq.refl

wl0750 : Complete 4 → ⟪ (CCZ134 ∷ CZ14 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl0750 c4 = lw0 c4 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl0751 : Complete 4 → ⟪ (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CCZ023 ∷ []) ⟫ʷ
wl0751 c4 = lw4 c4 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (CX10 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0752 : Complete 4 → ⟪ (CCZ123 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ
wl0752 c4 = lw0 c4 (CCZ123 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0753 : Complete 4 → ⟪ (CX10 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wl0753 c4 = lw4 c4 (CX10 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ []) tt tt Eq.refl

wl0754 : Complete 4 → ⟪ (CS24 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS24 ∷ []) ⟫ʷ
wl0754 c4 = lw0 c4 (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ []) tt tt Eq.refl

wl0755 : Complete 4 → ⟪ (CX10 ∷ CX01 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ []) ⟫ʷ
wl0755 c4 = lw4 c4 (CX10 ∷ CX01 ∷ CX10 ∷ []) (Sw01 ∷ []) tt tt Eq.refl

wl0756 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) ⟫ʷ
wl0756 c4 = lw0 c4 (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0757 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) ⟫ʷ
wl0757 c4 = lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) tt tt Eq.refl

wl0758 : Complete 4 → ⟪ (CCZ123 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) ⟫ʷ
wl0758 c4 = lw0 c4 (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0759 : Complete 4 → ⟪ (CCZ134 ∷ CCZ123 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ123 ∷ []) ⟫ʷ
wl0759 c4 = lw0 c4 (CCZ134 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0760 : Complete 4 → ⟪ (K3⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ K3⁻ ∷ []) ⟫ʷ
wl0760 c4 = lw0 c4 (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ []) tt tt Eq.refl

wl0761 : Complete 4 → ⟪ (CS34 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS34 ∷ []) ⟫ʷ
wl0761 c4 = lw0 c4 (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) tt tt Eq.refl

wl0762 : Complete 4 → ⟪ (K3 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ K3 ∷ []) ⟫ʷ
wl0762 c4 = lw0 c4 (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ []) tt tt Eq.refl

wl0763 : Complete 4 → ⟪ (CCZ123 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ123 ∷ []) ⟫ʷ
wl0763 c4 = lw4 c4 (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0764 : Complete 4 → ⟪ (CCZ123 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0764 c4 = lw0 c4 (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0765 : Complete 4 → ⟪ (CCZ123 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CCZ123 ∷ []) ⟫ʷ
wl0765 c4 = lw0 c4 (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0766 : Complete 4 → ⟪ (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
wl0766 c4 = lw0 c4 (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0767 : Complete 4 → ⟪ (CCZ124 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff214 ∷ []) ⟫ʷ
wl0767 c4 = lw0 c4 (CCZ124 ∷ CZ14 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0768 : Complete 4 → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ124 ∷ CZ14 ∷ []) ⟫ʷ
wl0768 c4 = lw0 c4 (CCZ124 ∷ []) (CZ14 ∷ CCZ124 ∷ CZ14 ∷ []) tt tt Eq.refl

wl0769 : Complete 4 → ⟪ (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ123 ∷ []) ⟫ʷ
wl0769 c4 = lw0 c4 (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) (Toff314 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0770 : Complete 4 → ⟪ (CCZ123 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ123 ∷ []) ⟫ʷ
wl0770 c4 = lw0 c4 (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0771 : Complete 4 → ⟪ (CX23 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff314 ∷ CX23 ∷ []) ⟫ʷ
wl0771 c4 = lw0 c4 (CX23 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ CX23 ∷ []) tt tt Eq.refl

wl0772 : Complete 4 → ⟪ (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ023 ∷ []) ⟫ʷ
wl0772 c4 = lw4 c4 (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) (CX23 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0773 : Complete 4 → ⟪ (CCZ023 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ023 ∷ CX23 ∷ []) ⟫ʷ
wl0773 c4 = lw4 c4 (CCZ023 ∷ CZ02 ∷ []) (CX23 ∷ CCZ023 ∷ CX23 ∷ []) tt tt Eq.refl

wl0774 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ023 ∷ CZ02 ∷ []) ⟫ʷ
wl0774 c4 = lw4 c4 (CCZ023 ∷ []) (CZ02 ∷ CCZ023 ∷ CZ02 ∷ []) tt tt Eq.refl

wl0775 : Complete 4 → ⟪ (Toff214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff214 ∷ []) ⟫ʷ
wl0775 c4 = lw0 c4 (Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0776 : Complete 4 → ⟪ (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0776 c4 = lw0 c4 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0777 : Complete 4 → ⟪ (Toff214 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ
wl0777 c4 = lw0 c4 (Toff214 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl

wl0778 : Complete 4 → ⟪ (CS14⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0778 c4 = lw0 c4 (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0779 : Complete 4 → ⟪ (Toff312 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff312 ∷ []) ⟫ʷ
wl0779 c4 = lw0 c4 (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0780 : Complete 4 → ⟪ (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0780 c4 = lw0 c4 (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0781 : Complete 4 → ⟪ (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ []) ⟫ʷ
wl0781 c4 = lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl

wl0782 : Complete 4 → ⟪ (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
wl0782 c4 = lw4 c4 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (Toff302 ∷ []) tt tt Eq.refl

wl0783 : Complete 4 → ⟪ (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
wl0783 c4 = lw0 c4 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0784 : Complete 4 → ⟪ (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
wl0784 c4 = lw4 c4 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0785 : Complete 4 → ⟪ (CS14⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS14⁻ ∷ []) ⟫ʷ
wl0785 c4 = lw0 c4 (CS14⁻ ∷ S3 ∷ []) (S3 ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0786 : Complete 4 → ⟪ (CS14⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS14⁻ ∷ []) ⟫ʷ
wl0786 c4 = lw0 c4 (CS14⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl

wl0787 : Complete 4 → ⟪ (Toff302 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0787 c4 = lw4 c4 (Toff302 ∷ Toff302 ∷ []) [] tt tt Eq.refl

wl0788 : Complete 4 → ⟪ (Toff314 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0788 c4 = lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl

wl0789 : Complete 4 → ⟪ (CS03⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0789 c4 = lw4 c4 (CS03⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0790 : Complete 4 → ⟪ (CCZ134 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ134 ∷ []) ⟫ʷ
wl0790 c4 = lw0 c4 (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0791 : Complete 4 → ⟪ (CCZ023 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) ⟫ʷ
wl0791 c4 = lw4 c4 (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0792 : Complete 4 → ⟪ (CS02⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0792 c4 = lw4 c4 (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0793 : Complete 4 → ⟪ (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CS02⁻ ∷ CZ02 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
wl0793 c4 = lw4 c4 (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CS02⁻ ∷ CZ02 ∷ CCZ023 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl

wl0794 : Complete 4 → ⟪ (CX23 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX23 ∷ []) ⟫ʷ
wl0794 c4 = lw0 c4 (CX23 ∷ Toff314 ∷ []) (Toff314 ∷ CX23 ∷ []) tt tt Eq.refl

wl0795 : Complete 4 → ⟪ (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS03 ∷ []) ⟫ʷ
wl0795 c4 = lw4 c4 (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03 ∷ []) tt tt Eq.refl

wl0796 : Complete 4 → ⟪ (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0796 c4 = lw4 c4 (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0797 : Complete 4 → ⟪ (CCZ023 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ023 ∷ []) ⟫ʷ
wl0797 c4 = lw4 c4 (CCZ023 ∷ CS02 ∷ []) (CS02 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0798 : Complete 4 → ⟪ (CS02 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
wl0798 c4 = lw4 c4 (CS02 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl

wl0799 : Complete 4 → ⟪ (CCZ023 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0799 c4 = lw4 c4 (CCZ023 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0800 : Complete 4 → ⟪ (CS03 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) ⟫ʷ
wl0800 c4 = lw4 c4 (CS03 ∷ Toff302 ∷ []) (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0801 : Complete 4 → ⟪ (CS02 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS02 ∷ []) ⟫ʷ
wl0801 c4 = lw4 c4 (CS02 ∷ Toff302 ∷ []) (Toff302 ∷ CS02 ∷ []) tt tt Eq.refl

wl0802 : Complete 4 → ⟪ (CS03 ∷ CS02 ∷ CCZ023 ∷ CS02 ∷ CZ02 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
wl0802 c4 = lw4 c4 (CS03 ∷ CS02 ∷ CCZ023 ∷ CS02 ∷ CZ02 ∷ CCZ023 ∷ []) (CS03 ∷ []) tt tt Eq.refl

wl0803 : Complete 4 → ⟪ (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
wl0803 c4 = lw0 c4 (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0804 : Complete 4 → ⟪ (CCZ134 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CZ14 ∷ CCZ134 ∷ []) ⟫ʷ
wl0804 c4 = lw0 c4 (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CZ14 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0805 : Complete 4 → ⟪ (CCZ123 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ
wl0805 c4 = lw0 c4 (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0806 : Complete 4 → ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0806 c4 = lw4 c4 (CX23 ∷ CX23 ∷ []) [] tt tt Eq.refl

wl0807 : Complete 4 → ⟪ (CS34⁻ ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS34⁻ ∷ []) ⟫ʷ
wl0807 c4 = lw0 c4 (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wl0808 : Complete 4 → ⟪ (CS34 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS34 ∷ []) ⟫ʷ
wl0808 c4 = lw0 c4 (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) tt tt Eq.refl

wl0809 : Complete 4 → ⟪ (CX32 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX32 ∷ []) ⟫ʷ
wl0809 c4 = lw4 c4 (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ []) tt tt Eq.refl

wl0810 : Complete 4 → ⟪ (CX32 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX32 ∷ Toff214 ∷ []) ⟫ʷ
wl0810 c4 = lw0 c4 (CX32 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ Toff214 ∷ []) tt tt Eq.refl

wl0811 : Complete 4 → ⟪ (CS03 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS03 ∷ []) ⟫ʷ
wl0811 c4 = lw4 c4 (CS03 ∷ CX32 ∷ []) (CX32 ∷ CS03 ∷ []) tt tt Eq.refl

wl0812 : Complete 4 → ⟪ (CX32 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX32 ∷ []) ⟫ʷ
wl0812 c4 = lw0 c4 (CX32 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ []) tt tt Eq.refl

wl0813 : Complete 4 → ⟪ (CS03⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0813 c4 = lw4 c4 (CS03⁻ ∷ CX32 ∷ []) (CX32 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0814 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) ⟫ʷ
wl0814 c4 = lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl

wl0815 : Complete 4 → ⟪ (Sw23 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw23 ∷ []) ⟫ʷ
wl0815 c4 = lw0 c4 (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0816 : Complete 4 → ⟪ (CS02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS03 ∷ []) ⟫ʷ
wl0816 c4 = lw4 c4 (CS02 ∷ Sw23 ∷ []) (Sw23 ∷ CS03 ∷ []) tt tt Eq.refl

wl0817 : Complete 4 → ⟪ (CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS03⁻ ∷ []) ⟫ʷ
wl0817 c4 = lw4 c4 (CS02⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wl0818 : Complete 4 → ⟪ (CS02⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) ⟫ʷ
wl0818 c4 = lw4 c4 (CS02⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0819 : Complete 4 → ⟪ (CCZ023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) ⟫ʷ
wl0819 c4 = lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0820 : Complete 4 → ⟪ (CS23⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS23⁻ ∷ []) ⟫ʷ
wl0820 c4 = lw4 c4 (CS23⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS23⁻ ∷ []) tt tt Eq.refl

wl0821 : Complete 4 → ⟪ (CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wl0821 c4 = lw4 c4 (CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl

wl0822 : Complete 4 → ⟪ (CS02 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) ⟫ʷ
wl0822 c4 = lw4 c4 (CS02 ∷ Toff023 ∷ []) (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0823 : Complete 4 → ⟪ (CS23 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS23 ∷ []) ⟫ʷ
wl0823 c4 = lw4 c4 (CS23 ∷ Toff023 ∷ []) (Toff023 ∷ CS23 ∷ []) tt tt Eq.refl

wl0824 : Complete 4 → ⟪ (CS02 ∷ CS23 ∷ CCZ023 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wl0824 c4 = lw4 c4 (CS02 ∷ CS23 ∷ CCZ023 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ []) (CS02 ∷ []) tt tt Eq.refl

wl0825 : Complete 4 → ⟪ (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
wl0825 c4 = lw4 c4 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0826 : Complete 4 → ⟪ (CCZ023 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff023 ∷ []) ⟫ʷ
wl0826 c4 = lw4 c4 (CCZ023 ∷ CZ23 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff023 ∷ []) tt tt Eq.refl

wl0827 : Complete 4 → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ023 ∷ CZ23 ∷ []) ⟫ʷ
wl0827 c4 = lw4 c4 (CCZ023 ∷ []) (CZ23 ∷ CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl

wl0828 : Complete 4 → ⟪ (CX21 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX21 ∷ []) ⟫ʷ
wl0828 c4 = lw4 c4 (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ []) tt tt Eq.refl

wl0829 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) ⟫ʷ
wl0829 c4 = lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl

wl0830 : Complete 4 → ⟪ (CX12 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX12 ∷ Toff013 ∷ []) ⟫ʷ
wl0830 c4 = lw4 c4 (CX12 ∷ Toff023 ∷ []) (Toff023 ∷ CX12 ∷ Toff013 ∷ []) tt tt Eq.refl

wl0831 : Complete 4 → ⟪ (CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) ⟫ʷ
wl0831 c4 = lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) tt tt Eq.refl

wl0832 : Complete 4 → ⟪ (CX31 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX31 ∷ []) ⟫ʷ
wl0832 c4 = lw4 c4 (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) tt tt Eq.refl

wl0833 : Complete 4 → ⟪ (Toff013 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff013 ∷ []) ⟫ʷ
wl0833 c4 = lw4 c4 (Toff013 ∷ Toff023 ∷ []) (Toff023 ∷ Toff013 ∷ []) tt tt Eq.refl

wl0834 : Complete 4 → ⟪ (CX12 ∷ Toff013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wl0834 c4 = lw4 c4 (CX12 ∷ Toff013 ∷ Toff013 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wl0835 : Complete 4 → ⟪ (CX21 ∷ CX12 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ []) ⟫ʷ
wl0835 c4 = lw4 c4 (CX21 ∷ CX12 ∷ CX21 ∷ []) (Sw12 ∷ []) tt tt Eq.refl

wl0836 : Complete 4 → ⟪ (CCZ234 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ234 ∷ []) ⟫ʷ
wl0836 c4 = lw0 c4 (CCZ234 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0837 : Complete 4 → ⟪ (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ []) ⟫ʷ
wl0837 c4 = lw0 c4 (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl

wl0838 : Complete 4 → ⟪ (CCZ013 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ023 ∷ []) ⟫ʷ
wl0838 c4 = lw4 c4 (CCZ013 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ023 ∷ []) tt tt Eq.refl

wl0839 : Complete 4 → ⟪ (Sw12 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw12 ∷ []) ⟫ʷ
wl0839 c4 = lw4 c4 (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0840 : Complete 4 → ⟪ (CCZ023 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ013 ∷ []) ⟫ʷ
wl0840 c4 = lw4 c4 (CCZ023 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0841 : Complete 4 → ⟪ (Sw12 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Sw12 ∷ []) ⟫ʷ
wl0841 c4 = lw4 c4 (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0842 : Complete 4 → ⟪ (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
wl0842 c4 = lw0 c4 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0843 : Complete 4 → ⟪ (CCZ234 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff324 ∷ []) ⟫ʷ
wl0843 c4 = lw0 c4 (CCZ234 ∷ CZ24 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0844 : Complete 4 → ⟪ (CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ234 ∷ CZ24 ∷ []) ⟫ʷ
wl0844 c4 = lw0 c4 (CCZ234 ∷ []) (CZ24 ∷ CCZ234 ∷ CZ24 ∷ []) tt tt Eq.refl

wl0845 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) ⟫ʷ
wl0845 c4 = lw4 c4 (CCZ013 ∷ []) (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) tt tt Eq.refl

wl0846 : Complete 4 → ⟪ (CCZ234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) ⟫ʷ
wl0846 c4 = lw0 c4 (CCZ234 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) tt tt Eq.refl

wl0847 : Complete 4 → ⟪ (CCZ234 ∷ CZ24 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ []) ⟫ʷ
wl0847 c4 = lw0 c4 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ []) tt tt Eq.refl

wl0848 : Complete 4 → ⟪ (CX41 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX41 ∷ []) ⟫ʷ
wl0848 c4 = lw0 c4 (CX41 ∷ Toff324 ∷ []) (Toff324 ∷ CX41 ∷ []) tt tt Eq.refl

wl0849 : Complete 4 → ⟪ (CX14 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX14 ∷ Toff312 ∷ []) ⟫ʷ
wl0849 c4 = lw0 c4 (CX14 ∷ Toff324 ∷ []) (Toff324 ∷ CX14 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0850 : Complete 4 → ⟪ (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ013 ∷ []) ⟫ʷ
wl0850 c4 = lw4 c4 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (Toff312 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0851 : Complete 4 → ⟪ (CX21 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CX21 ∷ []) ⟫ʷ
wl0851 c4 = lw0 c4 (CX21 ∷ Toff324 ∷ []) (Toff324 ∷ CX21 ∷ []) tt tt Eq.refl

wl0852 : Complete 4 → ⟪ (Toff312 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff312 ∷ []) ⟫ʷ
wl0852 c4 = lw0 c4 (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) tt tt Eq.refl

wl0853 : Complete 4 → ⟪ (CX14 ∷ Toff312 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ []) ⟫ʷ
wl0853 c4 = lw0 c4 (CX14 ∷ Toff312 ∷ Toff312 ∷ []) (CX14 ∷ []) tt tt Eq.refl

wl0854 : Complete 4 → ⟪ (CCZ123 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ234 ∷ []) ⟫ʷ
wl0854 c4 = lw0 c4 (CCZ123 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ234 ∷ []) tt tt Eq.refl

wl0855 : Complete 4 → ⟪ (Sw14 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw14 ∷ []) ⟫ʷ
wl0855 c4 = lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl

wl0856 : Complete 4 → ⟪ (CCZ234 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw14 ∷ CCZ123 ∷ []) ⟫ʷ
wl0856 c4 = lw0 c4 (CCZ234 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0857 : Complete 4 → ⟪ (Sw14 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Sw14 ∷ []) ⟫ʷ
wl0857 c4 = lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl

wl0858 : Complete 4 → ⟪ (CX14 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX14 ∷ []) ⟫ʷ
wl0858 c4 = lw0 c4 (CX14 ∷ Toff312 ∷ []) (Toff312 ∷ CX14 ∷ []) tt tt Eq.refl

wl0859 : Complete 4 → ⟪ (CCZ013 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ
wl0859 c4 = lw4 c4 (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0860 : Complete 4 → ⟪ (CX41 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX41 ∷ Toff324 ∷ []) ⟫ʷ
wl0860 c4 = lw0 c4 (CX41 ∷ Toff312 ∷ []) (Toff312 ∷ CX41 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0861 : Complete 4 → ⟪ (CS02 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS02 ∷ []) ⟫ʷ
wl0861 c4 = lw4 c4 (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) tt tt Eq.refl

wl0862 : Complete 4 → ⟪ (CX24 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX24 ∷ []) ⟫ʷ
wl0862 c4 = lw0 c4 (CX24 ∷ Toff312 ∷ []) (Toff312 ∷ CX24 ∷ []) tt tt Eq.refl

wl0863 : Complete 4 → ⟪ (CX41 ∷ Toff324 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ []) ⟫ʷ
wl0863 c4 = lw0 c4 (CX41 ∷ Toff324 ∷ Toff324 ∷ []) (CX41 ∷ []) tt tt Eq.refl

wl0864 : Complete 4 → ⟪ (Sw14 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sw14 ∷ []) ⟫ʷ
wl0864 c4 = lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl

wl0865 : Complete 4 → ⟪ (Sw14 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Sw14 ∷ []) ⟫ʷ
wl0865 c4 = lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl

wl0866 : Complete 4 → ⟪ (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
wl0866 c4 = lw4 c4 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0867 : Complete 4 → ⟪ (CCZ013 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff301 ∷ []) ⟫ʷ
wl0867 c4 = lw4 c4 (CCZ013 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff301 ∷ []) tt tt Eq.refl

wl0868 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ013 ∷ CZ01 ∷ []) ⟫ʷ
wl0868 c4 = lw4 c4 (CCZ013 ∷ []) (CZ01 ∷ CCZ013 ∷ CZ01 ∷ []) tt tt Eq.refl

wl0869 : Complete 4 → ⟪ (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0869 c4 = lw4 c4 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0870 : Complete 4 → ⟪ (Toff312 ∷ CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl0870 c4 = lw4 c4 (Toff312 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl0871 : Complete 4 → ⟪ (CCZ124 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ124 ∷ []) ⟫ʷ
wl0871 c4 = lw0 c4 (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) tt tt Eq.refl

wl0872 : Complete 4 → ⟪ (CX12 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX12 ∷ []) ⟫ʷ
wl0872 c4 = lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl

wl0873 : Complete 4 → ⟪ (CX21 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX21 ∷ Toff023 ∷ []) ⟫ʷ
wl0873 c4 = lw4 c4 (CX21 ∷ Toff013 ∷ []) (Toff013 ∷ CX21 ∷ Toff023 ∷ []) tt tt Eq.refl

wl0874 : Complete 4 → ⟪ (CX32 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX32 ∷ []) ⟫ʷ
wl0874 c4 = lw4 c4 (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) tt tt Eq.refl

wl0875 : Complete 4 → ⟪ (CX21 ∷ Toff023 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wl0875 c4 = lw4 c4 (CX21 ∷ Toff023 ∷ Toff023 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wl0876 : Complete 4 → ⟪ (Sw12 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw12 ∷ []) ⟫ʷ
wl0876 c4 = lw4 c4 (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0877 : Complete 4 → ⟪ (Sw12 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw12 ∷ []) ⟫ʷ
wl0877 c4 = lw4 c4 (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) tt tt Eq.refl

wl0878 : Complete 4 → ⟪ (CS24⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS24⁻ ∷ []) ⟫ʷ
wl0878 c4 = lw0 c4 (CS24⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wl0879 : Complete 4 → ⟪ (CS24 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS24 ∷ []) ⟫ʷ
wl0879 c4 = lw0 c4 (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) tt tt Eq.refl

wl0880 : Complete 4 → ⟪ (CX23 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX23 ∷ []) ⟫ʷ
wl0880 c4 = lw4 c4 (CX23 ∷ Toff312 ∷ []) (Toff312 ∷ CX23 ∷ []) tt tt Eq.refl

wl0881 : Complete 4 → ⟪ (CS13 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) ⟫ʷ
wl0881 c4 = lw4 c4 (CS13 ∷ Toff312 ∷ []) (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0882 : Complete 4 → ⟪ (CCZ123 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
wl0882 c4 = lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0883 : Complete 4 → ⟪ (CS12 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS12 ∷ []) ⟫ʷ
wl0883 c4 = lw4 c4 (CS12 ∷ Toff312 ∷ []) (Toff312 ∷ CS12 ∷ []) tt tt Eq.refl

wl0884 : Complete 4 → ⟪ (CS13 ∷ CS12 ∷ CCZ123 ∷ CS12 ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wl0884 c4 = lw4 c4 (CS13 ∷ CS12 ∷ CCZ123 ∷ CS12 ∷ CZ12 ∷ CCZ123 ∷ []) (CS13 ∷ []) tt tt Eq.refl

wl0885 : Complete 4 → ⟪ (CS13⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wl0885 c4 = lw4 c4 (CS13⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0886 : Complete 4 → ⟪ (CS12⁻ ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CS12⁻ ∷ []) ⟫ʷ
wl0886 c4 = lw4 c4 (CS12⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl0887 : Complete 4 → ⟪ (CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ CS12⁻ ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
wl0887 c4 = lw4 c4 (CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ CS12⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CS13⁻ ∷ []) tt tt Eq.refl

wl0888 : Complete 4 → ⟪ (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
wl0888 c4 = lw0 c4 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl

wl0889 : Complete 4 → ⟪ (CZ12 ∷ CCZ123 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
wl0889 c4 = lw4 c4 (CZ12 ∷ CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0890 : Complete 4 → ⟪ (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) ⟫ʷ
wl0890 c4 = lw0 c4 (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0891 : Complete 4 → ⟪ (CCZ123 ∷ CCZ134 ∷ Toff214 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) ⟫ʷ
wl0891 c4 = lw0 c4 (CCZ123 ∷ CCZ134 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0892 : Complete 4 → ⟪ (CCZ123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ123 ∷ []) ⟫ʷ
wl0892 c4 = lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0893 : Complete 4 → ⟪ (CCZ134 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ134 ∷ []) ⟫ʷ
wl0893 c4 = lw0 c4 (CCZ134 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0894 : Complete 4 → ⟪ (CX23 ∷ Toff324 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff324 ∷ []) ⟫ʷ
wl0894 c4 = lw0 c4 (CX23 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0895 : Complete 4 → ⟪ (CX23 ∷ Toff324 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX23 ∷ Toff324 ∷ []) ⟫ʷ
wl0895 c4 = lw0 c4 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (Toff214 ∷ CX23 ∷ Toff324 ∷ []) tt tt Eq.refl

wl0896 : Complete 4 → ⟪ (CS13 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13 ∷ []) ⟫ʷ
wl0896 c4 = lw0 c4 (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ []) tt tt Eq.refl

wl0897 : Complete 4 → ⟪ (CS02⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS02⁻ ∷ []) ⟫ʷ
wl0897 c4 = lw4 c4 (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0898 : Complete 4 → ⟪ (CS13 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS13 ∷ []) ⟫ʷ
wl0898 c4 = lw0 c4 (CS13 ∷ Toff214 ∷ []) (Toff214 ∷ CS13 ∷ []) tt tt Eq.refl

wl0899 : Complete 4 → ⟪ (CS02 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS02 ∷ []) ⟫ʷ
wl0899 c4 = lw4 c4 (CS02 ∷ CS13 ∷ []) (CS13 ∷ CS02 ∷ []) tt tt Eq.refl

wl0900 : Complete 4 → ⟪ (CS13⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0900 c4 = lw0 c4 (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0901 : Complete 4 → ⟪ (CS02⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wl0901 c4 = lw4 c4 (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl0902 : Complete 4 → ⟪ (CS13⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0902 c4 = lw0 c4 (CS13⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0903 : Complete 4 → ⟪ (CS02 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS02 ∷ []) ⟫ʷ
wl0903 c4 = lw4 c4 (CS02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02 ∷ []) tt tt Eq.refl

wl0904 : Complete 4 → ⟪ (CS03⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) ⟫ʷ
wl0904 c4 = lw4 c4 (CS03⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0905 : Complete 4 → ⟪ (CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) ⟫ʷ
wl0905 c4 = lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl

wl0906 : Complete 4 → ⟪ (CCZ013 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) ⟫ʷ
wl0906 c4 = lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0907 : Complete 4 → ⟪ (CS13⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS13⁻ ∷ []) ⟫ʷ
wl0907 c4 = lw4 c4 (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl0908 : Complete 4 → ⟪ (CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
wl0908 c4 = lw4 c4 (CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl

wl0909 : Complete 4 → ⟪ (CS03 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) ⟫ʷ
wl0909 c4 = lw4 c4 (CS03 ∷ Toff013 ∷ []) (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl0910 : Complete 4 → ⟪ (CS13 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS13 ∷ []) ⟫ʷ
wl0910 c4 = lw4 c4 (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ []) tt tt Eq.refl

wl0911 : Complete 4 → ⟪ (CS03 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
wl0911 c4 = lw4 c4 (CS03 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS03 ∷ []) tt tt Eq.refl

wl0912 : Complete 4 → ⟪ (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
wl0912 c4 = lw4 c4 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0913 : Complete 4 → ⟪ (CCZ123 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff213 ∷ []) ⟫ʷ
wl0913 c4 = lw4 c4 (CCZ123 ∷ CZ13 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff213 ∷ []) tt tt Eq.refl

wl0914 : Complete 4 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ123 ∷ CZ13 ∷ []) ⟫ʷ
wl0914 c4 = lw4 c4 (CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0915 : Complete 4 → ⟪ (CCZ123 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) ⟫ʷ
wl0915 c4 = lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) tt tt Eq.refl

wl0916 : Complete 4 → ⟪ (CCZ123 ∷ CZ13 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wl0916 c4 = lw4 c4 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ []) tt tt Eq.refl

wl0917 : Complete 4 → ⟪ (CX30 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX30 ∷ []) ⟫ʷ
wl0917 c4 = lw4 c4 (CX30 ∷ Toff213 ∷ []) (Toff213 ∷ CX30 ∷ []) tt tt Eq.refl

wl0918 : Complete 4 → ⟪ (CCZ234 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) ⟫ʷ
wl0918 c4 = lw0 c4 (CCZ234 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl

wl0919 : Complete 4 → ⟪ (CX03 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX03 ∷ Toff201 ∷ []) ⟫ʷ
wl0919 c4 = lw4 c4 (CX03 ∷ Toff213 ∷ []) (Toff213 ∷ CX03 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0920 : Complete 4 → ⟪ (CX10 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CX10 ∷ []) ⟫ʷ
wl0920 c4 = lw4 c4 (CX10 ∷ Toff213 ∷ []) (Toff213 ∷ CX10 ∷ []) tt tt Eq.refl

wl0921 : Complete 4 → ⟪ (Toff201 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff201 ∷ []) ⟫ʷ
wl0921 c4 = lw4 c4 (Toff201 ∷ Toff213 ∷ []) (Toff213 ∷ Toff201 ∷ []) tt tt Eq.refl

wl0922 : Complete 4 → ⟪ (CX03 ∷ Toff201 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wl0922 c4 = lw4 c4 (CX03 ∷ Toff201 ∷ Toff201 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wl0923 : Complete 4 → ⟪ (CX30 ∷ CX03 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ []) ⟫ʷ
wl0923 c4 = lw4 c4 (CX30 ∷ CX03 ∷ CX30 ∷ []) (Sw03 ∷ []) tt tt Eq.refl

wl0924 : Complete 4 → ⟪ (CCZ012 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CCZ123 ∷ []) ⟫ʷ
wl0924 c4 = lw4 c4 (CCZ012 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl0925 : Complete 4 → ⟪ (Sw03 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Sw03 ∷ []) ⟫ʷ
wl0925 c4 = lw4 c4 (Sw03 ∷ Toff213 ∷ []) (Toff201 ∷ Sw03 ∷ []) tt tt Eq.refl

wl0926 : Complete 4 → ⟪ (CCZ123 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw03 ∷ CCZ012 ∷ []) ⟫ʷ
wl0926 c4 = lw4 c4 (CCZ123 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ012 ∷ []) tt tt Eq.refl

wl0927 : Complete 4 → ⟪ (Sw03 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw03 ∷ []) ⟫ʷ
wl0927 c4 = lw4 c4 (Sw03 ∷ Toff102 ∷ []) (Toff123 ∷ Sw03 ∷ []) tt tt Eq.refl

wl0928 : Complete 4 → ⟪ (Sw03 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0928 c4 = lw4 c4 (Sw03 ∷ Sw03 ∷ []) [] tt tt Eq.refl

wl0929 : Complete 4 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ
wl0929 c4 = lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) tt tt Eq.refl
