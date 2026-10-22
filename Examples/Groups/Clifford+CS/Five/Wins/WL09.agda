------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL09 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl1712 : Base 4 → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1712 c4 = lw4 c4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) [] tt tt Eq.refl

wl1713 : Base 4 → ⟪ (CK01 ∷ S0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1713 c4 = lw4 c4 (CK01 ∷ S0 ∷ CK01 ∷ []) [] tt tt Eq.refl

wl1714 : Base 4 → ⟪ (CK01 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1714 c4 = lw4 c4 (CK01 ∷ CK01 ∷ S0 ∷ []) [] tt tt Eq.refl

wl1715 : Base 4 → ⟪ (K2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ
wl1715 c4 = lw4 c4 (K2 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) tt tt Eq.refl

wl1716 : Base 4 → ⟪ (K3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ
wl1716 c4 = lw4 c4 (K3 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ []) tt tt Eq.refl

wl1717 : Base 4 → ⟪ (Toff213 ∷ CCZ134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wl1717 c4 = lw0 c4 (Toff213 ∷ CCZ134 ∷ CCZ134 ∷ []) (Toff213 ∷ []) tt tt Eq.refl

wl1718 : Base 4 → ⟪ (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ []) ⟫ʷ
wl1718 c4 = lw4 c4 (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1719 : Base 4 → ⟪ (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Toff301 ∷ []) ⟫ʷ
wl1719 c4 = lw4 c4 (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Toff301 ∷ []) tt tt Eq.refl

wl1720 : Base 4 → ⟪ (CCZ123 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ123 ∷ []) ⟫ʷ
wl1720 c4 = lw4 c4 (CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1721 : Base 4 → ⟪ (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff103 ∷ []) ⟫ʷ
wl1721 c4 = lw4 c4 (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (Toff213 ∷ Toff103 ∷ []) tt tt Eq.refl

wl1722 : Base 4 → ⟪ (CS12⁻ ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS12⁻ ∷ []) ⟫ʷ
wl1722 c4 = lw4 c4 (CS12⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wl1723 : Base 4 → ⟪ (CK02 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ K2⁻ ∷ CS02⁻ ∷ K2 ∷ CS02⁻ ∷ []) ⟫ʷ
wl1723 c4 = lw4 c4 (CK02 ∷ []) (CS02⁻ ∷ K2⁻ ∷ CS02⁻ ∷ K2 ∷ CS02⁻ ∷ []) tt tt Eq.refl

wl1724 : Base 4 → ⟪ (K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ
wl1724 c4 = lw4 c4 (K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ CK02 ∷ S0 ∷ []) tt tt Eq.refl

wl1725 : Base 4 → ⟪ (S0 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ S0 ∷ []) ⟫ʷ
wl1725 c4 = lw4 c4 (S0 ∷ Toff213 ∷ []) (Toff213 ∷ S0 ∷ []) tt tt Eq.refl

wl1726 : Base 4 → ⟪ (CX12 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX12 ∷ Toff413 ∷ []) ⟫ʷ
wl1726 c4 = lw0 c4 (CX12 ∷ Toff423 ∷ []) (Toff423 ∷ CX12 ∷ Toff413 ∷ []) tt tt Eq.refl

wl1727 : Base 4 → ⟪ (Toff413 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff413 ∷ []) ⟫ʷ
wl1727 c4 = lw0 c4 (Toff413 ∷ Toff423 ∷ []) (Toff423 ∷ Toff413 ∷ []) tt tt Eq.refl

wl1728 : Base 4 → ⟪ (CX12 ∷ Toff413 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
wl1728 c4 = lw0 c4 (CX12 ∷ Toff413 ∷ Toff413 ∷ []) (CX12 ∷ []) tt tt Eq.refl

wl1729 : Base 4 → ⟪ (CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
wl1729 c4 = lw4 c4 (CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl

wl1730 : Base 4 → ⟪ (Toff312 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wl1730 c4 = lw0 c4 (Toff312 ∷ CCZ124 ∷ CCZ124 ∷ []) (Toff312 ∷ []) tt tt Eq.refl

wl1731 : Base 4 → ⟪ (CX21 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CX21 ∷ Toff423 ∷ []) ⟫ʷ
wl1731 c4 = lw0 c4 (CX21 ∷ Toff413 ∷ []) (Toff413 ∷ CX21 ∷ Toff423 ∷ []) tt tt Eq.refl

wl1732 : Base 4 → ⟪ (CX21 ∷ Toff423 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wl1732 c4 = lw0 c4 (CX21 ∷ Toff423 ∷ Toff423 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wl1733 : Base 4 → ⟪ (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
wl1733 c4 = lw4 c4 (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1734 : Base 4 → ⟪ (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
wl1734 c4 = lw4 c4 (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl

wl1735 : Base 4 → ⟪ (CCZ013 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ013 ∷ []) ⟫ʷ
wl1735 c4 = lw4 c4 (CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ []) tt tt Eq.refl

wl1736 : Base 4 → ⟪ (CX23 ∷ Toff302 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CX23 ∷ Toff302 ∷ []) ⟫ʷ
wl1736 c4 = lw4 c4 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (Toff201 ∷ CX23 ∷ Toff302 ∷ []) tt tt Eq.refl

wl1737 : Base 4 → ⟪ (CS13 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS13 ∷ []) ⟫ʷ
wl1737 c4 = lw4 c4 (CS13 ∷ Toff201 ∷ []) (Toff201 ∷ CS13 ∷ []) tt tt Eq.refl

wl1738 : Base 4 → ⟪ (CS13⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS13⁻ ∷ []) ⟫ʷ
wl1738 c4 = lw4 c4 (CS13⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS13⁻ ∷ []) tt tt Eq.refl

wl1739 : Base 4 → ⟪ (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ K3 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ
wl1739 c4 = lw4 c4 (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (Toff203 ∷ K3 ∷ CK03 ∷ S0 ∷ []) tt tt Eq.refl
