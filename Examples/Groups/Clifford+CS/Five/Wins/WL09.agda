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

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl1712 : Base 4 → ⟪ (ℓ "互乇互么亏互乇亘互么亏亐些亚些些乎些乏些二亚亐些二") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1712 c4 = lw4 c4 (ℓ "互乇互么亏互乇亘互么亏亐些亚些些乎些乏些二亚亐些二") [] tt tt Eq.refl

wl1713 : Base 4 → ⟪ (ℓ "中上中") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1713 c4 = lw4 c4 (ℓ "中上中") [] tt tt Eq.refl

wl1714 : Base 4 → ⟪ (ℓ "中中上") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl1714 c4 = lw4 c4 (ℓ "中中上") [] tt tt Eq.refl

wl1715 : Base 4 → ⟪ (ℓ "丘") ⟫ʷ ≈ ⟪ (ℓ "与临与临") ⟫ʷ
wl1715 c4 = lw4 c4 (ℓ "丘") (ℓ "与临与临") tt tt Eq.refl

wl1716 : Base 4 → ⟪ (ℓ "丞") ⟫ʷ ≈ ⟪ (ℓ "与主与主") ⟫ʷ
wl1716 c4 = lw4 c4 (ℓ "丞") (ℓ "与主与主") tt tt Eq.refl

wl1717 : Base 4 → ⟪ (ℓ "亦京京") ⟫ʷ ≈ ⟪ (ℓ "亦") ⟫ʷ
wl1717 c4 = lw0 c4 (ℓ "亦京京") (ℓ "亦") tt tt Eq.refl

wl1718 : Base 4 → ⟪ (ℓ "二亓交二") ⟫ʷ ≈ ⟪ (ℓ "交二亓") ⟫ʷ
wl1718 c4 = lw4 c4 (ℓ "二亓交二") (ℓ "交二亓") tt tt Eq.refl

wl1719 : Base 4 → ⟪ (ℓ "二亓交") ⟫ʷ ≈ ⟪ (ℓ "交二二亓") ⟫ʷ
wl1719 c4 = lw4 c4 (ℓ "二亓交") (ℓ "交二二亓") tt tt Eq.refl

wl1720 : Base 4 → ⟪ (ℓ "交与") ⟫ʷ ≈ ⟪ (ℓ "与交") ⟫ʷ
wl1720 c4 = lw4 c4 (ℓ "交与") (ℓ "与交") tt tt Eq.refl

wl1721 : Base 4 → ⟪ (ℓ "互亚亦") ⟫ʷ ≈ ⟪ (ℓ "亦互") ⟫ʷ
wl1721 c4 = lw4 c4 (ℓ "互亚亦") (ℓ "亦互") tt tt Eq.refl

wl1722 : Base 4 → ⟪ (ℓ "么亓") ⟫ʷ ≈ ⟪ (ℓ "亓么") ⟫ʷ
wl1722 c4 = lw4 c4 (ℓ "么亓") (ℓ "亓么") tt tt Eq.refl

wl1723 : Base 4 → ⟪ (ℓ "临") ⟫ʷ ≈ ⟪ (ℓ "丰丙丰丘丰") ⟫ʷ
wl1723 c4 = lw4 c4 (ℓ "临") (ℓ "丰丙丰丘丰") tt tt Eq.refl

wl1724 : Base 4 → ⟪ (ℓ "丘临上亓") ⟫ʷ ≈ ⟪ (ℓ "亓丘临上") ⟫ʷ
wl1724 c4 = lw4 c4 (ℓ "丘临上亓") (ℓ "亓丘临上") tt tt Eq.refl

wl1725 : Base 4 → ⟪ (ℓ "上亦") ⟫ʷ ≈ ⟪ (ℓ "亦上") ⟫ʷ
wl1725 c4 = lw4 c4 (ℓ "上亦") (ℓ "亦上") tt tt Eq.refl

wl1726 : Base 4 → ⟪ (ℓ "之亳") ⟫ʷ ≈ ⟪ (ℓ "亳之亯") ⟫ʷ
wl1726 c4 = lw0 c4 (ℓ "之亳") (ℓ "亳之亯") tt tt Eq.refl

wl1727 : Base 4 → ⟪ (ℓ "亯亳") ⟫ʷ ≈ ⟪ (ℓ "亳亯") ⟫ʷ
wl1727 c4 = lw0 c4 (ℓ "亯亳") (ℓ "亳亯") tt tt Eq.refl

wl1728 : Base 4 → ⟪ (ℓ "之亯亯") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wl1728 c4 = lw0 c4 (ℓ "之亯亯") (ℓ "之") tt tt Eq.refl

wl1729 : Base 4 → ⟪ (ℓ "亘亐亘亐亘") ⟫ʷ ≈ ⟪ (ℓ "亘") ⟫ʷ
wl1729 c4 = lw4 c4 (ℓ "亘亐亘亐亘") (ℓ "亘") tt tt Eq.refl

wl1730 : Base 4 → ⟪ (ℓ "产亨亨") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl1730 c4 = lw0 c4 (ℓ "产亨亨") (ℓ "产") tt tt Eq.refl

wl1731 : Base 4 → ⟪ (ℓ "也亯") ⟫ʷ ≈ ⟪ (ℓ "亯也亳") ⟫ʷ
wl1731 c4 = lw0 c4 (ℓ "也亯") (ℓ "亯也亳") tt tt Eq.refl

wl1732 : Base 4 → ⟪ (ℓ "也亳亳") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wl1732 c4 = lw0 c4 (ℓ "也亳亳") (ℓ "也") tt tt Eq.refl

wl1733 : Base 4 → ⟪ (ℓ "交亏亐") ⟫ʷ ≈ ⟪ (ℓ "亏亐交亐") ⟫ʷ
wl1733 c4 = lw4 c4 (ℓ "交亏亐") (ℓ "亏亐交亐") tt tt Eq.refl

wl1734 : Base 4 → ⟪ (ℓ "交亐亏亐") ⟫ʷ ≈ ⟪ (ℓ "亏亐交") ⟫ʷ
wl1734 c4 = lw4 c4 (ℓ "交亐亏亐") (ℓ "亏亐交") tt tt Eq.refl

wl1735 : Base 4 → ⟪ (ℓ "亐亏") ⟫ʷ ≈ ⟪ (ℓ "亏亐") ⟫ʷ
wl1735 c4 = lw4 c4 (ℓ "亐亏") (ℓ "亏亐") tt tt Eq.refl

wl1736 : Base 4 → ⟪ (ℓ "书些亏") ⟫ʷ ≈ ⟪ (ℓ "亏书些") ⟫ʷ
wl1736 c4 = lw4 c4 (ℓ "书些亏") (ℓ "亏书些") tt tt Eq.refl

wl1737 : Base 4 → ⟪ (ℓ "乎亏") ⟫ʷ ≈ ⟪ (ℓ "亏乎") ⟫ʷ
wl1737 c4 = lw4 c4 (ℓ "乎亏") (ℓ "亏乎") tt tt Eq.refl

wl1738 : Base 4 → ⟪ (ℓ "乏亏") ⟫ʷ ≈ ⟪ (ℓ "亏乏") ⟫ʷ
wl1738 c4 = lw4 c4 (ℓ "乏亏") (ℓ "亏乏") tt tt Eq.refl

wl1739 : Base 4 → ⟪ (ℓ "丞主上亚") ⟫ʷ ≈ ⟪ (ℓ "亚丞主上") ⟫ʷ
wl1739 c4 = lw4 c4 (ℓ "丞主上亚") (ℓ "亚丞主上") tt tt Eq.refl
