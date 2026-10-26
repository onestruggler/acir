------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL04 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl0701 : Base 4 → ⟪ (ℓ "亐书二") ⟫ʷ ≈ ⟪ (ℓ "书亐") ⟫ʷ
wl0701 c4 = lw4 c4 (ℓ "亐书二") (ℓ "书亐") tt tt Eq.refl

wl0702 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乇了么了乕") ⟫ʷ
wl0702 c4 = lw0 c4 (ℓ "亨") (ℓ "乇了么了乕") tt tt Eq.refl

wl0703 : Base 4 → ⟪ (ℓ "亐么") ⟫ʷ ≈ ⟪ (ℓ "么亐") ⟫ʷ
wl0703 c4 = lw4 c4 (ℓ "亐么") (ℓ "么亐") tt tt Eq.refl

wl0704 : Base 4 → ⟪ (ℓ "二亐") ⟫ʷ ≈ ⟪ (ℓ "亐二") ⟫ʷ
wl0704 c4 = lw4 c4 (ℓ "二亐") (ℓ "亐二") tt tt Eq.refl

wl0705 : Base 4 → ⟪ (ℓ "书二二") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
wl0705 c4 = lw4 c4 (ℓ "书二二") (ℓ "书") tt tt Eq.refl

wl0706 : Base 4 → ⟪ (ℓ "亐乶") ⟫ʷ ≈ ⟪ (ℓ "乶亐") ⟫ʷ
wl0706 c4 = lw4 c4 (ℓ "亐乶") (ℓ "乶亐") tt tt Eq.refl

wl0707 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乎争乏争乕") ⟫ʷ
wl0707 c4 = lw0 c4 (ℓ "京") (ℓ "乎争乏争乕") tt tt Eq.refl

wl0708 : Base 4 → ⟪ (ℓ "亭乇亭么並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亭乇亭么") ⟫ʷ
wl0708 c4 = lw0 c4 (ℓ "亭乇亭么並亊並") (ℓ "並亊並亭乇亭么") tt tt Eq.refl

wl0709 : Base 4 → ⟪ (ℓ "並丢") ⟫ʷ ≈ ⟪ (ℓ "一丣並") ⟫ʷ
wl0709 c4 = lw1 c4 (ℓ "並丢") (ℓ "一丣並") tt tt Eq.refl

wl0710 : Base 4 → ⟪ (ℓ "丢並") ⟫ʷ ≈ ⟪ (ℓ "並一丣") ⟫ʷ
wl0710 c4 = lw1 c4 (ℓ "丢並") (ℓ "並一丣") tt tt Eq.refl

wl0711 : Base 4 → ⟪ (ℓ "丐乖並") ⟫ʷ ≈ ⟪ (ℓ "並乕") ⟫ʷ
wl0711 c4 = lw0 c4 (ℓ "丐乖並") (ℓ "並乕") tt tt Eq.refl

wl0712 : Base 4 → ⟪ (ℓ "丐乖亦") ⟫ʷ ≈ ⟪ (ℓ "亦丐乖") ⟫ʷ
wl0712 c4 = lw0 c4 (ℓ "丐乖亦") (ℓ "亦丐乖") tt tt Eq.refl

wl0713 : Base 4 → ⟪ (ℓ "乕並") ⟫ʷ ≈ ⟪ (ℓ "並丐乖") ⟫ʷ
wl0713 c4 = lw0 c4 (ℓ "乕並") (ℓ "並丐乖") tt tt Eq.refl

wl0714 : Base 4 → ⟪ (ℓ "世乪並") ⟫ʷ ≈ ⟪ (ℓ "並乩") ⟫ʷ
wl0714 c4 = lw0 c4 (ℓ "世乪並") (ℓ "並乩") tt tt Eq.refl

wl0715 : Base 4 → ⟪ (ℓ "世乪亮") ⟫ʷ ≈ ⟪ (ℓ "亮世乪") ⟫ʷ
wl0715 c4 = lw0 c4 (ℓ "世乪亮") (ℓ "亮世乪") tt tt Eq.refl

wl0716 : Base 4 → ⟪ (ℓ "乩並") ⟫ʷ ≈ ⟪ (ℓ "並世乪") ⟫ʷ
wl0716 c4 = lw0 c4 (ℓ "乩並") (ℓ "並世乪") tt tt Eq.refl

wl0717 : Base 4 → ⟪ (ℓ "东乺並") ⟫ʷ ≈ ⟪ (ℓ "並乹") ⟫ʷ
wl0717 c4 = lw0 c4 (ℓ "东乺並") (ℓ "並乹") tt tt Eq.refl

wl0718 : Base 4 → ⟪ (ℓ "东乺亦") ⟫ʷ ≈ ⟪ (ℓ "亦东乺") ⟫ʷ
wl0718 c4 = lw0 c4 (ℓ "东乺亦") (ℓ "亦东乺") tt tt Eq.refl

wl0719 : Base 4 → ⟪ (ℓ "乹並") ⟫ʷ ≈ ⟪ (ℓ "並东乺") ⟫ʷ
wl0719 c4 = lw0 c4 (ℓ "乹並") (ℓ "並东乺") tt tt Eq.refl

wl0720 : Base 4 → ⟪ (ℓ "丒亄丢並") ⟫ʷ ≈ ⟪ (ℓ "並亄") ⟫ʷ
wl0720 c4 = lw0 c4 (ℓ "丒亄丢並") (ℓ "並亄") tt tt Eq.refl

wl0721 : Base 4 → ⟪ (ℓ "丒亄丢亪") ⟫ʷ ≈ ⟪ (ℓ "亪丒亄丢") ⟫ʷ
wl0721 c4 = lw0 c4 (ℓ "丒亄丢亪") (ℓ "亪丒亄丢") tt tt Eq.refl

wl0722 : Base 4 → ⟪ (ℓ "亘丒") ⟫ʷ ≈ ⟪ (ℓ "丒亘") ⟫ʷ
wl0722 c4 = lw4 c4 (ℓ "亘丒") (ℓ "丒亘") tt tt Eq.refl

wl0723 : Base 4 → ⟪ (ℓ "亄並") ⟫ʷ ≈ ⟪ (ℓ "並丒亄丢") ⟫ʷ
wl0723 c4 = lw0 c4 (ℓ "亄並") (ℓ "並丒亄丢") tt tt Eq.refl

wl0724 : Base 4 → ⟪ (ℓ "亇") ⟫ʷ ≈ ⟪ (ℓ "乪丙乪丘乪") ⟫ʷ
wl0724 c4 = lw0 c4 (ℓ "亇") (ℓ "乪丙乪丘乪") tt tt Eq.refl

wl0725 : Base 4 → ⟪ (ℓ "丘亇丢並") ⟫ʷ ≈ ⟪ (ℓ "並亇") ⟫ʷ
wl0725 c4 = lw0 c4 (ℓ "丘亇丢並") (ℓ "並亇") tt tt Eq.refl

wl0726 : Base 4 → ⟪ (ℓ "丘亇丢亮") ⟫ʷ ≈ ⟪ (ℓ "亮丘亇丢") ⟫ʷ
wl0726 c4 = lw0 c4 (ℓ "丘亇丢亮") (ℓ "亮丘亇丢") tt tt Eq.refl

wl0727 : Base 4 → ⟪ (ℓ "丢亦") ⟫ʷ ≈ ⟪ (ℓ "亦丢") ⟫ʷ
wl0727 c4 = lw0 c4 (ℓ "丢亦") (ℓ "亦丢") tt tt Eq.refl

wl0728 : Base 4 → ⟪ (ℓ "亇並") ⟫ʷ ≈ ⟪ (ℓ "並丘亇丢") ⟫ʷ
wl0728 c4 = lw0 c4 (ℓ "亇並") (ℓ "並丘亇丢") tt tt Eq.refl

wl0729 : Base 4 → ⟪ (ℓ "丞亊丢並") ⟫ʷ ≈ ⟪ (ℓ "並亊") ⟫ʷ
wl0729 c4 = lw0 c4 (ℓ "丞亊丢並") (ℓ "並亊") tt tt Eq.refl

wl0730 : Base 4 → ⟪ (ℓ "丞亊丢亱") ⟫ʷ ≈ ⟪ (ℓ "亱丞亊丢") ⟫ʷ
wl0730 c4 = lw0 c4 (ℓ "丞亊丢亱") (ℓ "亱丞亊丢") tt tt Eq.refl

wl0731 : Base 4 → ⟪ (ℓ "亊並") ⟫ʷ ≈ ⟪ (ℓ "並丞亊丢") ⟫ʷ
wl0731 c4 = lw0 c4 (ℓ "亊並") (ℓ "並丞亊丢") tt tt Eq.refl

wl0732 : Base 4 → ⟪ (ℓ "世乪亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏世乪") ⟫ʷ
wl0732 c4 = lw0 c4 (ℓ "世乪亲乎亲乏") (ℓ "亲乎亲乏世乪") tt tt Eq.refl

wl0733 : Base 4 → ⟪ (ℓ "东乺亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏东乺") ⟫ʷ
wl0733 c4 = lw0 c4 (ℓ "东乺亲乎亲乏") (ℓ "亲乎亲乏东乺") tt tt Eq.refl

wl0734 : Base 4 → ⟪ (ℓ "丒亄丢亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏丒亄丢") ⟫ʷ
wl0734 c4 = lw0 c4 (ℓ "丒亄丢亲乎亲乏") (ℓ "亲乎亲乏丒亄丢") tt tt Eq.refl

wl0735 : Base 4 → ⟪ (ℓ "丒亙") ⟫ʷ ≈ ⟪ (ℓ "亙丒") ⟫ʷ
wl0735 c4 = lw4 c4 (ℓ "丒亙") (ℓ "亙丒") tt tt Eq.refl

wl0736 : Base 4 → ⟪ (ℓ "丘亇丢亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏丘亇丢") ⟫ʷ
wl0736 c4 = lw0 c4 (ℓ "丘亇丢亲乎亲乏") (ℓ "亲乎亲乏丘亇丢") tt tt Eq.refl

wl0737 : Base 4 → ⟪ (ℓ "亐丘") ⟫ʷ ≈ ⟪ (ℓ "丘亐") ⟫ʷ
wl0737 c4 = lw4 c4 (ℓ "亐丘") (ℓ "丘亐") tt tt Eq.refl

wl0738 : Base 4 → ⟪ (ℓ "丞亊丢亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏丞亊丢") ⟫ʷ
wl0738 c4 = lw0 c4 (ℓ "丞亊丢亲乎亲乏") (ℓ "亲乎亲乏丞亊丢") tt tt Eq.refl

wl0739 : Base 4 → ⟪ (ℓ "丐乖亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么丐乖") ⟫ʷ
wl0739 c4 = lw0 c4 (ℓ "丐乖亭乇亭么") (ℓ "亭乇亭么丐乖") tt tt Eq.refl

wl0740 : Base 4 → ⟪ (ℓ "东乺亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么东乺") ⟫ʷ
wl0740 c4 = lw0 c4 (ℓ "东乺亭乇亭么") (ℓ "亭乇亭么东乺") tt tt Eq.refl

wl0741 : Base 4 → ⟪ (ℓ "丒亄丢亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么丒亄丢") ⟫ʷ
wl0741 c4 = lw0 c4 (ℓ "丒亄丢亭乇亭么") (ℓ "亭乇亭么丒亄丢") tt tt Eq.refl

wl0742 : Base 4 → ⟪ (ℓ "丘亇丢亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么丘亇丢") ⟫ʷ
wl0742 c4 = lw0 c4 (ℓ "丘亇丢亭乇亭么") (ℓ "亭乇亭么丘亇丢") tt tt Eq.refl

wl0743 : Base 4 → ⟪ (ℓ "丘云") ⟫ʷ ≈ ⟪ (ℓ "云丘") ⟫ʷ
wl0743 c4 = lw4 c4 (ℓ "丘云") (ℓ "云丘") tt tt Eq.refl

wl0744 : Base 4 → ⟪ (ℓ "丞亊丢亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么丞亊丢") ⟫ʷ
wl0744 c4 = lw0 c4 (ℓ "丞亊丢亭乇亭么") (ℓ "亭乇亭么丞亊丢") tt tt Eq.refl

wl0745 : Base 4 → ⟪ (ℓ "乒亮並") ⟫ʷ ≈ ⟪ (ℓ "並亮") ⟫ʷ
wl0745 c4 = lw0 c4 (ℓ "乒亮並") (ℓ "並亮") tt tt Eq.refl

wl0746 : Base 4 → ⟪ (ℓ "之乒亦") ⟫ʷ ≈ ⟪ (ℓ "亦乒") ⟫ʷ
wl0746 c4 = lw4 c4 (ℓ "之乒亦") (ℓ "亦乒") tt tt Eq.refl

wl0747 : Base 4 → ⟪ (ℓ "亦亮") ⟫ʷ ≈ ⟪ (ℓ "亪亮亦") ⟫ʷ
wl0747 c4 = lw0 c4 (ℓ "亦亮") (ℓ "亪亮亦") tt tt Eq.refl

wl0748 : Base 4 → ⟪ (ℓ "之亦") ⟫ʷ ≈ ⟪ (ℓ "亦之") ⟫ʷ
wl0748 c4 = lw4 c4 (ℓ "之亦") (ℓ "亦之") tt tt Eq.refl

wl0749 : Base 4 → ⟪ (ℓ "京亮") ⟫ʷ ≈ ⟪ (ℓ "亮京乗") ⟫ʷ
wl0749 c4 = lw0 c4 (ℓ "京亮") (ℓ "亮京乗") tt tt Eq.refl

wl0750 : Base 4 → ⟪ (ℓ "京乗亮京") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wl0750 c4 = lw0 c4 (ℓ "京乗亮京") (ℓ "亮") tt tt Eq.refl

wl0751 : Base 4 → ⟪ (ℓ "亘乄交") ⟫ʷ ≈ ⟪ (ℓ "乄亘") ⟫ʷ
wl0751 c4 = lw4 c4 (ℓ "亘乄交") (ℓ "乄亘") tt tt Eq.refl

wl0752 : Base 4 → ⟪ (ℓ "交亮") ⟫ʷ ≈ ⟪ (ℓ "亮交亨") ⟫ʷ
wl0752 c4 = lw0 c4 (ℓ "交亮") (ℓ "亮交亨") tt tt Eq.refl

wl0753 : Base 4 → ⟪ (ℓ "乄交交") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wl0753 c4 = lw4 c4 (ℓ "乄交交") (ℓ "乄") tt tt Eq.refl

wl0754 : Base 4 → ⟪ (ℓ "乩亮") ⟫ʷ ≈ ⟪ (ℓ "亮乩") ⟫ʷ
wl0754 c4 = lw0 c4 (ℓ "乩亮") (ℓ "亮乩") tt tt Eq.refl

wl0755 : Base 4 → ⟪ (ℓ "乄丬乄") ⟫ʷ ≈ ⟪ (ℓ "丫") ⟫ʷ
wl0755 c4 = lw4 c4 (ℓ "乄丬乄") (ℓ "丫") tt tt Eq.refl

wl0756 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亰亲乐亲亰乐") ⟫ʷ
wl0756 c4 = lw0 c4 (ℓ "亨") (ℓ "亰亲乐亲亰乐") tt tt Eq.refl

wl0757 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丯买丰买乢") ⟫ʷ
wl0757 c4 = lw4 c4 (ℓ "亘") (ℓ "丯买丰买乢") tt tt Eq.refl

wl0758 : Base 4 → ⟪ (ℓ "交亪") ⟫ʷ ≈ ⟪ (ℓ "亪京交") ⟫ʷ
wl0758 c4 = lw0 c4 (ℓ "交亪") (ℓ "亪京交") tt tt Eq.refl

wl0759 : Base 4 → ⟪ (ℓ "京交亪") ⟫ʷ ≈ ⟪ (ℓ "亪交") ⟫ʷ
wl0759 c4 = lw0 c4 (ℓ "京交亪") (ℓ "亪交") tt tt Eq.refl

wl0760 : Base 4 → ⟪ (ℓ "丟亪") ⟫ʷ ≈ ⟪ (ℓ "亪丟") ⟫ʷ
wl0760 c4 = lw0 c4 (ℓ "丟亪") (ℓ "亪丟") tt tt Eq.refl

wl0761 : Base 4 → ⟪ (ℓ "乹亪") ⟫ʷ ≈ ⟪ (ℓ "亪乹") ⟫ʷ
wl0761 c4 = lw0 c4 (ℓ "乹亪") (ℓ "亪乹") tt tt Eq.refl

wl0762 : Base 4 → ⟪ (ℓ "丞亪") ⟫ʷ ≈ ⟪ (ℓ "亪丞") ⟫ʷ
wl0762 c4 = lw0 c4 (ℓ "丞亪") (ℓ "亪丞") tt tt Eq.refl

wl0763 : Base 4 → ⟪ (ℓ "交丨") ⟫ʷ ≈ ⟪ (ℓ "丨交") ⟫ʷ
wl0763 c4 = lw4 c4 (ℓ "交丨") (ℓ "丨交") tt tt Eq.refl

wl0764 : Base 4 → ⟪ (ℓ "交乖") ⟫ʷ ≈ ⟪ (ℓ "乖交") ⟫ʷ
wl0764 c4 = lw0 c4 (ℓ "交乖") (ℓ "乖交") tt tt Eq.refl

wl0765 : Base 4 → ⟪ (ℓ "交乕") ⟫ʷ ≈ ⟪ (ℓ "乕交") ⟫ʷ
wl0765 c4 = lw0 c4 (ℓ "交乕") (ℓ "乕交") tt tt Eq.refl

wl0766 : Base 4 → ⟪ (ℓ "亨乗亪") ⟫ʷ ≈ ⟪ (ℓ "亪亨") ⟫ʷ
wl0766 c4 = lw0 c4 (ℓ "亨乗亪") (ℓ "亪亨") tt tt Eq.refl

wl0767 : Base 4 → ⟪ (ℓ "亨乗") ⟫ʷ ≈ ⟪ (ℓ "亪亨亪") ⟫ʷ
wl0767 c4 = lw0 c4 (ℓ "亨乗") (ℓ "亪亨亪") tt tt Eq.refl

wl0768 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乗亨乗") ⟫ʷ
wl0768 c4 = lw0 c4 (ℓ "亨") (ℓ "乗亨乗") tt tt Eq.refl

wl0769 : Base 4 → ⟪ (ℓ "交亮亨") ⟫ʷ ≈ ⟪ (ℓ "亮交") ⟫ʷ
wl0769 c4 = lw0 c4 (ℓ "交亮亨") (ℓ "亮交") tt tt Eq.refl

wl0770 : Base 4 → ⟪ (ℓ "交亨") ⟫ʷ ≈ ⟪ (ℓ "亨交") ⟫ʷ
wl0770 c4 = lw0 c4 (ℓ "交亨") (ℓ "亨交") tt tt Eq.refl

wl0771 : Base 4 → ⟪ (ℓ "书亪") ⟫ʷ ≈ ⟪ (ℓ "亪亮书") ⟫ʷ
wl0771 c4 = lw0 c4 (ℓ "书亪") (ℓ "亪亮书") tt tt Eq.refl

wl0772 : Base 4 → ⟪ (ℓ "亘丱书") ⟫ʷ ≈ ⟪ (ℓ "书亘") ⟫ʷ
wl0772 c4 = lw4 c4 (ℓ "亘丱书") (ℓ "书亘") tt tt Eq.refl

wl0773 : Base 4 → ⟪ (ℓ "亘丱") ⟫ʷ ≈ ⟪ (ℓ "书亘书") ⟫ʷ
wl0773 c4 = lw4 c4 (ℓ "亘丱") (ℓ "书亘书") tt tt Eq.refl

wl0774 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丱亘丱") ⟫ʷ
wl0774 c4 = lw4 c4 (ℓ "亘") (ℓ "丱亘丱") tt tt Eq.refl

wl0775 : Base 4 → ⟪ (ℓ "亪亮") ⟫ʷ ≈ ⟪ (ℓ "亮亪") ⟫ʷ
wl0775 c4 = lw0 c4 (ℓ "亪亮") (ℓ "亮亪") tt tt Eq.refl

wl0776 : Base 4 → ⟪ (ℓ "丘乇亃么亃乩丙") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wl0776 c4 = lw0 c4 (ℓ "丘乇亃么亃乩丙") (ℓ "亪") tt tt Eq.refl

wl0777 : Base 4 → ⟪ (ℓ "亪产") ⟫ʷ ≈ ⟪ (ℓ "产亪亮") ⟫ʷ
wl0777 c4 = lw0 c4 (ℓ "亪产") (ℓ "产亪亮") tt tt Eq.refl

wl0778 : Base 4 → ⟪ (ℓ "乖产") ⟫ʷ ≈ ⟪ (ℓ "产乖") ⟫ʷ
wl0778 c4 = lw0 c4 (ℓ "乖产") (ℓ "产乖") tt tt Eq.refl

wl0779 : Base 4 → ⟪ (ℓ "产亮") ⟫ʷ ≈ ⟪ (ℓ "亮产") ⟫ʷ
wl0779 c4 = lw0 c4 (ℓ "产亮") (ℓ "亮产") tt tt Eq.refl

wl0780 : Base 4 → ⟪ (ℓ "亪亮亮") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wl0780 c4 = lw0 c4 (ℓ "亪亮亮") (ℓ "亪") tt tt Eq.refl

wl0781 : Base 4 → ⟪ (ℓ "丞京丟") ⟫ʷ ≈ ⟪ (ℓ "亮") ⟫ʷ
wl0781 c4 = lw0 c4 (ℓ "丞京丟") (ℓ "亮") tt tt Eq.refl

wl0782 : Base 4 → ⟪ (ℓ "丞亘丟") ⟫ʷ ≈ ⟪ (ℓ "些") ⟫ʷ
wl0782 c4 = lw4 c4 (ℓ "丞亘丟") (ℓ "些") tt tt Eq.refl

wl0783 : Base 4 → ⟪ (ℓ "乖东亮丝") ⟫ʷ ≈ ⟪ (ℓ "亮京") ⟫ʷ
wl0783 c4 = lw0 c4 (ℓ "乖东亮丝") (ℓ "亮京") tt tt Eq.refl

wl0784 : Base 4 → ⟪ (ℓ "丰东些丝") ⟫ʷ ≈ ⟪ (ℓ "些亘") ⟫ʷ
wl0784 c4 = lw4 c4 (ℓ "丰东些丝") (ℓ "些亘") tt tt Eq.refl

wl0785 : Base 4 → ⟪ (ℓ "乖东") ⟫ʷ ≈ ⟪ (ℓ "东乖") ⟫ʷ
wl0785 c4 = lw0 c4 (ℓ "乖东") (ℓ "东乖") tt tt Eq.refl

wl0786 : Base 4 → ⟪ (ℓ "乖丝") ⟫ʷ ≈ ⟪ (ℓ "丝乖") ⟫ʷ
wl0786 c4 = lw0 c4 (ℓ "乖丝") (ℓ "丝乖") tt tt Eq.refl

wl0787 : Base 4 → ⟪ (ℓ "些些") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0787 c4 = lw4 c4 (ℓ "些些") [] tt tt Eq.refl

wl0788 : Base 4 → ⟪ (ℓ "亮亮") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0788 c4 = lw0 c4 (ℓ "亮亮") [] tt tt Eq.refl

wl0789 : Base 4 → ⟪ (ℓ "丷些") ⟫ʷ ≈ ⟪ (ℓ "些丷丰亘") ⟫ʷ
wl0789 c4 = lw4 c4 (ℓ "丷些") (ℓ "些丷丰亘") tt tt Eq.refl

wl0790 : Base 4 → ⟪ (ℓ "京乢") ⟫ʷ ≈ ⟪ (ℓ "乢京") ⟫ʷ
wl0790 c4 = lw0 c4 (ℓ "京乢") (ℓ "乢京") tt tt Eq.refl

wl0791 : Base 4 → ⟪ (ℓ "亘些") ⟫ʷ ≈ ⟪ (ℓ "些丱亘") ⟫ʷ
wl0791 c4 = lw4 c4 (ℓ "亘些") (ℓ "些丱亘") tt tt Eq.refl

wl0792 : Base 4 → ⟪ (ℓ "丰些") ⟫ʷ ≈ ⟪ (ℓ "些丰") ⟫ʷ
wl0792 c4 = lw4 c4 (ℓ "丰些") (ℓ "些丰") tt tt Eq.refl

wl0793 : Base 4 → ⟪ (ℓ "丷丰亘丰丱亘") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
wl0793 c4 = lw4 c4 (ℓ "丷丰亘丰丱亘") (ℓ "丷") tt tt Eq.refl

wl0794 : Base 4 → ⟪ (ℓ "书亮") ⟫ʷ ≈ ⟪ (ℓ "亮书") ⟫ʷ
wl0794 c4 = lw0 c4 (ℓ "书亮") (ℓ "亮书") tt tt Eq.refl

wl0795 : Base 4 → ⟪ (ℓ "丶丯亘书") ⟫ʷ ≈ ⟪ (ℓ "书丶") ⟫ʷ
wl0795 c4 = lw4 c4 (ℓ "丶丯亘书") (ℓ "书丶") tt tt Eq.refl

wl0796 : Base 4 → ⟪ (ℓ "丷丰亘书") ⟫ʷ ≈ ⟪ (ℓ "书丷") ⟫ʷ
wl0796 c4 = lw4 c4 (ℓ "丷丰亘书") (ℓ "书丷") tt tt Eq.refl

wl0797 : Base 4 → ⟪ (ℓ "亘丯") ⟫ʷ ≈ ⟪ (ℓ "丯亘") ⟫ʷ
wl0797 c4 = lw4 c4 (ℓ "亘丯") (ℓ "丯亘") tt tt Eq.refl

wl0798 : Base 4 → ⟪ (ℓ "丯丷丰") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
wl0798 c4 = lw4 c4 (ℓ "丯丷丰") (ℓ "丷") tt tt Eq.refl

wl0799 : Base 4 → ⟪ (ℓ "亘丷") ⟫ʷ ≈ ⟪ (ℓ "丷亘") ⟫ʷ
wl0799 c4 = lw4 c4 (ℓ "亘丷") (ℓ "丷亘") tt tt Eq.refl

wl0800 : Base 4 → ⟪ (ℓ "丶些") ⟫ʷ ≈ ⟪ (ℓ "些丶丯亘") ⟫ʷ
wl0800 c4 = lw4 c4 (ℓ "丶些") (ℓ "些丶丯亘") tt tt Eq.refl

wl0801 : Base 4 → ⟪ (ℓ "丯些") ⟫ʷ ≈ ⟪ (ℓ "些丯") ⟫ʷ
wl0801 c4 = lw4 c4 (ℓ "丯些") (ℓ "些丯") tt tt Eq.refl

wl0802 : Base 4 → ⟪ (ℓ "丶丯亘丯丱亘") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
wl0802 c4 = lw4 c4 (ℓ "丶丯亘丯丱亘") (ℓ "丶") tt tt Eq.refl

wl0803 : Base 4 → ⟪ (ℓ "京亮乗") ⟫ʷ ≈ ⟪ (ℓ "亮京") ⟫ʷ
wl0803 c4 = lw0 c4 (ℓ "京亮乗") (ℓ "亮京") tt tt Eq.refl

wl0804 : Base 4 → ⟪ (ℓ "京亮") ⟫ʷ ≈ ⟪ (ℓ "亮乗京") ⟫ʷ
wl0804 c4 = lw0 c4 (ℓ "京亮") (ℓ "亮乗京") tt tt Eq.refl

wl0805 : Base 4 → ⟪ (ℓ "交亪") ⟫ʷ ≈ ⟪ (ℓ "亪交京") ⟫ʷ
wl0805 c4 = lw0 c4 (ℓ "交亪") (ℓ "亪交京") tt tt Eq.refl

wl0806 : Base 4 → ⟪ (ℓ "书书") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0806 c4 = lw4 c4 (ℓ "书书") [] tt tt Eq.refl

wl0807 : Base 4 → ⟪ (ℓ "乺亦") ⟫ʷ ≈ ⟪ (ℓ "亦乺") ⟫ʷ
wl0807 c4 = lw0 c4 (ℓ "乺亦") (ℓ "亦乺") tt tt Eq.refl

wl0808 : Base 4 → ⟪ (ℓ "乹亦") ⟫ʷ ≈ ⟪ (ℓ "亦乹") ⟫ʷ
wl0808 c4 = lw0 c4 (ℓ "乹亦") (ℓ "亦乹") tt tt Eq.refl

wl0809 : Base 4 → ⟪ (ℓ "乶亦") ⟫ʷ ≈ ⟪ (ℓ "亦乶") ⟫ʷ
wl0809 c4 = lw4 c4 (ℓ "乶亦") (ℓ "亦乶") tt tt Eq.refl

wl0810 : Base 4 → ⟪ (ℓ "乶亮") ⟫ʷ ≈ ⟪ (ℓ "亮乶亪") ⟫ʷ
wl0810 c4 = lw0 c4 (ℓ "乶亮") (ℓ "亮乶亪") tt tt Eq.refl

wl0811 : Base 4 → ⟪ (ℓ "丶乶") ⟫ʷ ≈ ⟪ (ℓ "乶丶") ⟫ʷ
wl0811 c4 = lw4 c4 (ℓ "丶乶") (ℓ "乶丶") tt tt Eq.refl

wl0812 : Base 4 → ⟪ (ℓ "乶亪亮") ⟫ʷ ≈ ⟪ (ℓ "亮乶") ⟫ʷ
wl0812 c4 = lw0 c4 (ℓ "乶亪亮") (ℓ "亮乶") tt tt Eq.refl

wl0813 : Base 4 → ⟪ (ℓ "丷乶") ⟫ʷ ≈ ⟪ (ℓ "乶丷") ⟫ʷ
wl0813 c4 = lw4 c4 (ℓ "丷乶") (ℓ "乶丷") tt tt Eq.refl

wl0814 : Base 4 → ⟪ (ℓ "亐云丱云亐丱乥") ⟫ʷ ≈ ⟪ (ℓ "乥二亍丸亍二丸") ⟫ʷ
wl0814 c4 = lw4 c4 (ℓ "亐云丱云亐丱乥") (ℓ "乥二亍丸亍二丸") tt tt Eq.refl

wl0815 : Base 4 → ⟪ (ℓ "乥亮") ⟫ʷ ≈ ⟪ (ℓ "亪乥") ⟫ʷ
wl0815 c4 = lw0 c4 (ℓ "乥亮") (ℓ "亪乥") tt tt Eq.refl

wl0816 : Base 4 → ⟪ (ℓ "丯乥") ⟫ʷ ≈ ⟪ (ℓ "乥丶") ⟫ʷ
wl0816 c4 = lw4 c4 (ℓ "丯乥") (ℓ "乥丶") tt tt Eq.refl

wl0817 : Base 4 → ⟪ (ℓ "丰乥") ⟫ʷ ≈ ⟪ (ℓ "乥丷") ⟫ʷ
wl0817 c4 = lw4 c4 (ℓ "丰乥") (ℓ "乥丷") tt tt Eq.refl

wl0818 : Base 4 → ⟪ (ℓ "丰亙") ⟫ʷ ≈ ⟪ (ℓ "亙丰乣亘") ⟫ʷ
wl0818 c4 = lw4 c4 (ℓ "丰亙") (ℓ "亙丰乣亘") tt tt Eq.refl

wl0819 : Base 4 → ⟪ (ℓ "亘亙") ⟫ʷ ≈ ⟪ (ℓ "亙乤亘") ⟫ʷ
wl0819 c4 = lw4 c4 (ℓ "亘亙") (ℓ "亙乤亘") tt tt Eq.refl

wl0820 : Base 4 → ⟪ (ℓ "乣亙") ⟫ʷ ≈ ⟪ (ℓ "亙乣") ⟫ʷ
wl0820 c4 = lw4 c4 (ℓ "乣亙") (ℓ "亙乣") tt tt Eq.refl

wl0821 : Base 4 → ⟪ (ℓ "丰乣亘乣乤亘") ⟫ʷ ≈ ⟪ (ℓ "丰") ⟫ʷ
wl0821 c4 = lw4 c4 (ℓ "丰乣亘乣乤亘") (ℓ "丰") tt tt Eq.refl

wl0822 : Base 4 → ⟪ (ℓ "丯亙") ⟫ʷ ≈ ⟪ (ℓ "亙丯乢亘") ⟫ʷ
wl0822 c4 = lw4 c4 (ℓ "丯亙") (ℓ "亙丯乢亘") tt tt Eq.refl

wl0823 : Base 4 → ⟪ (ℓ "乢亙") ⟫ʷ ≈ ⟪ (ℓ "亙乢") ⟫ʷ
wl0823 c4 = lw4 c4 (ℓ "乢亙") (ℓ "亙乢") tt tt Eq.refl

wl0824 : Base 4 → ⟪ (ℓ "丯乢亘乢乤亘") ⟫ʷ ≈ ⟪ (ℓ "丯") ⟫ʷ
wl0824 c4 = lw4 c4 (ℓ "丯乢亘乢乤亘") (ℓ "丯") tt tt Eq.refl

wl0825 : Base 4 → ⟪ (ℓ "亘乤亙") ⟫ʷ ≈ ⟪ (ℓ "亙亘") ⟫ʷ
wl0825 c4 = lw4 c4 (ℓ "亘乤亙") (ℓ "亙亘") tt tt Eq.refl

wl0826 : Base 4 → ⟪ (ℓ "亘乤") ⟫ʷ ≈ ⟪ (ℓ "亙亘亙") ⟫ʷ
wl0826 c4 = lw4 c4 (ℓ "亘乤") (ℓ "亙亘亙") tt tt Eq.refl

wl0827 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "乤亘乤") ⟫ʷ
wl0827 c4 = lw4 c4 (ℓ "亘") (ℓ "乤亘乤") tt tt Eq.refl

wl0828 : Base 4 → ⟪ (ℓ "也亙") ⟫ʷ ≈ ⟪ (ℓ "亙也") ⟫ʷ
wl0828 c4 = lw4 c4 (ℓ "也亙") (ℓ "亙也") tt tt Eq.refl

wl0829 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乩乶乪乶乹") ⟫ʷ
wl0829 c4 = lw0 c4 (ℓ "亰") (ℓ "乩乶乪乶乹") tt tt Eq.refl

wl0830 : Base 4 → ⟪ (ℓ "之亙") ⟫ʷ ≈ ⟪ (ℓ "亙之云") ⟫ʷ
wl0830 c4 = lw4 c4 (ℓ "之亙") (ℓ "亙之云") tt tt Eq.refl

wl0831 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乕乳乖乳乹") ⟫ʷ
wl0831 c4 = lw0 c4 (ℓ "京") (ℓ "乕乳乖乳乹") tt tt Eq.refl

wl0832 : Base 4 → ⟪ (ℓ "乳亙") ⟫ʷ ≈ ⟪ (ℓ "亙乳") ⟫ʷ
wl0832 c4 = lw4 c4 (ℓ "乳亙") (ℓ "亙乳") tt tt Eq.refl

wl0833 : Base 4 → ⟪ (ℓ "云亙") ⟫ʷ ≈ ⟪ (ℓ "亙云") ⟫ʷ
wl0833 c4 = lw4 c4 (ℓ "云亙") (ℓ "亙云") tt tt Eq.refl

wl0834 : Base 4 → ⟪ (ℓ "之云云") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wl0834 c4 = lw4 c4 (ℓ "之云云") (ℓ "之") tt tt Eq.refl

wl0835 : Base 4 → ⟪ (ℓ "也之也") ⟫ʷ ≈ ⟪ (ℓ "乊") ⟫ʷ
wl0835 c4 = lw4 c4 (ℓ "也之也") (ℓ "乊") tt tt Eq.refl

wl0836 : Base 4 → ⟪ (ℓ "亰也") ⟫ʷ ≈ ⟪ (ℓ "也亰") ⟫ʷ
wl0836 c4 = lw0 c4 (ℓ "亰也") (ℓ "也亰") tt tt Eq.refl

wl0837 : Base 4 → ⟪ (ℓ "亰京亰京亰") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl0837 c4 = lw0 c4 (ℓ "亰京亰京亰") (ℓ "亰") tt tt Eq.refl

wl0838 : Base 4 → ⟪ (ℓ "亐乊") ⟫ʷ ≈ ⟪ (ℓ "乊亘") ⟫ʷ
wl0838 c4 = lw4 c4 (ℓ "亐乊") (ℓ "乊亘") tt tt Eq.refl

wl0839 : Base 4 → ⟪ (ℓ "乊亙") ⟫ʷ ≈ ⟪ (ℓ "云乊") ⟫ʷ
wl0839 c4 = lw4 c4 (ℓ "乊亙") (ℓ "云乊") tt tt Eq.refl

wl0840 : Base 4 → ⟪ (ℓ "亘乊") ⟫ʷ ≈ ⟪ (ℓ "乊亐") ⟫ʷ
wl0840 c4 = lw4 c4 (ℓ "亘乊") (ℓ "乊亐") tt tt Eq.refl

wl0841 : Base 4 → ⟪ (ℓ "乊亓") ⟫ʷ ≈ ⟪ (ℓ "些乊") ⟫ʷ
wl0841 c4 = lw4 c4 (ℓ "乊亓") (ℓ "些乊") tt tt Eq.refl

wl0842 : Base 4 → ⟪ (ℓ "亰乫亲") ⟫ʷ ≈ ⟪ (ℓ "亲亰") ⟫ʷ
wl0842 c4 = lw0 c4 (ℓ "亰乫亲") (ℓ "亲亰") tt tt Eq.refl

wl0843 : Base 4 → ⟪ (ℓ "亰乫") ⟫ʷ ≈ ⟪ (ℓ "亲亰亲") ⟫ʷ
wl0843 c4 = lw0 c4 (ℓ "亰乫") (ℓ "亲亰亲") tt tt Eq.refl

wl0844 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乫亰乫") ⟫ʷ
wl0844 c4 = lw0 c4 (ℓ "亰") (ℓ "乫亰乫") tt tt Eq.refl

wl0845 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "交亦丱亦交丱") ⟫ʷ
wl0845 c4 = lw4 c4 (ℓ "亐") (ℓ "交亦丱亦交丱") tt tt Eq.refl

wl0846 : Base 4 → ⟪ (ℓ "亰亲") ⟫ʷ ≈ ⟪ (ℓ "亲亰乫") ⟫ʷ
wl0846 c4 = lw0 c4 (ℓ "亰亲") (ℓ "亲亰乫") tt tt Eq.refl

wl0847 : Base 4 → ⟪ (ℓ "亰乫亲亰") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wl0847 c4 = lw0 c4 (ℓ "亰乫亲亰") (ℓ "亲") tt tt Eq.refl

wl0848 : Base 4 → ⟪ (ℓ "亃亲") ⟫ʷ ≈ ⟪ (ℓ "亲亃") ⟫ʷ
wl0848 c4 = lw0 c4 (ℓ "亃亲") (ℓ "亲亃") tt tt Eq.refl

wl0849 : Base 4 → ⟪ (ℓ "乙亲") ⟫ʷ ≈ ⟪ (ℓ "亲乙产") ⟫ʷ
wl0849 c4 = lw0 c4 (ℓ "乙亲") (ℓ "亲乙产") tt tt Eq.refl

wl0850 : Base 4 → ⟪ (ℓ "亐产二") ⟫ʷ ≈ ⟪ (ℓ "产亐") ⟫ʷ
wl0850 c4 = lw4 c4 (ℓ "亐产二") (ℓ "产亐") tt tt Eq.refl

wl0851 : Base 4 → ⟪ (ℓ "也亲") ⟫ʷ ≈ ⟪ (ℓ "亲也") ⟫ʷ
wl0851 c4 = lw0 c4 (ℓ "也亲") (ℓ "亲也") tt tt Eq.refl

wl0852 : Base 4 → ⟪ (ℓ "产亲") ⟫ʷ ≈ ⟪ (ℓ "亲产") ⟫ʷ
wl0852 c4 = lw0 c4 (ℓ "产亲") (ℓ "亲产") tt tt Eq.refl

wl0853 : Base 4 → ⟪ (ℓ "乙产产") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wl0853 c4 = lw0 c4 (ℓ "乙产产") (ℓ "乙") tt tt Eq.refl

wl0854 : Base 4 → ⟪ (ℓ "交乘") ⟫ʷ ≈ ⟪ (ℓ "乘亰") ⟫ʷ
wl0854 c4 = lw0 c4 (ℓ "交乘") (ℓ "乘亰") tt tt Eq.refl

wl0855 : Base 4 → ⟪ (ℓ "乘亲") ⟫ʷ ≈ ⟪ (ℓ "产乘") ⟫ʷ
wl0855 c4 = lw0 c4 (ℓ "乘亲") (ℓ "产乘") tt tt Eq.refl

wl0856 : Base 4 → ⟪ (ℓ "亰乘") ⟫ʷ ≈ ⟪ (ℓ "乘交") ⟫ʷ
wl0856 c4 = lw0 c4 (ℓ "亰乘") (ℓ "乘交") tt tt Eq.refl

wl0857 : Base 4 → ⟪ (ℓ "乘亦") ⟫ʷ ≈ ⟪ (ℓ "亱乘") ⟫ʷ
wl0857 c4 = lw0 c4 (ℓ "乘亦") (ℓ "亱乘") tt tt Eq.refl

wl0858 : Base 4 → ⟪ (ℓ "乙产") ⟫ʷ ≈ ⟪ (ℓ "产乙") ⟫ʷ
wl0858 c4 = lw0 c4 (ℓ "乙产") (ℓ "产乙") tt tt Eq.refl

wl0859 : Base 4 → ⟪ (ℓ "亐产") ⟫ʷ ≈ ⟪ (ℓ "产亐二") ⟫ʷ
wl0859 c4 = lw4 c4 (ℓ "亐产") (ℓ "产亐二") tt tt Eq.refl

wl0860 : Base 4 → ⟪ (ℓ "亃产") ⟫ʷ ≈ ⟪ (ℓ "产亃亲") ⟫ʷ
wl0860 c4 = lw0 c4 (ℓ "亃产") (ℓ "产亃亲") tt tt Eq.refl

wl0861 : Base 4 → ⟪ (ℓ "丯产") ⟫ʷ ≈ ⟪ (ℓ "产丯") ⟫ʷ
wl0861 c4 = lw4 c4 (ℓ "丯产") (ℓ "产丯") tt tt Eq.refl

wl0862 : Base 4 → ⟪ (ℓ "乭产") ⟫ʷ ≈ ⟪ (ℓ "产乭") ⟫ʷ
wl0862 c4 = lw0 c4 (ℓ "乭产") (ℓ "产乭") tt tt Eq.refl

wl0863 : Base 4 → ⟪ (ℓ "亃亲亲") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wl0863 c4 = lw0 c4 (ℓ "亃亲亲") (ℓ "亃") tt tt Eq.refl

wl0864 : Base 4 → ⟪ (ℓ "乘产") ⟫ʷ ≈ ⟪ (ℓ "亲乘") ⟫ʷ
wl0864 c4 = lw0 c4 (ℓ "乘产") (ℓ "亲乘") tt tt Eq.refl

wl0865 : Base 4 → ⟪ (ℓ "乘亱") ⟫ʷ ≈ ⟪ (ℓ "亦乘") ⟫ʷ
wl0865 c4 = lw0 c4 (ℓ "乘亱") (ℓ "亦乘") tt tt Eq.refl

wl0866 : Base 4 → ⟪ (ℓ "亐个亓") ⟫ʷ ≈ ⟪ (ℓ "亓亐") ⟫ʷ
wl0866 c4 = lw4 c4 (ℓ "亐个亓") (ℓ "亓亐") tt tt Eq.refl

wl0867 : Base 4 → ⟪ (ℓ "亐个") ⟫ʷ ≈ ⟪ (ℓ "亓亐亓") ⟫ʷ
wl0867 c4 = lw4 c4 (ℓ "亐个") (ℓ "亓亐亓") tt tt Eq.refl

wl0868 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "个亐个") ⟫ʷ
wl0868 c4 = lw4 c4 (ℓ "亐") (ℓ "个亐个") tt tt Eq.refl

wl0869 : Base 4 → ⟪ (ℓ "丞乇乳么乳乢丟") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl0869 c4 = lw4 c4 (ℓ "丞乇乳么乳乢丟") (ℓ "产") tt tt Eq.refl

wl0870 : Base 4 → ⟪ (ℓ "产二二") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl0870 c4 = lw4 c4 (ℓ "产二二") (ℓ "产") tt tt Eq.refl

wl0871 : Base 4 → ⟪ (ℓ "亨产") ⟫ʷ ≈ ⟪ (ℓ "产亨") ⟫ʷ
wl0871 c4 = lw0 c4 (ℓ "亨产") (ℓ "产亨") tt tt Eq.refl

wl0872 : Base 4 → ⟪ (ℓ "之云") ⟫ʷ ≈ ⟪ (ℓ "云之") ⟫ʷ
wl0872 c4 = lw4 c4 (ℓ "之云") (ℓ "云之") tt tt Eq.refl

wl0873 : Base 4 → ⟪ (ℓ "也云") ⟫ʷ ≈ ⟪ (ℓ "云也亙") ⟫ʷ
wl0873 c4 = lw4 c4 (ℓ "也云") (ℓ "云也亙") tt tt Eq.refl

wl0874 : Base 4 → ⟪ (ℓ "乶云") ⟫ʷ ≈ ⟪ (ℓ "云乶") ⟫ʷ
wl0874 c4 = lw4 c4 (ℓ "乶云") (ℓ "云乶") tt tt Eq.refl

wl0875 : Base 4 → ⟪ (ℓ "也亙亙") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wl0875 c4 = lw4 c4 (ℓ "也亙亙") (ℓ "也") tt tt Eq.refl

wl0876 : Base 4 → ⟪ (ℓ "乊云") ⟫ʷ ≈ ⟪ (ℓ "亙乊") ⟫ʷ
wl0876 c4 = lw4 c4 (ℓ "乊云") (ℓ "亙乊") tt tt Eq.refl

wl0877 : Base 4 → ⟪ (ℓ "乊些") ⟫ʷ ≈ ⟪ (ℓ "亓乊") ⟫ʷ
wl0877 c4 = lw4 c4 (ℓ "乊些") (ℓ "亓乊") tt tt Eq.refl

wl0878 : Base 4 → ⟪ (ℓ "乪产") ⟫ʷ ≈ ⟪ (ℓ "产乪") ⟫ʷ
wl0878 c4 = lw0 c4 (ℓ "乪产") (ℓ "产乪") tt tt Eq.refl

wl0879 : Base 4 → ⟪ (ℓ "乩产") ⟫ʷ ≈ ⟪ (ℓ "产乩") ⟫ʷ
wl0879 c4 = lw0 c4 (ℓ "乩产") (ℓ "产乩") tt tt Eq.refl

wl0880 : Base 4 → ⟪ (ℓ "书产") ⟫ʷ ≈ ⟪ (ℓ "产书") ⟫ʷ
wl0880 c4 = lw4 c4 (ℓ "书产") (ℓ "产书") tt tt Eq.refl

wl0881 : Base 4 → ⟪ (ℓ "乎产") ⟫ʷ ≈ ⟪ (ℓ "产乎乇交") ⟫ʷ
wl0881 c4 = lw4 c4 (ℓ "乎产") (ℓ "产乎乇交") tt tt Eq.refl

wl0882 : Base 4 → ⟪ (ℓ "交产") ⟫ʷ ≈ ⟪ (ℓ "产义交") ⟫ʷ
wl0882 c4 = lw4 c4 (ℓ "交产") (ℓ "产义交") tt tt Eq.refl

wl0883 : Base 4 → ⟪ (ℓ "乇产") ⟫ʷ ≈ ⟪ (ℓ "产乇") ⟫ʷ
wl0883 c4 = lw4 c4 (ℓ "乇产") (ℓ "产乇") tt tt Eq.refl

wl0884 : Base 4 → ⟪ (ℓ "乎乇交乇义交") ⟫ʷ ≈ ⟪ (ℓ "乎") ⟫ʷ
wl0884 c4 = lw4 c4 (ℓ "乎乇交乇义交") (ℓ "乎") tt tt Eq.refl

wl0885 : Base 4 → ⟪ (ℓ "乏产") ⟫ʷ ≈ ⟪ (ℓ "产乏么交") ⟫ʷ
wl0885 c4 = lw4 c4 (ℓ "乏产") (ℓ "产乏么交") tt tt Eq.refl

wl0886 : Base 4 → ⟪ (ℓ "么产") ⟫ʷ ≈ ⟪ (ℓ "产么") ⟫ʷ
wl0886 c4 = lw4 c4 (ℓ "么产") (ℓ "产么") tt tt Eq.refl

wl0887 : Base 4 → ⟪ (ℓ "乏么交么义交") ⟫ʷ ≈ ⟪ (ℓ "乏") ⟫ʷ
wl0887 c4 = lw4 c4 (ℓ "乏么交么义交") (ℓ "乏") tt tt Eq.refl

wl0888 : Base 4 → ⟪ (ℓ "丘乩之乪之乕丙") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wl0888 c4 = lw0 c4 (ℓ "丘乩之乪之乕丙") (ℓ "亪") tt tt Eq.refl

wl0889 : Base 4 → ⟪ (ℓ "义交产") ⟫ʷ ≈ ⟪ (ℓ "产交") ⟫ʷ
wl0889 c4 = lw4 c4 (ℓ "义交产") (ℓ "产交") tt tt Eq.refl

wl0890 : Base 4 → ⟪ (ℓ "交亪京") ⟫ʷ ≈ ⟪ (ℓ "亪京交京") ⟫ʷ
wl0890 c4 = lw0 c4 (ℓ "交亪京") (ℓ "亪京交京") tt tt Eq.refl

wl0891 : Base 4 → ⟪ (ℓ "交京亪京") ⟫ʷ ≈ ⟪ (ℓ "亪京交") ⟫ʷ
wl0891 c4 = lw0 c4 (ℓ "交京亪京") (ℓ "亪京交") tt tt Eq.refl

wl0892 : Base 4 → ⟪ (ℓ "交並") ⟫ʷ ≈ ⟪ (ℓ "並交") ⟫ʷ
wl0892 c4 = lw0 c4 (ℓ "交並") (ℓ "並交") tt tt Eq.refl

wl0893 : Base 4 → ⟪ (ℓ "京亪") ⟫ʷ ≈ ⟪ (ℓ "亪京") ⟫ʷ
wl0893 c4 = lw0 c4 (ℓ "京亪") (ℓ "亪京") tt tt Eq.refl

wl0894 : Base 4 → ⟪ (ℓ "书亲並") ⟫ʷ ≈ ⟪ (ℓ "並亲") ⟫ʷ
wl0894 c4 = lw0 c4 (ℓ "书亲並") (ℓ "並亲") tt tt Eq.refl

wl0895 : Base 4 → ⟪ (ℓ "书亲亪") ⟫ʷ ≈ ⟪ (ℓ "亪书亲") ⟫ʷ
wl0895 c4 = lw0 c4 (ℓ "书亲亪") (ℓ "亪书亲") tt tt Eq.refl

wl0896 : Base 4 → ⟪ (ℓ "乎並") ⟫ʷ ≈ ⟪ (ℓ "並乎") ⟫ʷ
wl0896 c4 = lw0 c4 (ℓ "乎並") (ℓ "並乎") tt tt Eq.refl

wl0897 : Base 4 → ⟪ (ℓ "丰乎") ⟫ʷ ≈ ⟪ (ℓ "乎丰") ⟫ʷ
wl0897 c4 = lw4 c4 (ℓ "丰乎") (ℓ "乎丰") tt tt Eq.refl

wl0898 : Base 4 → ⟪ (ℓ "乎亪") ⟫ʷ ≈ ⟪ (ℓ "亪乎") ⟫ʷ
wl0898 c4 = lw0 c4 (ℓ "乎亪") (ℓ "亪乎") tt tt Eq.refl

wl0899 : Base 4 → ⟪ (ℓ "丯乎") ⟫ʷ ≈ ⟪ (ℓ "乎丯") ⟫ʷ
wl0899 c4 = lw4 c4 (ℓ "丯乎") (ℓ "乎丯") tt tt Eq.refl

wl0900 : Base 4 → ⟪ (ℓ "乏並") ⟫ʷ ≈ ⟪ (ℓ "並乏") ⟫ʷ
wl0900 c4 = lw0 c4 (ℓ "乏並") (ℓ "並乏") tt tt Eq.refl

wl0901 : Base 4 → ⟪ (ℓ "丰乏") ⟫ʷ ≈ ⟪ (ℓ "乏丰") ⟫ʷ
wl0901 c4 = lw4 c4 (ℓ "丰乏") (ℓ "乏丰") tt tt Eq.refl

wl0902 : Base 4 → ⟪ (ℓ "乏亪") ⟫ʷ ≈ ⟪ (ℓ "亪乏") ⟫ʷ
wl0902 c4 = lw0 c4 (ℓ "乏亪") (ℓ "亪乏") tt tt Eq.refl

wl0903 : Base 4 → ⟪ (ℓ "丯乏") ⟫ʷ ≈ ⟪ (ℓ "乏丯") ⟫ʷ
wl0903 c4 = lw4 c4 (ℓ "丯乏") (ℓ "乏丯") tt tt Eq.refl

wl0904 : Base 4 → ⟪ (ℓ "丷云") ⟫ʷ ≈ ⟪ (ℓ "云丷乏亐") ⟫ʷ
wl0904 c4 = lw4 c4 (ℓ "丷云") (ℓ "云丷乏亐") tt tt Eq.refl

wl0905 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乎为乏为丨") ⟫ʷ
wl0905 c4 = lw4 c4 (ℓ "亐") (ℓ "乎为乏为丨") tt tt Eq.refl

wl0906 : Base 4 → ⟪ (ℓ "亐云") ⟫ʷ ≈ ⟪ (ℓ "云乐亐") ⟫ʷ
wl0906 c4 = lw4 c4 (ℓ "亐云") (ℓ "云乐亐") tt tt Eq.refl

wl0907 : Base 4 → ⟪ (ℓ "乏云") ⟫ʷ ≈ ⟪ (ℓ "云乏") ⟫ʷ
wl0907 c4 = lw4 c4 (ℓ "乏云") (ℓ "云乏") tt tt Eq.refl

wl0908 : Base 4 → ⟪ (ℓ "丷乏亐乏乐亐") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
wl0908 c4 = lw4 c4 (ℓ "丷乏亐乏乐亐") (ℓ "丷") tt tt Eq.refl

wl0909 : Base 4 → ⟪ (ℓ "丶云") ⟫ʷ ≈ ⟪ (ℓ "云丶乎亐") ⟫ʷ
wl0909 c4 = lw4 c4 (ℓ "丶云") (ℓ "云丶乎亐") tt tt Eq.refl

wl0910 : Base 4 → ⟪ (ℓ "乎云") ⟫ʷ ≈ ⟪ (ℓ "云乎") ⟫ʷ
wl0910 c4 = lw4 c4 (ℓ "乎云") (ℓ "云乎") tt tt Eq.refl

wl0911 : Base 4 → ⟪ (ℓ "丶乎亐乎乐亐") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
wl0911 c4 = lw4 c4 (ℓ "丶乎亐乎乐亐") (ℓ "丶") tt tt Eq.refl

wl0912 : Base 4 → ⟪ (ℓ "交乐亦") ⟫ʷ ≈ ⟪ (ℓ "亦交") ⟫ʷ
wl0912 c4 = lw4 c4 (ℓ "交乐亦") (ℓ "亦交") tt tt Eq.refl

wl0913 : Base 4 → ⟪ (ℓ "交乐") ⟫ʷ ≈ ⟪ (ℓ "亦交亦") ⟫ʷ
wl0913 c4 = lw4 c4 (ℓ "交乐") (ℓ "亦交亦") tt tt Eq.refl

wl0914 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乐交乐") ⟫ʷ
wl0914 c4 = lw4 c4 (ℓ "交") (ℓ "乐交乐") tt tt Eq.refl

wl0915 : Base 4 → ⟪ (ℓ "交亦") ⟫ʷ ≈ ⟪ (ℓ "亦交乐") ⟫ʷ
wl0915 c4 = lw4 c4 (ℓ "交亦") (ℓ "亦交乐") tt tt Eq.refl

wl0916 : Base 4 → ⟪ (ℓ "交乐亦交") ⟫ʷ ≈ ⟪ (ℓ "亦") ⟫ʷ
wl0916 c4 = lw4 c4 (ℓ "交乐亦交") (ℓ "亦") tt tt Eq.refl

wl0917 : Base 4 → ⟪ (ℓ "买亦") ⟫ʷ ≈ ⟪ (ℓ "亦买") ⟫ʷ
wl0917 c4 = lw4 c4 (ℓ "买亦") (ℓ "亦买") tt tt Eq.refl

wl0918 : Base 4 → ⟪ (ℓ "亰亦") ⟫ʷ ≈ ⟪ (ℓ "亦亰京") ⟫ʷ
wl0918 c4 = lw0 c4 (ℓ "亰亦") (ℓ "亦亰京") tt tt Eq.refl

wl0919 : Base 4 → ⟪ (ℓ "为亦") ⟫ʷ ≈ ⟪ (ℓ "亦为亏") ⟫ʷ
wl0919 c4 = lw4 c4 (ℓ "为亦") (ℓ "亦为亏") tt tt Eq.refl

wl0920 : Base 4 → ⟪ (ℓ "乄亦") ⟫ʷ ≈ ⟪ (ℓ "亦乄") ⟫ʷ
wl0920 c4 = lw4 c4 (ℓ "乄亦") (ℓ "亦乄") tt tt Eq.refl

wl0921 : Base 4 → ⟪ (ℓ "亏亦") ⟫ʷ ≈ ⟪ (ℓ "亦亏") ⟫ʷ
wl0921 c4 = lw4 c4 (ℓ "亏亦") (ℓ "亦亏") tt tt Eq.refl

wl0922 : Base 4 → ⟪ (ℓ "为亏亏") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
wl0922 c4 = lw4 c4 (ℓ "为亏亏") (ℓ "为") tt tt Eq.refl

wl0923 : Base 4 → ⟪ (ℓ "买为买") ⟫ʷ ≈ ⟪ (ℓ "丹") ⟫ʷ
wl0923 c4 = lw4 c4 (ℓ "买为买") (ℓ "丹") tt tt Eq.refl

wl0924 : Base 4 → ⟪ (ℓ "二丹") ⟫ʷ ≈ ⟪ (ℓ "丹交") ⟫ʷ
wl0924 c4 = lw4 c4 (ℓ "二丹") (ℓ "丹交") tt tt Eq.refl

wl0925 : Base 4 → ⟪ (ℓ "丹亦") ⟫ʷ ≈ ⟪ (ℓ "亏丹") ⟫ʷ
wl0925 c4 = lw4 c4 (ℓ "丹亦") (ℓ "亏丹") tt tt Eq.refl

wl0926 : Base 4 → ⟪ (ℓ "交丹") ⟫ʷ ≈ ⟪ (ℓ "丹二") ⟫ʷ
wl0926 c4 = lw4 c4 (ℓ "交丹") (ℓ "丹二") tt tt Eq.refl

wl0927 : Base 4 → ⟪ (ℓ "丹于") ⟫ʷ ≈ ⟪ (ℓ "亥丹") ⟫ʷ
wl0927 c4 = lw4 c4 (ℓ "丹于") (ℓ "亥丹") tt tt Eq.refl

wl0928 : Base 4 → ⟪ (ℓ "丹丹") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0928 c4 = lw4 c4 (ℓ "丹丹") [] tt tt Eq.refl

wl0929 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "丯乄丰乄乇") ⟫ʷ
wl0929 c4 = lw4 c4 (ℓ "二") (ℓ "丯乄丰乄乇") tt tt Eq.refl
