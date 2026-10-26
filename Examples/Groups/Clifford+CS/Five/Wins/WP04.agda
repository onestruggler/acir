------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP04 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp0675 : Base 4 → WsL → ⟪ (ℓ "亠丫") ⟫ʷ ≈ ⟪ (ℓ "丫京") ⟫ʷ
wp0675 c4 L = pw2 c4 L (ℓ "亠丫") (ℓ "丫京") tt tt Eq.refl

wp0676 : Base 4 → WsL → ⟪ (ℓ "丫亮") ⟫ʷ ≈ ⟪ (ℓ "亢丫") ⟫ʷ
wp0676 c4 L = pw2 c4 L (ℓ "丫亮") (ℓ "亢丫") tt tt Eq.refl

wp0677 : Base 4 → WsL → ⟪ (ℓ "京丫") ⟫ʷ ≈ ⟪ (ℓ "丫亠") ⟫ʷ
wp0677 c4 L = pw2 c4 L (ℓ "京丫") (ℓ "丫亠") tt tt Eq.refl

wp0678 : Base 4 → WsL → ⟪ (ℓ "丫亣") ⟫ʷ ≈ ⟪ (ℓ "亯丫") ⟫ʷ
wp0678 c4 L = pw2 c4 L (ℓ "丫亣") (ℓ "亯丫") tt tt Eq.refl

wp0679 : Base 4 → WsL → ⟪ (ℓ "亨丰") ⟫ʷ ≈ ⟪ (ℓ "丰亨") ⟫ʷ
wp0679 c4 L = pw3 c4 L (ℓ "亨丰") (ℓ "丰亨") tt tt Eq.refl

wp0680 : Base 4 → WsL → ⟪ (ℓ "亘乽") ⟫ʷ ≈ ⟪ (ℓ "乽亘") ⟫ʷ
wp0680 c4 L = pw1 c4 L (ℓ "亘乽") (ℓ "乽亘") tt tt Eq.refl

wp0681 : Base 4 → WsL → ⟪ (ℓ "丞丽买举买乹丟") ⟫ʷ ≈ ⟪ (ℓ "亢") ⟫ʷ
wp0681 c4 L = pw1 c4 L (ℓ "丞丽买举买乹丟") (ℓ "亢") tt tt Eq.refl

wp0682 : Base 4 → WsL → ⟪ (ℓ "举亪") ⟫ʷ ≈ ⟪ (ℓ "亪举") ⟫ʷ
wp0682 c4 L = pw3 c4 L (ℓ "举亪") (ℓ "亪举") tt tt Eq.refl

wp0683 : Base 4 → WsL → ⟪ (ℓ "丽亪") ⟫ʷ ≈ ⟪ (ℓ "亪丽") ⟫ʷ
wp0683 c4 L = pw3 c4 L (ℓ "丽亪") (ℓ "亪丽") tt tt Eq.refl

wp0684 : Base 4 → WsL → ⟪ (ℓ "亘乁") ⟫ʷ ≈ ⟪ (ℓ "乁亘") ⟫ʷ
wp0684 c4 L = pw1 c4 L (ℓ "亘乁") (ℓ "乁亘") tt tt Eq.refl

wp0685 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亜五亜") ⟫ʷ
wp0685 c4 L = pw3 c4 L (ℓ "五") (ℓ "亜五亜") tt tt Eq.refl

wp0686 : Base 4 → WsL → ⟪ (ℓ "五亪") ⟫ʷ ≈ ⟪ (ℓ "亪五") ⟫ʷ
wp0686 c4 L = pw3 c4 L (ℓ "五亪") (ℓ "亪五") tt tt Eq.refl

wp0687 : Base 4 → WsL → ⟪ (ℓ "五亢") ⟫ʷ ≈ ⟪ (ℓ "亢五") ⟫ʷ
wp0687 c4 L = pw2 c4 L (ℓ "五亢") (ℓ "亢五") tt tt Eq.refl

wp0688 : Base 4 → WsL → ⟪ (ℓ "丬亢") ⟫ʷ ≈ ⟪ (ℓ "亢丬") ⟫ʷ
wp0688 c4 L = pw2 c4 L (ℓ "丬亢") (ℓ "亢丬") tt tt Eq.refl

wp0689 : Base 4 → WsL → ⟪ (ℓ "亘亢") ⟫ʷ ≈ ⟪ (ℓ "亢亘亜") ⟫ʷ
wp0689 c4 L = pw1 c4 L (ℓ "亘亢") (ℓ "亢亘亜") tt tt Eq.refl

wp0690 : Base 4 → WsL → ⟪ (ℓ "乄亢") ⟫ʷ ≈ ⟪ (ℓ "亢乄亮") ⟫ʷ
wp0690 c4 L = pw2 c4 L (ℓ "乄亢") (ℓ "亢乄亮") tt tt Eq.refl

wp0691 : Base 4 → WsL → ⟪ (ℓ "乩亢") ⟫ʷ ≈ ⟪ (ℓ "亢乩") ⟫ʷ
wp0691 c4 L = pw1 c4 L (ℓ "乩亢") (ℓ "亢乩") tt tt Eq.refl

wp0692 : Base 4 → WsL → ⟪ (ℓ "亃亢") ⟫ʷ ≈ ⟪ (ℓ "亢亃") ⟫ʷ
wp0692 c4 L = pw2 c4 L (ℓ "亃亢") (ℓ "亢亃") tt tt Eq.refl

wp0693 : Base 4 → WsL → ⟪ (ℓ "乄亮亮") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wp0693 c4 L = pw2 c4 L (ℓ "乄亮亮") (ℓ "乄") tt tt Eq.refl

wp0694 : Base 4 → WsL → ⟪ (ℓ "亜亨亜亨亜") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp0694 c4 L = pw3 c4 L (ℓ "亜亨亜亨亜") (ℓ "亜") tt tt Eq.refl

wp0695 : Base 4 → WsL → ⟪ (ℓ "丫亢") ⟫ʷ ≈ ⟪ (ℓ "亮丫") ⟫ʷ
wp0695 c4 L = pw2 c4 L (ℓ "丫亢") (ℓ "亮丫") tt tt Eq.refl

wp0696 : Base 4 → WsL → ⟪ (ℓ "丫亯") ⟫ʷ ≈ ⟪ (ℓ "亣丫") ⟫ʷ
wp0696 c4 L = pw2 c4 L (ℓ "丫亯") (ℓ "亣丫") tt tt Eq.refl

wp0697 : Base 4 → WsL → ⟪ (ℓ "丱亪") ⟫ʷ ≈ ⟪ (ℓ "亪丱五") ⟫ʷ
wp0697 c4 L = pw3 c4 L (ℓ "丱亪") (ℓ "亪丱五") tt tt Eq.refl

wp0698 : Base 4 → WsL → ⟪ (ℓ "五亮") ⟫ʷ ≈ ⟪ (ℓ "亮五") ⟫ʷ
wp0698 c4 L = pw2 c4 L (ℓ "五亮") (ℓ "亮五") tt tt Eq.refl

wp0699 : Base 4 → WsL → ⟪ (ℓ "五丱") ⟫ʷ ≈ ⟪ (ℓ "丱五") ⟫ʷ
wp0699 c4 L = pw3 c4 L (ℓ "五丱") (ℓ "丱五") tt tt Eq.refl

wp0700 : Base 4 → WsL → ⟪ (ℓ "亠丙") ⟫ʷ ≈ ⟪ (ℓ "丙亠") ⟫ʷ
wp0700 c4 L = pw1 c4 L (ℓ "亠丙") (ℓ "丙亠") tt tt Eq.refl

wp0701 : Base 4 → WsL → ⟪ (ℓ "亠丘") ⟫ʷ ≈ ⟪ (ℓ "丘亠") ⟫ʷ
wp0701 c4 L = pw1 c4 L (ℓ "亠丘") (ℓ "丘亠") tt tt Eq.refl

wp0702 : Base 4 → WsL → ⟪ (ℓ "亠亮五") ⟫ʷ ≈ ⟪ (ℓ "亮亠") ⟫ʷ
wp0702 c4 L = pw2 c4 L (ℓ "亠亮五") (ℓ "亮亠") tt tt Eq.refl

wp0703 : Base 4 → WsL → ⟪ (ℓ "丰乖") ⟫ʷ ≈ ⟪ (ℓ "乖丰") ⟫ʷ
wp0703 c4 L = pw3 c4 L (ℓ "丰乖") (ℓ "乖丰") tt tt Eq.refl

wp0704 : Base 4 → WsL → ⟪ (ℓ "京丷") ⟫ʷ ≈ ⟪ (ℓ "丷京") ⟫ʷ
wp0704 c4 L = pw2 c4 L (ℓ "京丷") (ℓ "丷京") tt tt Eq.refl

wp0705 : Base 4 → WsL → ⟪ (ℓ "京买") ⟫ʷ ≈ ⟪ (ℓ "买京") ⟫ʷ
wp0705 c4 L = pw2 c4 L (ℓ "京买") (ℓ "买京") tt tt Eq.refl

wp0706 : Base 4 → WsL → ⟪ (ℓ "京丶") ⟫ʷ ≈ ⟪ (ℓ "丶京") ⟫ʷ
wp0706 c4 L = pw2 c4 L (ℓ "京丶") (ℓ "丶京") tt tt Eq.refl

wp0707 : Base 4 → WsL → ⟪ (ℓ "乄亪") ⟫ʷ ≈ ⟪ (ℓ "亪乄") ⟫ʷ
wp0707 c4 L = pw3 c4 L (ℓ "乄亪") (ℓ "亪乄") tt tt Eq.refl

wp0708 : Base 4 → WsL → ⟪ (ℓ "丬亪") ⟫ʷ ≈ ⟪ (ℓ "亪丬亞") ⟫ʷ
wp0708 c4 L = pw3 c4 L (ℓ "丬亪") (ℓ "亪丬亞") tt tt Eq.refl

wp0709 : Base 4 → WsL → ⟪ (ℓ "亘亞亠") ⟫ʷ ≈ ⟪ (ℓ "亞亘") ⟫ʷ
wp0709 c4 L = pw1 c4 L (ℓ "亘亞亠") (ℓ "亞亘") tt tt Eq.refl

wp0710 : Base 4 → WsL → ⟪ (ℓ "亀亪") ⟫ʷ ≈ ⟪ (ℓ "亪亀") ⟫ʷ
wp0710 c4 L = pw3 c4 L (ℓ "亀亪") (ℓ "亪亀") tt tt Eq.refl

wp0711 : Base 4 → WsL → ⟪ (ℓ "丬亞亞") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wp0711 c4 L = pw3 c4 L (ℓ "丬亞亞") (ℓ "丬") tt tt Eq.refl

wp0712 : Base 4 → WsL → ⟪ (ℓ "京乄") ⟫ʷ ≈ ⟪ (ℓ "乄京") ⟫ʷ
wp0712 c4 L = pw2 c4 L (ℓ "京乄") (ℓ "乄京") tt tt Eq.refl

wp0713 : Base 4 → WsL → ⟪ (ℓ "京亠京亠京") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wp0713 c4 L = pw2 c4 L (ℓ "京亠京亠京") (ℓ "京") tt tt Eq.refl

wp0714 : Base 4 → WsL → ⟪ (ℓ "丫亪") ⟫ʷ ≈ ⟪ (ℓ "亞丫") ⟫ʷ
wp0714 c4 L = pw3 c4 L (ℓ "丫亪") (ℓ "亞丫") tt tt Eq.refl

wp0715 : Base 4 → WsL → ⟪ (ℓ "丫亟") ⟫ʷ ≈ ⟪ (ℓ "享丫") ⟫ʷ
wp0715 c4 L = pw3 c4 L (ℓ "丫亟") (ℓ "享丫") tt tt Eq.refl

wp0716 : Base 4 → WsL → ⟪ (ℓ "亠亮") ⟫ʷ ≈ ⟪ (ℓ "亮五亠") ⟫ʷ
wp0716 c4 L = pw2 c4 L (ℓ "亠亮") (ℓ "亮五亠") tt tt Eq.refl

wp0717 : Base 4 → WsL → ⟪ (ℓ "亜乶亠") ⟫ʷ ≈ ⟪ (ℓ "乶亜") ⟫ʷ
wp0717 c4 L = pw1 c4 L (ℓ "亜乶亠") (ℓ "乶亜") tt tt Eq.refl

wp0718 : Base 4 → WsL → ⟪ (ℓ "乶亠亠") ⟫ʷ ≈ ⟪ (ℓ "乶") ⟫ʷ
wp0718 c4 L = pw1 c4 L (ℓ "乶亠亠") (ℓ "乶") tt tt Eq.refl

wp0719 : Base 4 → WsL → ⟪ (ℓ "乥亞") ⟫ʷ ≈ ⟪ (ℓ "亢乥") ⟫ʷ
wp0719 c4 L = pw1 c4 L (ℓ "乥亞") (ℓ "亢乥") tt tt Eq.refl

wp0720 : Base 4 → WsL → ⟪ (ℓ "五也亜") ⟫ʷ ≈ ⟪ (ℓ "也五") ⟫ʷ
wp0720 c4 L = pw3 c4 L (ℓ "五也亜") (ℓ "也五") tt tt Eq.refl

wp0721 : Base 4 → WsL → ⟪ (ℓ "亜亙") ⟫ʷ ≈ ⟪ (ℓ "亙亜亰") ⟫ʷ
wp0721 c4 L = pw1 c4 L (ℓ "亜亙") (ℓ "亙亜亰") tt tt Eq.refl

wp0722 : Base 4 → WsL → ⟪ (ℓ "五乪") ⟫ʷ ≈ ⟪ (ℓ "乪五") ⟫ʷ
wp0722 c4 L = pw3 c4 L (ℓ "五乪") (ℓ "乪五") tt tt Eq.refl

wp0723 : Base 4 → WsL → ⟪ (ℓ "也亜亜") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wp0723 c4 L = pw3 c4 L (ℓ "也亜亜") (ℓ "也") tt tt Eq.refl

wp0724 : Base 4 → WsL → ⟪ (ℓ "五云京") ⟫ʷ ≈ ⟪ (ℓ "云五") ⟫ʷ
wp0724 c4 L = pw2 c4 L (ℓ "五云京") (ℓ "云五") tt tt Eq.refl

wp0725 : Base 4 → WsL → ⟪ (ℓ "乹亙") ⟫ʷ ≈ ⟪ (ℓ "亙乹") ⟫ʷ
wp0725 c4 L = pw1 c4 L (ℓ "乹亙") (ℓ "亙乹") tt tt Eq.refl

wp0726 : Base 4 → WsL → ⟪ (ℓ "亠亲") ⟫ʷ ≈ ⟪ (ℓ "亲亠亜") ⟫ʷ
wp0726 c4 L = pw1 c4 L (ℓ "亠亲") (ℓ "亲亠亜") tt tt Eq.refl

wp0727 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亃亜亃") ⟫ʷ
wp0727 c4 L = pw3 c4 L (ℓ "亜") (ℓ "亃亜亃") tt tt Eq.refl

wp0728 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "乙二乙") ⟫ʷ
wp0728 c4 L = pw3 c4 L (ℓ "二") (ℓ "乙二乙") tt tt Eq.refl

wp0729 : Base 4 → WsL → ⟪ (ℓ "亜乙") ⟫ʷ ≈ ⟪ (ℓ "乙二亜") ⟫ʷ
wp0729 c4 L = pw3 c4 L (ℓ "亜乙") (ℓ "乙二亜") tt tt Eq.refl

wp0730 : Base 4 → WsL → ⟪ (ℓ "二亃") ⟫ʷ ≈ ⟪ (ℓ "亃亜二") ⟫ʷ
wp0730 c4 L = pw3 c4 L (ℓ "二亃") (ℓ "亃亜二") tt tt Eq.refl

wp0731 : Base 4 → WsL → ⟪ (ℓ "亜二亜二亜") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp0731 c4 L = pw3 c4 L (ℓ "亜二亜二亜") (ℓ "亜") tt tt Eq.refl

wp0732 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "亰亱丱亱亰丱") ⟫ʷ
wp0732 c4 L = pw1 c4 L (ℓ "亠") (ℓ "亰亱丱亱亰丱") tt tt Eq.refl

wp0733 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "京亭个亭京个") ⟫ʷ
wp0733 c4 L = pw2 c4 L (ℓ "亠") (ℓ "京亭个亭京个") tt tt Eq.refl

wp0734 : Base 4 → WsL → ⟪ (ℓ "亠乏") ⟫ʷ ≈ ⟪ (ℓ "乏亠") ⟫ʷ
wp0734 c4 L = pw2 c4 L (ℓ "亠乏") (ℓ "乏亠") tt tt Eq.refl

wp0735 : Base 4 → WsL → ⟪ (ℓ "亠乙亐") ⟫ʷ ≈ ⟪ (ℓ "乙亠") ⟫ʷ
wp0735 c4 L = pw2 c4 L (ℓ "亠乙亐") (ℓ "乙亠") tt tt Eq.refl

wp0736 : Base 4 → WsL → ⟪ (ℓ "乙亐亐") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wp0736 c4 L = pw2 c4 L (ℓ "乙亐亐") (ℓ "乙") tt tt Eq.refl

wp0737 : Base 4 → WsL → ⟪ (ℓ "亠亲亜") ⟫ʷ ≈ ⟪ (ℓ "亲亠") ⟫ʷ
wp0737 c4 L = pw1 c4 L (ℓ "亠亲亜") (ℓ "亲亠") tt tt Eq.refl

wp0738 : Base 4 → WsL → ⟪ (ℓ "二亜二亜二") ⟫ʷ ≈ ⟪ (ℓ "二") ⟫ʷ
wp0738 c4 L = pw3 c4 L (ℓ "二亜二亜二") (ℓ "二") tt tt Eq.refl

wp0739 : Base 4 → WsL → ⟪ (ℓ "亠亰亝") ⟫ʷ ≈ ⟪ (ℓ "亝亠") ⟫ʷ
wp0739 c4 L = pw1 c4 L (ℓ "亠亰亝") (ℓ "亝亠") tt tt Eq.refl

wp0740 : Base 4 → WsL → ⟪ (ℓ "丟亝") ⟫ʷ ≈ ⟪ (ℓ "亝丟") ⟫ʷ
wp0740 c4 L = pw1 c4 L (ℓ "丟亝") (ℓ "亝丟") tt tt Eq.refl

wp0741 : Base 4 → WsL → ⟪ (ℓ "么亝") ⟫ʷ ≈ ⟪ (ℓ "亝么") ⟫ʷ
wp0741 c4 L = pw3 c4 L (ℓ "么亝") (ℓ "亝么") tt tt Eq.refl

wp0742 : Base 4 → WsL → ⟪ (ℓ "丞亝") ⟫ʷ ≈ ⟪ (ℓ "亝丞") ⟫ʷ
wp0742 c4 L = pw1 c4 L (ℓ "丞亝") (ℓ "亝丞") tt tt Eq.refl

wp0743 : Base 4 → WsL → ⟪ (ℓ "亨亝") ⟫ʷ ≈ ⟪ (ℓ "亝亨") ⟫ʷ
wp0743 c4 L = pw3 c4 L (ℓ "亨亝") (ℓ "亝亨") tt tt Eq.refl

wp0744 : Base 4 → WsL → ⟪ (ℓ "亜之五") ⟫ʷ ≈ ⟪ (ℓ "之亜") ⟫ʷ
wp0744 c4 L = pw3 c4 L (ℓ "亜之五") (ℓ "之亜") tt tt Eq.refl

wp0745 : Base 4 → WsL → ⟪ (ℓ "五云") ⟫ʷ ≈ ⟪ (ℓ "云五京") ⟫ʷ
wp0745 c4 L = pw2 c4 L (ℓ "五云") (ℓ "云五京") tt tt Eq.refl

wp0746 : Base 4 → WsL → ⟪ (ℓ "亜乖") ⟫ʷ ≈ ⟪ (ℓ "乖亜") ⟫ʷ
wp0746 c4 L = pw3 c4 L (ℓ "亜乖") (ℓ "乖亜") tt tt Eq.refl

wp0747 : Base 4 → WsL → ⟪ (ℓ "之五五") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wp0747 c4 L = pw3 c4 L (ℓ "之五五") (ℓ "之") tt tt Eq.refl

wp0748 : Base 4 → WsL → ⟪ (ℓ "亜亙亰") ⟫ʷ ≈ ⟪ (ℓ "亙亜") ⟫ʷ
wp0748 c4 L = pw1 c4 L (ℓ "亜亙亰") (ℓ "亙亜") tt tt Eq.refl

wp0749 : Base 4 → WsL → ⟪ (ℓ "亜也") ⟫ʷ ≈ ⟪ (ℓ "也亜") ⟫ʷ
wp0749 c4 L = pw3 c4 L (ℓ "亜也") (ℓ "也亜") tt tt Eq.refl

wp0750 : Base 4 → WsL → ⟪ (ℓ "二亪五") ⟫ʷ ≈ ⟪ (ℓ "亪二") ⟫ʷ
wp0750 c4 L = pw3 c4 L (ℓ "二亪五") (ℓ "亪二") tt tt Eq.refl

wp0751 : Base 4 → WsL → ⟪ (ℓ "丙亡") ⟫ʷ ≈ ⟪ (ℓ "亡丙") ⟫ʷ
wp0751 c4 L = pw1 c4 L (ℓ "丙亡") (ℓ "亡丙") tt tt Eq.refl

wp0752 : Base 4 → WsL → ⟪ (ℓ "丘亡") ⟫ʷ ≈ ⟪ (ℓ "亡丘") ⟫ʷ
wp0752 c4 L = pw1 c4 L (ℓ "丘亡") (ℓ "亡丘") tt tt Eq.refl

wp0753 : Base 4 → WsL → ⟪ (ℓ "亪五五") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wp0753 c4 L = pw3 c4 L (ℓ "亪五五") (ℓ "亪") tt tt Eq.refl

wp0754 : Base 4 → WsL → ⟪ (ℓ "丰书亲") ⟫ʷ ≈ ⟪ (ℓ "书亲丰") ⟫ʷ
wp0754 c4 L = pw1 c4 L (ℓ "丰书亲") (ℓ "书亲丰") tt tt Eq.refl

wp0755 : Base 4 → WsL → ⟪ (ℓ "丯书亲") ⟫ʷ ≈ ⟪ (ℓ "书亲丯") ⟫ʷ
wp0755 c4 L = pw1 c4 L (ℓ "丯书亲") (ℓ "书亲丯") tt tt Eq.refl

wp0756 : Base 4 → WsL → ⟪ (ℓ "亜为") ⟫ʷ ≈ ⟪ (ℓ "为亜") ⟫ʷ
wp0756 c4 L = pw1 c4 L (ℓ "亜为") (ℓ "为亜") tt tt Eq.refl

wp0757 : Base 4 → WsL → ⟪ (ℓ "亜买亰") ⟫ʷ ≈ ⟪ (ℓ "买亜") ⟫ʷ
wp0757 c4 L = pw1 c4 L (ℓ "亜买亰") (ℓ "买亜") tt tt Eq.refl

wp0758 : Base 4 → WsL → ⟪ (ℓ "买亰亰") ⟫ʷ ≈ ⟪ (ℓ "买") ⟫ʷ
wp0758 c4 L = pw1 c4 L (ℓ "买亰亰") (ℓ "买") tt tt Eq.refl

wp0759 : Base 4 → WsL → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "买京买") ⟫ʷ
wp0759 c4 L = pw2 c4 L (ℓ "京") (ℓ "买京买") tt tt Eq.refl

wp0760 : Base 4 → WsL → ⟪ (ℓ "亜亏五") ⟫ʷ ≈ ⟪ (ℓ "亏亜") ⟫ʷ
wp0760 c4 L = pw3 c4 L (ℓ "亜亏五") (ℓ "亏亜") tt tt Eq.refl

wp0761 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "为五为") ⟫ʷ
wp0761 c4 L = pw2 c4 L (ℓ "五") (ℓ "为五为") tt tt Eq.refl

wp0762 : Base 4 → WsL → ⟪ (ℓ "京为") ⟫ʷ ≈ ⟪ (ℓ "为五京") ⟫ʷ
wp0762 c4 L = pw2 c4 L (ℓ "京为") (ℓ "为五京") tt tt Eq.refl

wp0763 : Base 4 → WsL → ⟪ (ℓ "五买") ⟫ʷ ≈ ⟪ (ℓ "买京五") ⟫ʷ
wp0763 c4 L = pw2 c4 L (ℓ "五买") (ℓ "买京五") tt tt Eq.refl

wp0764 : Base 4 → WsL → ⟪ (ℓ "京五京五京") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wp0764 c4 L = pw2 c4 L (ℓ "京五京五京") (ℓ "京") tt tt Eq.refl

wp0765 : Base 4 → WsL → ⟪ (ℓ "亰丰") ⟫ʷ ≈ ⟪ (ℓ "丰亰") ⟫ʷ
wp0765 c4 L = pw1 c4 L (ℓ "亰丰") (ℓ "丰亰") tt tt Eq.refl

wp0766 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亰亲丸亲亰丸") ⟫ʷ
wp0766 c4 L = pw1 c4 L (ℓ "亜") (ℓ "亰亲丸亲亰丸") tt tt Eq.refl

wp0767 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亨亩个亩亨个") ⟫ʷ
wp0767 c4 L = pw3 c4 L (ℓ "亜") (ℓ "亨亩个亩亨个") tt tt Eq.refl

wp0768 : Base 4 → WsL → ⟪ (ℓ "亜亱亠") ⟫ʷ ≈ ⟪ (ℓ "亱亜") ⟫ʷ
wp0768 c4 L = pw1 c4 L (ℓ "亜亱亠") (ℓ "亱亜") tt tt Eq.refl

wp0769 : Base 4 → WsL → ⟪ (ℓ "亐亠亐亠亐") ⟫ʷ ≈ ⟪ (ℓ "亐") ⟫ʷ
wp0769 c4 L = pw2 c4 L (ℓ "亐亠亐亠亐") (ℓ "亐") tt tt Eq.refl

wp0770 : Base 4 → WsL → ⟪ (ℓ "亜亰亡") ⟫ʷ ≈ ⟪ (ℓ "亡亜") ⟫ʷ
wp0770 c4 L = pw1 c4 L (ℓ "亜亰亡") (ℓ "亡亜") tt tt Eq.refl

wp0771 : Base 4 → WsL → ⟪ (ℓ "亐亡") ⟫ʷ ≈ ⟪ (ℓ "亡亐京") ⟫ʷ
wp0771 c4 L = pw2 c4 L (ℓ "亐亡") (ℓ "亡亐京") tt tt Eq.refl

wp0772 : Base 4 → WsL → ⟪ (ℓ "乏亡") ⟫ʷ ≈ ⟪ (ℓ "亡乏") ⟫ʷ
wp0772 c4 L = pw2 c4 L (ℓ "乏亡") (ℓ "亡乏") tt tt Eq.refl

wp0773 : Base 4 → WsL → ⟪ (ℓ "亰为亜") ⟫ʷ ≈ ⟪ (ℓ "为亰") ⟫ʷ
wp0773 c4 L = pw1 c4 L (ℓ "亰为亜") (ℓ "为亰") tt tt Eq.refl

wp0774 : Base 4 → WsL → ⟪ (ℓ "亜亏") ⟫ʷ ≈ ⟪ (ℓ "亏亜五") ⟫ʷ
wp0774 c4 L = pw3 c4 L (ℓ "亜亏") (ℓ "亏亜五") tt tt Eq.refl

wp0775 : Base 4 → WsL → ⟪ (ℓ "为亜亜") ⟫ʷ ≈ ⟪ (ℓ "为") ⟫ʷ
wp0775 c4 L = pw1 c4 L (ℓ "为亜亜") (ℓ "为") tt tt Eq.refl

wp0776 : Base 4 → WsL → ⟪ (ℓ "亰买") ⟫ʷ ≈ ⟪ (ℓ "买亰") ⟫ʷ
wp0776 c4 L = pw1 c4 L (ℓ "亰买") (ℓ "买亰") tt tt Eq.refl

wp0777 : Base 4 → WsL → ⟪ (ℓ "乕亏") ⟫ʷ ≈ ⟪ (ℓ "亏乕") ⟫ʷ
wp0777 c4 L = pw3 c4 L (ℓ "乕亏") (ℓ "亏乕") tt tt Eq.refl

wp0778 : Base 4 → WsL → ⟪ (ℓ "五为") ⟫ʷ ≈ ⟪ (ℓ "为五") ⟫ʷ
wp0778 c4 L = pw2 c4 L (ℓ "五为") (ℓ "为五") tt tt Eq.refl

wp0779 : Base 4 → WsL → ⟪ (ℓ "五京五京五") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp0779 c4 L = pw2 c4 L (ℓ "五京五京五") (ℓ "五") tt tt Eq.refl

wp0780 : Base 4 → WsL → ⟪ (ℓ "亜丿亞") ⟫ʷ ≈ ⟪ (ℓ "亞亜") ⟫ʷ
wp0780 c4 L = pw1 c4 L (ℓ "亜丿亞") (ℓ "亞亜") tt tt Eq.refl

wp0781 : Base 4 → WsL → ⟪ (ℓ "亜丿") ⟫ʷ ≈ ⟪ (ℓ "亞亜亞") ⟫ʷ
wp0781 c4 L = pw1 c4 L (ℓ "亜丿") (ℓ "亞亜亞") tt tt Eq.refl

wp0782 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丿亜丿") ⟫ʷ
wp0782 c4 L = pw1 c4 L (ℓ "亜") (ℓ "丿亜丿") tt tt Eq.refl

wp0783 : Base 4 → WsL → ⟪ (ℓ "云井亮") ⟫ʷ ≈ ⟪ (ℓ "亮云") ⟫ʷ
wp0783 c4 L = pw2 c4 L (ℓ "云井亮") (ℓ "亮云") tt tt Eq.refl

wp0784 : Base 4 → WsL → ⟪ (ℓ "亜井亨") ⟫ʷ ≈ ⟪ (ℓ "井亜") ⟫ʷ
wp0784 c4 L = pw3 c4 L (ℓ "亜井亨") (ℓ "井亜") tt tt Eq.refl

wp0785 : Base 4 → WsL → ⟪ (ℓ "乕云") ⟫ʷ ≈ ⟪ (ℓ "云乕") ⟫ʷ
wp0785 c4 L = pw2 c4 L (ℓ "乕云") (ℓ "云乕") tt tt Eq.refl

wp0786 : Base 4 → WsL → ⟪ (ℓ "云井") ⟫ʷ ≈ ⟪ (ℓ "井云") ⟫ʷ
wp0786 c4 L = pw2 c4 L (ℓ "云井") (ℓ "井云") tt tt Eq.refl

wp0787 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "井亨井") ⟫ʷ
wp0787 c4 L = pw3 c4 L (ℓ "亨") (ℓ "井亨井") tt tt Eq.refl

wp0788 : Base 4 → WsL → ⟪ (ℓ "乳亭亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷乳亭") ⟫ʷ
wp0788 c4 L = pw2 c4 L (ℓ "乳亭亮丶亮丷") (ℓ "亮丶亮丷乳亭") tt tt Eq.refl

wp0789 : Base 4 → WsL → ⟪ (ℓ "亜乶") ⟫ʷ ≈ ⟪ (ℓ "乶亠亜") ⟫ʷ
wp0789 c4 L = pw1 c4 L (ℓ "亜乶") (ℓ "乶亠亜") tt tt Eq.refl

wp0790 : Base 4 → WsL → ⟪ (ℓ "亜亱") ⟫ʷ ≈ ⟪ (ℓ "亱亠亜") ⟫ʷ
wp0790 c4 L = pw1 c4 L (ℓ "亜亱") (ℓ "亱亠亜") tt tt Eq.refl

wp0791 : Base 4 → WsL → ⟪ (ℓ "乳亠亭亠") ⟫ʷ ≈ ⟪ (ℓ "乳亭") ⟫ʷ
wp0791 c4 L = pw2 c4 L (ℓ "乳亠亭亠") (ℓ "乳亭") tt tt Eq.refl

wp0792 : Base 4 → WsL → ⟪ (ℓ "五乳亠") ⟫ʷ ≈ ⟪ (ℓ "乳五") ⟫ʷ
wp0792 c4 L = pw2 c4 L (ℓ "五乳亠") (ℓ "乳五") tt tt Eq.refl

wp0793 : Base 4 → WsL → ⟪ (ℓ "亠亙") ⟫ʷ ≈ ⟪ (ℓ "亙亠亰") ⟫ʷ
wp0793 c4 L = pw1 c4 L (ℓ "亠亙") (ℓ "亙亠亰") tt tt Eq.refl

wp0794 : Base 4 → WsL → ⟪ (ℓ "乳亠亠") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wp0794 c4 L = pw2 c4 L (ℓ "乳亠亠") (ℓ "乳") tt tt Eq.refl

wp0795 : Base 4 → WsL → ⟪ (ℓ "五乒") ⟫ʷ ≈ ⟪ (ℓ "乒五") ⟫ʷ
wp0795 c4 L = pw2 c4 L (ℓ "五乒") (ℓ "乒五") tt tt Eq.refl

wp0796 : Base 4 → WsL → ⟪ (ℓ "亠並丸") ⟫ʷ ≈ ⟪ (ℓ "並亠") ⟫ʷ
wp0796 c4 L = pw1 c4 L (ℓ "亠並丸") (ℓ "並亠") tt tt Eq.refl

wp0797 : Base 4 → WsL → ⟪ (ℓ "亠丸") ⟫ʷ ≈ ⟪ (ℓ "丸亠") ⟫ʷ
wp0797 c4 L = pw1 c4 L (ℓ "亠丸") (ℓ "丸亠") tt tt Eq.refl

wp0798 : Base 4 → WsL → ⟪ (ℓ "並丸丸") ⟫ʷ ≈ ⟪ (ℓ "並") ⟫ʷ
wp0798 c4 L = pw1 c4 L (ℓ "並丸丸") (ℓ "並") tt tt Eq.refl

wp0799 : Base 4 → WsL → ⟪ (ℓ "二之亪") ⟫ʷ ≈ ⟪ (ℓ "之亪个五二") ⟫ʷ
wp0799 c4 L = pw3 c4 L (ℓ "二之亪") (ℓ "之亪个五二") tt tt Eq.refl

wp0800 : Base 4 → WsL → ⟪ (ℓ "个京亡") ⟫ʷ ≈ ⟪ (ℓ "亡个") ⟫ʷ
wp0800 c4 L = pw2 c4 L (ℓ "个京亡") (ℓ "亡个") tt tt Eq.refl

wp0801 : Base 4 → WsL → ⟪ (ℓ "五京亡") ⟫ʷ ≈ ⟪ (ℓ "亡五") ⟫ʷ
wp0801 c4 L = pw2 c4 L (ℓ "五京亡") (ℓ "亡五") tt tt Eq.refl

wp0802 : Base 4 → WsL → ⟪ (ℓ "个五") ⟫ʷ ≈ ⟪ (ℓ "个京五京") ⟫ʷ
wp0802 c4 L = pw2 c4 L (ℓ "个五") (ℓ "个京五京") tt tt Eq.refl

wp0803 : Base 4 → WsL → ⟪ (ℓ "二之亪个五") ⟫ʷ ≈ ⟪ (ℓ "之亪二") ⟫ʷ
wp0803 c4 L = pw3 c4 L (ℓ "二之亪个五") (ℓ "之亪二") tt tt Eq.refl

wp0804 : Base 4 → WsL → ⟪ (ℓ "丰亲") ⟫ʷ ≈ ⟪ (ℓ "亲丰") ⟫ʷ
wp0804 c4 L = pw1 c4 L (ℓ "丰亲") (ℓ "亲丰") tt tt Eq.refl

wp0805 : Base 4 → WsL → ⟪ (ℓ "亙亲") ⟫ʷ ≈ ⟪ (ℓ "亝亲亙") ⟫ʷ
wp0805 c4 L = pw1 c4 L (ℓ "亙亲") (ℓ "亝亲亙") tt tt Eq.refl

wp0806 : Base 4 → WsL → ⟪ (ℓ "五亝") ⟫ʷ ≈ ⟪ (ℓ "亝亨五") ⟫ʷ
wp0806 c4 L = pw3 c4 L (ℓ "五亝") (ℓ "亝亨五") tt tt Eq.refl

wp0807 : Base 4 → WsL → ⟪ (ℓ "五乽亐") ⟫ʷ ≈ ⟪ (ℓ "乽五") ⟫ʷ
wp0807 c4 L = pw2 c4 L (ℓ "五乽亐") (ℓ "乽五") tt tt Eq.refl

wp0808 : Base 4 → WsL → ⟪ (ℓ "乽亐亐") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wp0808 c4 L = pw2 c4 L (ℓ "乽亐亐") (ℓ "乽") tt tt Eq.refl

wp0809 : Base 4 → WsL → ⟪ (ℓ "争亙") ⟫ʷ ≈ ⟪ (ℓ "亙争亝") ⟫ʷ
wp0809 c4 L = pw1 c4 L (ℓ "争亙") (ℓ "亙争亝") tt tt Eq.refl

wp0810 : Base 4 → WsL → ⟪ (ℓ "五争") ⟫ʷ ≈ ⟪ (ℓ "争五") ⟫ʷ
wp0810 c4 L = pw2 c4 L (ℓ "五争") (ℓ "争五") tt tt Eq.refl

wp0811 : Base 4 → WsL → ⟪ (ℓ "争亝亝") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wp0811 c4 L = pw1 c4 L (ℓ "争亝亝") (ℓ "争") tt tt Eq.refl

wp0812 : Base 4 → WsL → ⟪ (ℓ "乼亙") ⟫ʷ ≈ ⟪ (ℓ "亝乼") ⟫ʷ
wp0812 c4 L = pw1 c4 L (ℓ "乼亙") (ℓ "亝乼") tt tt Eq.refl

wp0813 : Base 4 → WsL → ⟪ (ℓ "乼亞") ⟫ʷ ≈ ⟪ (ℓ "亚乼") ⟫ʷ
wp0813 c4 L = pw1 c4 L (ℓ "乼亞") (ℓ "亚乼") tt tt Eq.refl

wp0814 : Base 4 → WsL → ⟪ (ℓ "亘亲亜") ⟫ʷ ≈ ⟪ (ℓ "亲亘") ⟫ʷ
wp0814 c4 L = pw1 c4 L (ℓ "亘亲亜") (ℓ "亲亘") tt tt Eq.refl

wp0815 : Base 4 → WsL → ⟪ (ℓ "亜井") ⟫ʷ ≈ ⟪ (ℓ "井亜亨") ⟫ʷ
wp0815 c4 L = pw3 c4 L (ℓ "亜井") (ℓ "井亜亨") tt tt Eq.refl

wp0816 : Base 4 → WsL → ⟪ (ℓ "丟井") ⟫ʷ ≈ ⟪ (ℓ "井丟") ⟫ʷ
wp0816 c4 L = pw2 c4 L (ℓ "丟井") (ℓ "井丟") tt tt Eq.refl

wp0817 : Base 4 → WsL → ⟪ (ℓ "乩井") ⟫ʷ ≈ ⟪ (ℓ "井乩") ⟫ʷ
wp0817 c4 L = pw3 c4 L (ℓ "乩井") (ℓ "井乩") tt tt Eq.refl

wp0818 : Base 4 → WsL → ⟪ (ℓ "乺井") ⟫ʷ ≈ ⟪ (ℓ "井乺") ⟫ʷ
wp0818 c4 L = pw2 c4 L (ℓ "乺井") (ℓ "井乺") tt tt Eq.refl

wp0819 : Base 4 → WsL → ⟪ (ℓ "丞井") ⟫ʷ ≈ ⟪ (ℓ "井丞") ⟫ʷ
wp0819 c4 L = pw2 c4 L (ℓ "丞井") (ℓ "井丞") tt tt Eq.refl

wp0820 : Base 4 → WsL → ⟪ (ℓ "亘乪") ⟫ʷ ≈ ⟪ (ℓ "乪亘") ⟫ʷ
wp0820 c4 L = pw1 c4 L (ℓ "亘乪") (ℓ "乪亘") tt tt Eq.refl

wp0821 : Base 4 → WsL → ⟪ (ℓ "亲亜亜") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wp0821 c4 L = pw1 c4 L (ℓ "亲亜亜") (ℓ "亲") tt tt Eq.refl

wp0822 : Base 4 → WsL → ⟪ (ℓ "亨井") ⟫ʷ ≈ ⟪ (ℓ "井亨") ⟫ʷ
wp0822 c4 L = pw3 c4 L (ℓ "亨井") (ℓ "井亨") tt tt Eq.refl

wp0823 : Base 4 → WsL → ⟪ (ℓ "乺亙") ⟫ʷ ≈ ⟪ (ℓ "亙乺") ⟫ʷ
wp0823 c4 L = pw1 c4 L (ℓ "乺亙") (ℓ "亙乺") tt tt Eq.refl

wp0824 : Base 4 → WsL → ⟪ (ℓ "五乳亭") ⟫ʷ ≈ ⟪ (ℓ "乳亭五") ⟫ʷ
wp0824 c4 L = pw2 c4 L (ℓ "五乳亭") (ℓ "乳亭五") tt tt Eq.refl

wp0825 : Base 4 → WsL → ⟪ (ℓ "亠云") ⟫ʷ ≈ ⟪ (ℓ "云亠京") ⟫ʷ
wp0825 c4 L = pw2 c4 L (ℓ "亠云") (ℓ "云亠京") tt tt Eq.refl

wp0826 : Base 4 → WsL → ⟪ (ℓ "亜亍亨") ⟫ʷ ≈ ⟪ (ℓ "亍亜") ⟫ʷ
wp0826 c4 L = pw3 c4 L (ℓ "亜亍亨") (ℓ "亍亜") tt tt Eq.refl

wp0827 : Base 4 → WsL → ⟪ (ℓ "亜亨") ⟫ʷ ≈ ⟪ (ℓ "亨亜") ⟫ʷ
wp0827 c4 L = pw3 c4 L (ℓ "亜亨") (ℓ "亨亜") tt tt Eq.refl

wp0828 : Base 4 → WsL → ⟪ (ℓ "亐亭亠") ⟫ʷ ≈ ⟪ (ℓ "亭亠亐亠") ⟫ʷ
wp0828 c4 L = pw2 c4 L (ℓ "亐亭亠") (ℓ "亭亠亐亠") tt tt Eq.refl

wp0829 : Base 4 → WsL → ⟪ (ℓ "亐亠亭亠") ⟫ʷ ≈ ⟪ (ℓ "亭亠亐") ⟫ʷ
wp0829 c4 L = pw2 c4 L (ℓ "亐亠亭亠") (ℓ "亭亠亐") tt tt Eq.refl

wp0830 : Base 4 → WsL → ⟪ (ℓ "亐並") ⟫ʷ ≈ ⟪ (ℓ "並亐") ⟫ʷ
wp0830 c4 L = pw2 c4 L (ℓ "亐並") (ℓ "並亐") tt tt Eq.refl

wp0831 : Base 4 → WsL → ⟪ (ℓ "亠亭") ⟫ʷ ≈ ⟪ (ℓ "亭亠") ⟫ʷ
wp0831 c4 L = pw2 c4 L (ℓ "亠亭") (ℓ "亭亠") tt tt Eq.refl

wp0832 : Base 4 → WsL → ⟪ (ℓ "云亮") ⟫ʷ ≈ ⟪ (ℓ "井亮云") ⟫ʷ
wp0832 c4 L = pw2 c4 L (ℓ "云亮") (ℓ "井亮云") tt tt Eq.refl

wp0833 : Base 4 → WsL → ⟪ (ℓ "亜井") ⟫ʷ ≈ ⟪ (ℓ "井亨亜") ⟫ʷ
wp0833 c4 L = pw3 c4 L (ℓ "亜井") (ℓ "井亨亜") tt tt Eq.refl

wp0834 : Base 4 → WsL → ⟪ (ℓ "丷亭") ⟫ʷ ≈ ⟪ (ℓ "亭丷") ⟫ʷ
wp0834 c4 L = pw2 c4 L (ℓ "丷亭") (ℓ "亭丷") tt tt Eq.refl

wp0835 : Base 4 → WsL → ⟪ (ℓ "五亭亠") ⟫ʷ ≈ ⟪ (ℓ "亭五") ⟫ʷ
wp0835 c4 L = pw2 c4 L (ℓ "五亭亠") (ℓ "亭五") tt tt Eq.refl

wp0836 : Base 4 → WsL → ⟪ (ℓ "亭亠亠") ⟫ʷ ≈ ⟪ (ℓ "亭") ⟫ʷ
wp0836 c4 L = pw2 c4 L (ℓ "亭亠亠") (ℓ "亭") tt tt Eq.refl

wp0837 : Base 4 → WsL → ⟪ (ℓ "亘书亲") ⟫ʷ ≈ ⟪ (ℓ "书亲丱亜亘") ⟫ʷ
wp0837 c4 L = pw1 c4 L (ℓ "亘书亲") (ℓ "书亲丱亜亘") tt tt Eq.refl

wp0838 : Base 4 → WsL → ⟪ (ℓ "丱亨井") ⟫ʷ ≈ ⟪ (ℓ "井丱") ⟫ʷ
wp0838 c4 L = pw3 c4 L (ℓ "丱亨井") (ℓ "井丱") tt tt Eq.refl

wp0839 : Base 4 → WsL → ⟪ (ℓ "亜亨井") ⟫ʷ ≈ ⟪ (ℓ "井亜") ⟫ʷ
wp0839 c4 L = pw3 c4 L (ℓ "亜亨井") (ℓ "井亜") tt tt Eq.refl

wp0840 : Base 4 → WsL → ⟪ (ℓ "丱亜") ⟫ʷ ≈ ⟪ (ℓ "丱亨亜亨") ⟫ʷ
wp0840 c4 L = pw3 c4 L (ℓ "丱亜") (ℓ "丱亨亜亨") tt tt Eq.refl

wp0841 : Base 4 → WsL → ⟪ (ℓ "亘书亲丱亜") ⟫ʷ ≈ ⟪ (ℓ "书亲亘") ⟫ʷ
wp0841 c4 L = pw1 c4 L (ℓ "亘书亲丱亜") (ℓ "书亲亘") tt tt Eq.refl

wp0842 : Base 4 → WsL → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "亡亰亡") ⟫ʷ
wp0842 c4 L = pw1 c4 L (ℓ "亰") (ℓ "亡亰亡") tt tt Eq.refl

wp0843 : Base 4 → WsL → ⟪ (ℓ "云亭") ⟫ʷ ≈ ⟪ (ℓ "亡亭云") ⟫ʷ
wp0843 c4 L = pw2 c4 L (ℓ "云亭") (ℓ "亡亭云") tt tt Eq.refl

wp0844 : Base 4 → WsL → ⟪ (ℓ "亜买") ⟫ʷ ≈ ⟪ (ℓ "买亰亜") ⟫ʷ
wp0844 c4 L = pw1 c4 L (ℓ "亜买") (ℓ "买亰亜") tt tt Eq.refl

wp0845 : Base 4 → WsL → ⟪ (ℓ "亜亡") ⟫ʷ ≈ ⟪ (ℓ "亡亰亜") ⟫ʷ
wp0845 c4 L = pw1 c4 L (ℓ "亜亡") (ℓ "亡亰亜") tt tt Eq.refl

wp0846 : Base 4 → WsL → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "买亰买") ⟫ʷ
wp0846 c4 L = pw1 c4 L (ℓ "亰") (ℓ "买亰买") tt tt Eq.refl

wp0847 : Base 4 → WsL → ⟪ (ℓ "丽丢") ⟫ʷ ≈ ⟪ (ℓ "丢丽") ⟫ʷ
wp0847 c4 L = pw1 c4 L (ℓ "丽丢") (ℓ "丢丽") tt tt Eq.refl

wp0848 : Base 4 → WsL → ⟪ (ℓ "亁丢") ⟫ʷ ≈ ⟪ (ℓ "丢亁") ⟫ʷ
wp0848 c4 L = pw1 c4 L (ℓ "亁丢") (ℓ "丢亁") tt tt Eq.refl

wp0849 : Base 4 → WsL → ⟪ (ℓ "丢亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丢") ⟫ʷ
wp0849 c4 L = pw2 c4 L (ℓ "丢亮丶亮丷") (ℓ "亮丶亮丷丢") tt tt Eq.refl

wp0850 : Base 4 → WsL → ⟪ (ℓ "丽乕") ⟫ʷ ≈ ⟪ (ℓ "乕丽") ⟫ʷ
wp0850 c4 L = pw2 c4 L (ℓ "丽乕") (ℓ "乕丽") tt tt Eq.refl

wp0851 : Base 4 → WsL → ⟪ (ℓ "丽乩") ⟫ʷ ≈ ⟪ (ℓ "乩丽") ⟫ʷ
wp0851 c4 L = pw1 c4 L (ℓ "丽乩") (ℓ "乩丽") tt tt Eq.refl

wp0852 : Base 4 → WsL → ⟪ (ℓ "丽乹") ⟫ʷ ≈ ⟪ (ℓ "乹丽") ⟫ʷ
wp0852 c4 L = pw1 c4 L (ℓ "丽乹") (ℓ "乹丽") tt tt Eq.refl

wp0853 : Base 4 → WsL → ⟪ (ℓ "亄丽") ⟫ʷ ≈ ⟪ (ℓ "丽亄") ⟫ʷ
wp0853 c4 L = pw2 c4 L (ℓ "亄丽") (ℓ "丽亄") tt tt Eq.refl

wp0854 : Base 4 → WsL → ⟪ (ℓ "亇丽") ⟫ʷ ≈ ⟪ (ℓ "丽亇") ⟫ʷ
wp0854 c4 L = pw1 c4 L (ℓ "亇丽") (ℓ "丽亇") tt tt Eq.refl

wp0855 : Base 4 → WsL → ⟪ (ℓ "亊丽") ⟫ʷ ≈ ⟪ (ℓ "丽亊") ⟫ʷ
wp0855 c4 L = pw1 c4 L (ℓ "亊丽") (ℓ "丽亊") tt tt Eq.refl

wp0856 : Base 4 → WsL → ⟪ (ℓ "丽乎") ⟫ʷ ≈ ⟪ (ℓ "乎丽") ⟫ʷ
wp0856 c4 L = pw2 c4 L (ℓ "丽乎") (ℓ "乎丽") tt tt Eq.refl

wp0857 : Base 4 → WsL → ⟪ (ℓ "丽乏") ⟫ʷ ≈ ⟪ (ℓ "乏丽") ⟫ʷ
wp0857 c4 L = pw2 c4 L (ℓ "丽乏") (ℓ "乏丽") tt tt Eq.refl

wp0858 : Base 4 → WsL → ⟪ (ℓ "丽亭") ⟫ʷ ≈ ⟪ (ℓ "亭丽") ⟫ʷ
wp0858 c4 L = pw2 c4 L (ℓ "丽亭") (ℓ "亭丽") tt tt Eq.refl

wp0859 : Base 4 → WsL → ⟪ (ℓ "丽乇") ⟫ʷ ≈ ⟪ (ℓ "乇丽") ⟫ʷ
wp0859 c4 L = pw3 c4 L (ℓ "丽乇") (ℓ "乇丽") tt tt Eq.refl

wp0860 : Base 4 → WsL → ⟪ (ℓ "丽么") ⟫ʷ ≈ ⟪ (ℓ "么丽") ⟫ʷ
wp0860 c4 L = pw3 c4 L (ℓ "丽么") (ℓ "么丽") tt tt Eq.refl

wp0861 : Base 4 → WsL → ⟪ (ℓ "亁乕") ⟫ʷ ≈ ⟪ (ℓ "乕亁") ⟫ʷ
wp0861 c4 L = pw2 c4 L (ℓ "亁乕") (ℓ "乕亁") tt tt Eq.refl

wp0862 : Base 4 → WsL → ⟪ (ℓ "亁乩") ⟫ʷ ≈ ⟪ (ℓ "乩亁") ⟫ʷ
wp0862 c4 L = pw1 c4 L (ℓ "亁乩") (ℓ "乩亁") tt tt Eq.refl

wp0863 : Base 4 → WsL → ⟪ (ℓ "丶乩") ⟫ʷ ≈ ⟪ (ℓ "乩丶") ⟫ʷ
wp0863 c4 L = pw1 c4 L (ℓ "丶乩") (ℓ "乩丶") tt tt Eq.refl

wp0864 : Base 4 → WsL → ⟪ (ℓ "丷乩") ⟫ʷ ≈ ⟪ (ℓ "乩丷") ⟫ʷ
wp0864 c4 L = pw1 c4 L (ℓ "丷乩") (ℓ "乩丷") tt tt Eq.refl

wp0865 : Base 4 → WsL → ⟪ (ℓ "亁乹") ⟫ʷ ≈ ⟪ (ℓ "乹亁") ⟫ʷ
wp0865 c4 L = pw1 c4 L (ℓ "亁乹") (ℓ "乹亁") tt tt Eq.refl

wp0866 : Base 4 → WsL → ⟪ (ℓ "乹亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷乹") ⟫ʷ
wp0866 c4 L = pw2 c4 L (ℓ "乹亮丶亮丷") (ℓ "亮丶亮丷乹") tt tt Eq.refl

wp0867 : Base 4 → WsL → ⟪ (ℓ "亁亄") ⟫ʷ ≈ ⟪ (ℓ "亄亁") ⟫ʷ
wp0867 c4 L = pw2 c4 L (ℓ "亁亄") (ℓ "亄亁") tt tt Eq.refl

wp0868 : Base 4 → WsL → ⟪ (ℓ "亁亇") ⟫ʷ ≈ ⟪ (ℓ "亇亁") ⟫ʷ
wp0868 c4 L = pw1 c4 L (ℓ "亁亇") (ℓ "亇亁") tt tt Eq.refl

wp0869 : Base 4 → WsL → ⟪ (ℓ "亁亊") ⟫ʷ ≈ ⟪ (ℓ "亊亁") ⟫ʷ
wp0869 c4 L = pw1 c4 L (ℓ "亁亊") (ℓ "亊亁") tt tt Eq.refl

wp0870 : Base 4 → WsL → ⟪ (ℓ "亁亲") ⟫ʷ ≈ ⟪ (ℓ "亲亁") ⟫ʷ
wp0870 c4 L = pw1 c4 L (ℓ "亁亲") (ℓ "亲亁") tt tt Eq.refl

wp0871 : Base 4 → WsL → ⟪ (ℓ "亁乎") ⟫ʷ ≈ ⟪ (ℓ "乎亁") ⟫ʷ
wp0871 c4 L = pw2 c4 L (ℓ "亁乎") (ℓ "乎亁") tt tt Eq.refl

wp0872 : Base 4 → WsL → ⟪ (ℓ "亁乏") ⟫ʷ ≈ ⟪ (ℓ "乏亁") ⟫ʷ
wp0872 c4 L = pw2 c4 L (ℓ "亁乏") (ℓ "乏亁") tt tt Eq.refl

wp0873 : Base 4 → WsL → ⟪ (ℓ "亁亭") ⟫ʷ ≈ ⟪ (ℓ "亭亁") ⟫ʷ
wp0873 c4 L = pw2 c4 L (ℓ "亁亭") (ℓ "亭亁") tt tt Eq.refl

wp0874 : Base 4 → WsL → ⟪ (ℓ "亁乇") ⟫ʷ ≈ ⟪ (ℓ "乇亁") ⟫ʷ
wp0874 c4 L = pw3 c4 L (ℓ "亁乇") (ℓ "乇亁") tt tt Eq.refl

wp0875 : Base 4 → WsL → ⟪ (ℓ "亁么") ⟫ʷ ≈ ⟪ (ℓ "么亁") ⟫ʷ
wp0875 c4 L = pw3 c4 L (ℓ "亁么") (ℓ "么亁") tt tt Eq.refl

wp0876 : Base 4 → WsL → ⟪ (ℓ "五个亄个") ⟫ʷ ≈ ⟪ (ℓ "亄五") ⟫ʷ
wp0876 c4 L = pw2 c4 L (ℓ "五个亄个") (ℓ "亄五") tt tt Eq.refl

wp0877 : Base 4 → WsL → ⟪ (ℓ "个亄个个") ⟫ʷ ≈ ⟪ (ℓ "个亄") ⟫ʷ
wp0877 c4 L = pw2 c4 L (ℓ "个亄个个") (ℓ "个亄") tt tt Eq.refl

wp0878 : Base 4 → WsL → ⟪ (ℓ "亇丶") ⟫ʷ ≈ ⟪ (ℓ "丶亇") ⟫ʷ
wp0878 c4 L = pw1 c4 L (ℓ "亇丶") (ℓ "丶亇") tt tt Eq.refl

wp0879 : Base 4 → WsL → ⟪ (ℓ "亇丷") ⟫ʷ ≈ ⟪ (ℓ "丷亇") ⟫ʷ
wp0879 c4 L = pw1 c4 L (ℓ "亇丷") (ℓ "丷亇") tt tt Eq.refl

wp0880 : Base 4 → WsL → ⟪ (ℓ "亐亊亐亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷亊") ⟫ʷ
wp0880 c4 L = pw2 c4 L (ℓ "亐亊亐亮丶亮丷") (ℓ "亮丶亮丷亊") tt tt Eq.refl

wp0881 : Base 4 → WsL → ⟪ (ℓ "亠丸亊丸") ⟫ʷ ≈ ⟪ (ℓ "亊亠") ⟫ʷ
wp0881 c4 L = pw1 c4 L (ℓ "亠丸亊丸") (ℓ "亊亠") tt tt Eq.refl

wp0882 : Base 4 → WsL → ⟪ (ℓ "丸亊丸丸") ⟫ʷ ≈ ⟪ (ℓ "丸亊") ⟫ʷ
wp0882 c4 L = pw1 c4 L (ℓ "丸亊丸丸") (ℓ "丸亊") tt tt Eq.refl

wp0883 : Base 4 → WsL → ⟪ (ℓ "亠五亓") ⟫ʷ ≈ ⟪ (ℓ "亓亠") ⟫ʷ
wp0883 c4 L = pw2 c4 L (ℓ "亠五亓") (ℓ "亓亠") tt tt Eq.refl

wp0884 : Base 4 → WsL → ⟪ (ℓ "亠五") ⟫ʷ ≈ ⟪ (ℓ "亓亠亓") ⟫ʷ
wp0884 c4 L = pw2 c4 L (ℓ "亠五") (ℓ "亓亠亓") tt tt Eq.refl

wp0885 : Base 4 → WsL → ⟪ (ℓ "五亠五") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0885 c4 L = pw2 c4 L (ℓ "五亠五") (ℓ "亠") tt tt Eq.refl

wp0886 : Base 4 → WsL → ⟪ (ℓ "个亝") ⟫ʷ ≈ ⟪ (ℓ "亝个亨") ⟫ʷ
wp0886 c4 L = pw3 c4 L (ℓ "个亝") (ℓ "亝个亨") tt tt Eq.refl

wp0887 : Base 4 → WsL → ⟪ (ℓ "亝丠") ⟫ʷ ≈ ⟪ (ℓ "丠亝") ⟫ʷ
wp0887 c4 L = pw1 c4 L (ℓ "亝丠") (ℓ "丠亝") tt tt Eq.refl

wp0888 : Base 4 → WsL → ⟪ (ℓ "亠两") ⟫ʷ ≈ ⟪ (ℓ "两亣亠亠") ⟫ʷ
wp0888 c4 L = pw1 c4 L (ℓ "亠两") (ℓ "两亣亠亠") tt tt Eq.refl

wp0889 : Base 4 → WsL → ⟪ (ℓ "亠乾") ⟫ʷ ≈ ⟪ (ℓ "丿乾丿亠") ⟫ʷ
wp0889 c4 L = pw1 c4 L (ℓ "亠乾") (ℓ "丿乾丿亠") tt tt Eq.refl

wp0890 : Base 4 → WsL → ⟪ (ℓ "亠东") ⟫ʷ ≈ ⟪ (ℓ "东亠") ⟫ʷ
wp0890 c4 L = pw1 c4 L (ℓ "亠东") (ℓ "东亠") tt tt Eq.refl

wp0891 : Base 4 → WsL → ⟪ (ℓ "两乾东") ⟫ʷ ≈ ⟪ (ℓ "两亣亠丿乾丿东") ⟫ʷ
wp0891 c4 L = pw1 c4 L (ℓ "两乾东") (ℓ "两亣亠丿乾丿东") tt tt Eq.refl

wp0892 : Base 4 → WsL → ⟪ (ℓ "两乾一") ⟫ʷ ≈ ⟪ (ℓ "两亣亠丿乾丿一") ⟫ʷ
wp0892 c4 L = pw1 c4 L (ℓ "两乾一") (ℓ "两亣亠丿乾丿一") tt tt Eq.refl

wp0893 : Base 4 → WsL → ⟪ (ℓ "亨乾东亨丠") ⟫ʷ ≈ ⟪ (ℓ "丠亨两乾丂亨") ⟫ʷ
wp0893 c4 L = pw0 c4 L (ℓ "亨乾东亨丠") (ℓ "丠亨两乾丂亨") tt tt Eq.refl

wp0894 : Base 4 → WsL → ⟪ (ℓ "亟乕亟乖") ⟫ʷ ≈ ⟪ (ℓ "享丽享举") ⟫ʷ
wp0894 c4 L = pw3 c4 L (ℓ "亟乕亟乖") (ℓ "享丽享举") tt tt Eq.refl

wp0895 : Base 4 → WsL → ⟪ (ℓ "京亓") ⟫ʷ ≈ ⟪ (ℓ "亓京五") ⟫ʷ
wp0895 c4 L = pw2 c4 L (ℓ "京亓") (ℓ "亓京五") tt tt Eq.refl

wp0896 : Base 4 → WsL → ⟪ (ℓ "亰些亜") ⟫ʷ ≈ ⟪ (ℓ "些亰") ⟫ʷ
wp0896 c4 L = pw1 c4 L (ℓ "亰些亜") (ℓ "些亰") tt tt Eq.refl

wp0897 : Base 4 → WsL → ⟪ (ℓ "丽亓") ⟫ʷ ≈ ⟪ (ℓ "亓丽") ⟫ʷ
wp0897 c4 L = pw2 c4 L (ℓ "丽亓") (ℓ "亓丽") tt tt Eq.refl

wp0898 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "也亜也") ⟫ʷ
wp0898 c4 L = pw3 c4 L (ℓ "亜") (ℓ "也亜也") tt tt Eq.refl

wp0899 : Base 4 → WsL → ⟪ (ℓ "五也") ⟫ʷ ≈ ⟪ (ℓ "也亜五") ⟫ʷ
wp0899 c4 L = pw3 c4 L (ℓ "五也") (ℓ "也亜五") tt tt Eq.refl

wp0900 : Base 4 → WsL → ⟪ (ℓ "五亜五亜五") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp0900 c4 L = pw3 c4 L (ℓ "五亜五亜五") (ℓ "五") tt tt Eq.refl

wp0901 : Base 4 → WsL → ⟪ (ℓ "享丽享举") ⟫ʷ ≈ ⟪ (ℓ "享丽享举") ⟫ʷ
wp0901 c4 L = pw3 c4 L (ℓ "享丽享举") (ℓ "享丽享举") tt tt Eq.refl

wp0902 : Base 4 → WsL → ⟪ (ℓ "丽丽丽丽") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0902 c4 L = pw1 c4 L (ℓ "丽丽丽丽") [] tt tt Eq.refl

wp0903 : Base 4 → WsL → ⟪ (ℓ "亁亁") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wp0903 c4 L = pw1 c4 L (ℓ "亁亁") (ℓ "丢丢丢") tt tt Eq.refl

wp0904 : Base 4 → WsL → ⟪ (ℓ "丽亁丽亁丽亁") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
wp0904 c4 L = pw1 c4 L (ℓ "丽亁丽亁丽亁") (ℓ "丢丢丢") tt tt Eq.refl

wp0905 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷亮丶亮丷") ⟫ʷ
wp0905 c4 L = pw2 c4 L (ℓ "五") (ℓ "亮丶亮丷亮丶亮丷") tt tt Eq.refl

wp0906 : Base 4 → WsL → ⟪ (ℓ "亜丽") ⟫ʷ ≈ ⟪ (ℓ "丽亜") ⟫ʷ
wp0906 c4 L = pw1 c4 L (ℓ "亜丽") (ℓ "丽亜") tt tt Eq.refl

wp0907 : Base 4 → WsL → ⟪ (ℓ "丽亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丽") ⟫ʷ
wp0907 c4 L = pw2 c4 L (ℓ "丽亮丶亮丷") (ℓ "亮丶亮丷丽") tt tt Eq.refl

wp0908 : Base 4 → WsL → ⟪ (ℓ "五乕") ⟫ʷ ≈ ⟪ (ℓ "乕五") ⟫ʷ
wp0908 c4 L = pw2 c4 L (ℓ "五乕") (ℓ "乕五") tt tt Eq.refl

wp0909 : Base 4 → WsL → ⟪ (ℓ "亜乩") ⟫ʷ ≈ ⟪ (ℓ "乩亜") ⟫ʷ
wp0909 c4 L = pw1 c4 L (ℓ "亜乩") (ℓ "乩亜") tt tt Eq.refl

wp0910 : Base 4 → WsL → ⟪ (ℓ "乕亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷乕") ⟫ʷ
wp0910 c4 L = pw2 c4 L (ℓ "乕亮丶亮丷") (ℓ "亮丶亮丷乕") tt tt Eq.refl

wp0911 : Base 4 → WsL → ⟪ (ℓ "亜乽亘") ⟫ʷ ≈ ⟪ (ℓ "乽亜") ⟫ʷ
wp0911 c4 L = pw1 c4 L (ℓ "亜乽亘") (ℓ "乽亜") tt tt Eq.refl

wp0912 : Base 4 → WsL → ⟪ (ℓ "乽亘亘") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wp0912 c4 L = pw1 c4 L (ℓ "乽亘亘") (ℓ "乽") tt tt Eq.refl

wp0913 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乽亐乽") ⟫ʷ
wp0913 c4 L = pw2 c4 L (ℓ "亐") (ℓ "乽亐乽") tt tt Eq.refl

wp0914 : Base 4 → WsL → ⟪ (ℓ "亜争") ⟫ʷ ≈ ⟪ (ℓ "争亜") ⟫ʷ
wp0914 c4 L = pw1 c4 L (ℓ "亜争") (ℓ "争亜") tt tt Eq.refl

wp0915 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "争五争") ⟫ʷ
wp0915 c4 L = pw2 c4 L (ℓ "五") (ℓ "争五争") tt tt Eq.refl

wp0916 : Base 4 → WsL → ⟪ (ℓ "亐争") ⟫ʷ ≈ ⟪ (ℓ "争五亐") ⟫ʷ
wp0916 c4 L = pw2 c4 L (ℓ "亐争") (ℓ "争五亐") tt tt Eq.refl

wp0917 : Base 4 → WsL → ⟪ (ℓ "五乽") ⟫ʷ ≈ ⟪ (ℓ "乽亐五") ⟫ʷ
wp0917 c4 L = pw2 c4 L (ℓ "五乽") (ℓ "乽亐五") tt tt Eq.refl

wp0918 : Base 4 → WsL → ⟪ (ℓ "亐五亐五亐") ⟫ʷ ≈ ⟪ (ℓ "亐") ⟫ʷ
wp0918 c4 L = pw2 c4 L (ℓ "亐五亐五亐") (ℓ "亐") tt tt Eq.refl
