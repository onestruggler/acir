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

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp0001 : Base 4 → WsL → ⟪ (ℓ "亠丨") ⟫ʷ ≈ ⟪ (ℓ "丨亠") ⟫ʷ
wp0001 c4 L = pw2 c4 L (ℓ "亠丨") (ℓ "丨亠") tt tt Eq.refl

wp0002 : Base 4 → WsL → ⟪ (ℓ "亠丰") ⟫ʷ ≈ ⟪ (ℓ "丰亠") ⟫ʷ
wp0002 c4 L = pw1 c4 L (ℓ "亠丰") (ℓ "丰亠") tt tt Eq.refl

wp0003 : Base 4 → WsL → ⟪ (ℓ "亠丯") ⟫ʷ ≈ ⟪ (ℓ "丯亠") ⟫ʷ
wp0003 c4 L = pw1 c4 L (ℓ "亠丯") (ℓ "丯亠") tt tt Eq.refl

wp0004 : Base 4 → WsL → ⟪ (ℓ "丌亠不") ⟫ʷ ≈ ⟪ (ℓ "亡") ⟫ʷ
wp0004 c4 L = pw1 c4 L (ℓ "丌亠不") (ℓ "亡") tt tt Eq.refl

wp0005 : Base 4 → WsL → ⟪ (ℓ "乺上亡下") ⟫ʷ ≈ ⟪ (ℓ "亡亠") ⟫ʷ
wp0005 c4 L = pw1 c4 L (ℓ "乺上亡下") (ℓ "亡亠") tt tt Eq.refl

wp0006 : Base 4 → WsL → ⟪ (ℓ "亡亡") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0006 c4 L = pw1 c4 L (ℓ "亡亡") [] tt tt Eq.refl

wp0007 : Base 4 → WsL → ⟪ (ℓ "亠亠") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0007 c4 L = pw1 c4 L (ℓ "亠亠") [] tt tt Eq.refl

wp0008 : Base 4 → WsL → ⟪ (ℓ "亐互乗互亐乗") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0008 c4 L = pw2 c4 L (ℓ "亐互乗互亐乗") (ℓ "亠") tt tt Eq.refl

wp0009 : Base 4 → WsL → ⟪ (ℓ "个亡") ⟫ʷ ≈ ⟪ (ℓ "亡个京") ⟫ʷ
wp0009 c4 L = pw2 c4 L (ℓ "个亡") (ℓ "亡个京") tt tt Eq.refl

wp0010 : Base 4 → WsL → ⟪ (ℓ "亡业") ⟫ʷ ≈ ⟪ (ℓ "业亡") ⟫ʷ
wp0010 c4 L = pw1 c4 L (ℓ "亡业") (ℓ "业亡") tt tt Eq.refl

wp0011 : Base 4 → WsL → ⟪ (ℓ "二乕") ⟫ʷ ≈ ⟪ (ℓ "乕二") ⟫ʷ
wp0011 c4 L = pw3 c4 L (ℓ "二乕") (ℓ "乕二") tt tt Eq.refl

wp0012 : Base 4 → WsL → ⟪ (ℓ "京亡") ⟫ʷ ≈ ⟪ (ℓ "亡京") ⟫ʷ
wp0012 c4 L = pw2 c4 L (ℓ "京亡") (ℓ "亡京") tt tt Eq.refl

wp0013 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "乩乁乪乁丯") ⟫ʷ
wp0013 c4 L = pw1 c4 L (ℓ "亜") (ℓ "乩乁乪乁丯") tt tt Eq.refl

wp0014 : Base 4 → WsL → ⟪ (ℓ "丘亜丙") ⟫ʷ ≈ ⟪ (ℓ "亞") ⟫ʷ
wp0014 c4 L = pw1 c4 L (ℓ "丘亜丙") (ℓ "亞") tt tt Eq.refl

wp0015 : Base 4 → WsL → ⟪ (ℓ "举世亞丗") ⟫ʷ ≈ ⟪ (ℓ "亞亜") ⟫ʷ
wp0015 c4 L = pw1 c4 L (ℓ "举世亞丗") (ℓ "亞亜") tt tt Eq.refl

wp0016 : Base 4 → WsL → ⟪ (ℓ "举乏") ⟫ʷ ≈ ⟪ (ℓ "乏举") ⟫ʷ
wp0016 c4 L = pw2 c4 L (ℓ "举乏") (ℓ "乏举") tt tt Eq.refl

wp0017 : Base 4 → WsL → ⟪ (ℓ "举世") ⟫ʷ ≈ ⟪ (ℓ "世举") ⟫ʷ
wp0017 c4 L = pw1 c4 L (ℓ "举世") (ℓ "世举") tt tt Eq.refl

wp0018 : Base 4 → WsL → ⟪ (ℓ "举丗") ⟫ʷ ≈ ⟪ (ℓ "丗举") ⟫ʷ
wp0018 c4 L = pw1 c4 L (ℓ "举丗") (ℓ "丗举") tt tt Eq.refl

wp0019 : Base 4 → WsL → ⟪ (ℓ "亞亞") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0019 c4 L = pw1 c4 L (ℓ "亞亞") [] tt tt Eq.refl

wp0020 : Base 4 → WsL → ⟪ (ℓ "亜並丱") ⟫ʷ ≈ ⟪ (ℓ "並亜") ⟫ʷ
wp0020 c4 L = pw3 c4 L (ℓ "亜並丱") (ℓ "並亜") tt tt Eq.refl

wp0021 : Base 4 → WsL → ⟪ (ℓ "亜丶") ⟫ʷ ≈ ⟪ (ℓ "丶亜") ⟫ʷ
wp0021 c4 L = pw1 c4 L (ℓ "亜丶") (ℓ "丶亜") tt tt Eq.refl

wp0022 : Base 4 → WsL → ⟪ (ℓ "亜丬") ⟫ʷ ≈ ⟪ (ℓ "丬亜") ⟫ʷ
wp0022 c4 L = pw3 c4 L (ℓ "亜丬") (ℓ "丬亜") tt tt Eq.refl

wp0023 : Base 4 → WsL → ⟪ (ℓ "亜丱") ⟫ʷ ≈ ⟪ (ℓ "丱亜") ⟫ʷ
wp0023 c4 L = pw3 c4 L (ℓ "亜丱") (ℓ "丱亜") tt tt Eq.refl

wp0024 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "並亐並") ⟫ʷ
wp0024 c4 L = pw2 c4 L (ℓ "亐") (ℓ "並亐並") tt tt Eq.refl

wp0025 : Base 4 → WsL → ⟪ (ℓ "亜亞") ⟫ʷ ≈ ⟪ (ℓ "亞亜丿") ⟫ʷ
wp0025 c4 L = pw1 c4 L (ℓ "亜亞") (ℓ "亞亜丿") tt tt Eq.refl

wp0026 : Base 4 → WsL → ⟪ (ℓ "亜丿亞亜") ⟫ʷ ≈ ⟪ (ℓ "亞") ⟫ʷ
wp0026 c4 L = pw1 c4 L (ℓ "亜丿亞亜") (ℓ "亞") tt tt Eq.refl

wp0027 : Base 4 → WsL → ⟪ (ℓ "亜亞丿") ⟫ʷ ≈ ⟪ (ℓ "亞亜") ⟫ʷ
wp0027 c4 L = pw1 c4 L (ℓ "亜亞丿") (ℓ "亞亜") tt tt Eq.refl

wp0028 : Base 4 → WsL → ⟪ (ℓ "亜亞") ⟫ʷ ≈ ⟪ (ℓ "亞丿亜") ⟫ʷ
wp0028 c4 L = pw1 c4 L (ℓ "亜亞") (ℓ "亞丿亜") tt tt Eq.refl

wp0029 : Base 4 → WsL → ⟪ (ℓ "丨亮") ⟫ʷ ≈ ⟪ (ℓ "亮丨") ⟫ʷ
wp0029 c4 L = pw2 c4 L (ℓ "丨亮") (ℓ "亮丨") tt tt Eq.refl

wp0030 : Base 4 → WsL → ⟪ (ℓ "亐五亮") ⟫ʷ ≈ ⟪ (ℓ "亮亐") ⟫ʷ
wp0030 c4 L = pw2 c4 L (ℓ "亐五亮") (ℓ "亮亐") tt tt Eq.refl

wp0031 : Base 4 → WsL → ⟪ (ℓ "並丨亐五") ⟫ʷ ≈ ⟪ (ℓ "並乒乒丨亐五") ⟫ʷ
wp0031 c4 L = pw2 c4 L (ℓ "並丨亐五") (ℓ "並乒乒丨亐五") tt tt Eq.refl

wp0032 : Base 4 → WsL → ⟪ (ℓ "亜丷") ⟫ʷ ≈ ⟪ (ℓ "丷亜") ⟫ʷ
wp0032 c4 L = pw1 c4 L (ℓ "亜丷") (ℓ "丷亜") tt tt Eq.refl

wp0033 : Base 4 → WsL → ⟪ (ℓ "亜丟") ⟫ʷ ≈ ⟪ (ℓ "丟亜") ⟫ʷ
wp0033 c4 L = pw1 c4 L (ℓ "亜丟") (ℓ "丟亜") tt tt Eq.refl

wp0034 : Base 4 → WsL → ⟪ (ℓ "亜乕") ⟫ʷ ≈ ⟪ (ℓ "乕亜") ⟫ʷ
wp0034 c4 L = pw3 c4 L (ℓ "亜乕") (ℓ "乕亜") tt tt Eq.refl

wp0035 : Base 4 → WsL → ⟪ (ℓ "亜乺") ⟫ʷ ≈ ⟪ (ℓ "乺亜") ⟫ʷ
wp0035 c4 L = pw1 c4 L (ℓ "亜乺") (ℓ "乺亜") tt tt Eq.refl

wp0036 : Base 4 → WsL → ⟪ (ℓ "亜乹") ⟫ʷ ≈ ⟪ (ℓ "乹亜") ⟫ʷ
wp0036 c4 L = pw1 c4 L (ℓ "亜乹") (ℓ "乹亜") tt tt Eq.refl

wp0037 : Base 4 → WsL → ⟪ (ℓ "亜丞") ⟫ʷ ≈ ⟪ (ℓ "丞亜") ⟫ʷ
wp0037 c4 L = pw1 c4 L (ℓ "亜丞") (ℓ "丞亜") tt tt Eq.refl

wp0038 : Base 4 → WsL → ⟪ (ℓ "五亜") ⟫ʷ ≈ ⟪ (ℓ "亜五") ⟫ʷ
wp0038 c4 L = pw3 c4 L (ℓ "五亜") (ℓ "亜五") tt tt Eq.refl

wp0039 : Base 4 → WsL → ⟪ (ℓ "亜丨") ⟫ʷ ≈ ⟪ (ℓ "丨亜") ⟫ʷ
wp0039 c4 L = pw3 c4 L (ℓ "亜丨") (ℓ "丨亜") tt tt Eq.refl

wp0040 : Base 4 → WsL → ⟪ (ℓ "亐丨亐五亮丶") ⟫ʷ ≈ ⟪ (ℓ "亮丨丶五") ⟫ʷ
wp0040 c4 L = pw2 c4 L (ℓ "亐丨亐五亮丶") (ℓ "亮丨丶五") tt tt Eq.refl

wp0041 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "乕乁乖乁丨") ⟫ʷ
wp0041 c4 L = pw2 c4 L (ℓ "五") (ℓ "乕乁乖乁丨") tt tt Eq.refl

wp0042 : Base 4 → WsL → ⟪ (ℓ "亜亪五") ⟫ʷ ≈ ⟪ (ℓ "亪亜") ⟫ʷ
wp0042 c4 L = pw3 c4 L (ℓ "亜亪五") (ℓ "亪亜") tt tt Eq.refl

wp0043 : Base 4 → WsL → ⟪ (ℓ "五亮丨丶五") ⟫ʷ ≈ ⟪ (ℓ "亮丨丶") ⟫ʷ
wp0043 c4 L = pw2 c4 L (ℓ "五亮丨丶五") (ℓ "亮丨丶") tt tt Eq.refl

wp0044 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亪五亪") ⟫ʷ
wp0044 c4 L = pw3 c4 L (ℓ "五") (ℓ "亪五亪") tt tt Eq.refl

wp0045 : Base 4 → WsL → ⟪ (ℓ "丨") ⟫ʷ ≈ ⟪ (ℓ "亮丨丶五亮丷亮丶亮丷") ⟫ʷ
wp0045 c4 L = pw2 c4 L (ℓ "丨") (ℓ "亮丨丶五亮丷亮丶亮丷") tt tt Eq.refl

wp0046 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "丽乙举乙丨") ⟫ʷ
wp0046 c4 L = pw2 c4 L (ℓ "五") (ℓ "丽乙举乙丨") tt tt Eq.refl

wp0047 : Base 4 → WsL → ⟪ (ℓ "亘举") ⟫ʷ ≈ ⟪ (ℓ "举亘") ⟫ʷ
wp0047 c4 L = pw1 c4 L (ℓ "亘举") (ℓ "举亘") tt tt Eq.refl

wp0048 : Base 4 → WsL → ⟪ (ℓ "亘丽") ⟫ʷ ≈ ⟪ (ℓ "丽亘") ⟫ʷ
wp0048 c4 L = pw1 c4 L (ℓ "亘丽") (ℓ "丽亘") tt tt Eq.refl

wp0049 : Base 4 → WsL → ⟪ (ℓ "丌五不") ⟫ʷ ≈ ⟪ (ℓ "井") ⟫ʷ
wp0049 c4 L = pw2 c4 L (ℓ "丌五不") (ℓ "井") tt tt Eq.refl

wp0050 : Base 4 → WsL → ⟪ (ℓ "乖上井下") ⟫ʷ ≈ ⟪ (ℓ "井五") ⟫ʷ
wp0050 c4 L = pw2 c4 L (ℓ "乖上井下") (ℓ "井五") tt tt Eq.refl

wp0051 : Base 4 → WsL → ⟪ (ℓ "井井") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0051 c4 L = pw2 c4 L (ℓ "井井") [] tt tt Eq.refl

wp0052 : Base 4 → WsL → ⟪ (ℓ "五並个") ⟫ʷ ≈ ⟪ (ℓ "並五") ⟫ʷ
wp0052 c4 L = pw2 c4 L (ℓ "五並个") (ℓ "並五") tt tt Eq.refl

wp0053 : Base 4 → WsL → ⟪ (ℓ "五乎") ⟫ʷ ≈ ⟪ (ℓ "乎五") ⟫ʷ
wp0053 c4 L = pw2 c4 L (ℓ "五乎") (ℓ "乎五") tt tt Eq.refl

wp0054 : Base 4 → WsL → ⟪ (ℓ "五之") ⟫ʷ ≈ ⟪ (ℓ "之五") ⟫ʷ
wp0054 c4 L = pw3 c4 L (ℓ "五之") (ℓ "之五") tt tt Eq.refl

wp0055 : Base 4 → WsL → ⟪ (ℓ "五个") ⟫ʷ ≈ ⟪ (ℓ "个五") ⟫ʷ
wp0055 c4 L = pw2 c4 L (ℓ "五个") (ℓ "个五") tt tt Eq.refl

wp0056 : Base 4 → WsL → ⟪ (ℓ "五井") ⟫ʷ ≈ ⟪ (ℓ "井五乗") ⟫ʷ
wp0056 c4 L = pw2 c4 L (ℓ "五井") (ℓ "井五乗") tt tt Eq.refl

wp0057 : Base 4 → WsL → ⟪ (ℓ "五乗井五") ⟫ʷ ≈ ⟪ (ℓ "井") ⟫ʷ
wp0057 c4 L = pw2 c4 L (ℓ "五乗井五") (ℓ "井") tt tt Eq.refl

wp0058 : Base 4 → WsL → ⟪ (ℓ "五井乗") ⟫ʷ ≈ ⟪ (ℓ "井五") ⟫ʷ
wp0058 c4 L = pw2 c4 L (ℓ "五井乗") (ℓ "井五") tt tt Eq.refl

wp0059 : Base 4 → WsL → ⟪ (ℓ "五井") ⟫ʷ ≈ ⟪ (ℓ "井乗五") ⟫ʷ
wp0059 c4 L = pw2 c4 L (ℓ "五井") (ℓ "井乗五") tt tt Eq.refl

wp0060 : Base 4 → WsL → ⟪ (ℓ "五乏") ⟫ʷ ≈ ⟪ (ℓ "乏五") ⟫ʷ
wp0060 c4 L = pw2 c4 L (ℓ "五乏") (ℓ "乏五") tt tt Eq.refl

wp0061 : Base 4 → WsL → ⟪ (ℓ "五丟") ⟫ʷ ≈ ⟪ (ℓ "丟五") ⟫ʷ
wp0061 c4 L = pw2 c4 L (ℓ "五丟") (ℓ "丟五") tt tt Eq.refl

wp0062 : Base 4 → WsL → ⟪ (ℓ "五乩") ⟫ʷ ≈ ⟪ (ℓ "乩五") ⟫ʷ
wp0062 c4 L = pw3 c4 L (ℓ "五乩") (ℓ "乩五") tt tt Eq.refl

wp0063 : Base 4 → WsL → ⟪ (ℓ "五乺") ⟫ʷ ≈ ⟪ (ℓ "乺五") ⟫ʷ
wp0063 c4 L = pw2 c4 L (ℓ "五乺") (ℓ "乺五") tt tt Eq.refl

wp0064 : Base 4 → WsL → ⟪ (ℓ "五乹") ⟫ʷ ≈ ⟪ (ℓ "乹五") ⟫ʷ
wp0064 c4 L = pw2 c4 L (ℓ "五乹") (ℓ "乹五") tt tt Eq.refl

wp0065 : Base 4 → WsL → ⟪ (ℓ "五丞") ⟫ʷ ≈ ⟪ (ℓ "丞五") ⟫ʷ
wp0065 c4 L = pw2 c4 L (ℓ "五丞") (ℓ "丞五") tt tt Eq.refl

wp0066 : Base 4 → WsL → ⟪ (ℓ "五亨") ⟫ʷ ≈ ⟪ (ℓ "亨五") ⟫ʷ
wp0066 c4 L = pw3 c4 L (ℓ "五亨") (ℓ "亨五") tt tt Eq.refl

wp0067 : Base 4 → WsL → ⟪ (ℓ "五乇") ⟫ʷ ≈ ⟪ (ℓ "乇五") ⟫ʷ
wp0067 c4 L = pw3 c4 L (ℓ "五乇") (ℓ "乇五") tt tt Eq.refl

wp0068 : Base 4 → WsL → ⟪ (ℓ "亙亝亲") ⟫ʷ ≈ ⟪ (ℓ "亲亙") ⟫ʷ
wp0068 c4 L = pw1 c4 L (ℓ "亙亝亲") (ℓ "亲亙") tt tt Eq.refl

wp0069 : Base 4 → WsL → ⟪ (ℓ "乪亙") ⟫ʷ ≈ ⟪ (ℓ "亙乪") ⟫ʷ
wp0069 c4 L = pw1 c4 L (ℓ "乪亙") (ℓ "亙乪") tt tt Eq.refl

wp0070 : Base 4 → WsL → ⟪ (ℓ "乩亙") ⟫ʷ ≈ ⟪ (ℓ "亙乩") ⟫ʷ
wp0070 c4 L = pw1 c4 L (ℓ "乩亙") (ℓ "亙乩") tt tt Eq.refl

wp0071 : Base 4 → WsL → ⟪ (ℓ "五亝亨") ⟫ʷ ≈ ⟪ (ℓ "亝五") ⟫ʷ
wp0071 c4 L = pw3 c4 L (ℓ "五亝亨") (ℓ "亝五") tt tt Eq.refl

wp0072 : Base 4 → WsL → ⟪ (ℓ "亙亝") ⟫ʷ ≈ ⟪ (ℓ "亝亙") ⟫ʷ
wp0072 c4 L = pw1 c4 L (ℓ "亙亝") (ℓ "亝亙") tt tt Eq.refl

wp0073 : Base 4 → WsL → ⟪ (ℓ "亝亝亲") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wp0073 c4 L = pw1 c4 L (ℓ "亝亝亲") (ℓ "亲") tt tt Eq.refl

wp0074 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亝亨亝") ⟫ʷ
wp0074 c4 L = pw3 c4 L (ℓ "亨") (ℓ "亝亨亝") tt tt Eq.refl

wp0075 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丽乭举乭丯") ⟫ʷ
wp0075 c4 L = pw1 c4 L (ℓ "亜") (ℓ "丽乭举乭丯") tt tt Eq.refl

wp0076 : Base 4 → WsL → ⟪ (ℓ "亐举") ⟫ʷ ≈ ⟪ (ℓ "举亐") ⟫ʷ
wp0076 c4 L = pw2 c4 L (ℓ "亐举") (ℓ "举亐") tt tt Eq.refl

wp0077 : Base 4 → WsL → ⟪ (ℓ "亐丽") ⟫ʷ ≈ ⟪ (ℓ "丽亐") ⟫ʷ
wp0077 c4 L = pw2 c4 L (ℓ "亐丽") (ℓ "丽亐") tt tt Eq.refl

wp0078 : Base 4 → WsL → ⟪ (ℓ "丌亜不") ⟫ʷ ≈ ⟪ (ℓ "亝") ⟫ʷ
wp0078 c4 L = pw1 c4 L (ℓ "丌亜不") (ℓ "亝") tt tt Eq.refl

wp0079 : Base 4 → WsL → ⟪ (ℓ "乪上亝下") ⟫ʷ ≈ ⟪ (ℓ "亝亜") ⟫ʷ
wp0079 c4 L = pw1 c4 L (ℓ "乪上亝下") (ℓ "亝亜") tt tt Eq.refl

wp0080 : Base 4 → WsL → ⟪ (ℓ "亝亝") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0080 c4 L = pw1 c4 L (ℓ "亝亝") [] tt tt Eq.refl

wp0081 : Base 4 → WsL → ⟪ (ℓ "亜乇") ⟫ʷ ≈ ⟪ (ℓ "乇亜") ⟫ʷ
wp0081 c4 L = pw3 c4 L (ℓ "亜乇") (ℓ "乇亜") tt tt Eq.refl

wp0082 : Base 4 → WsL → ⟪ (ℓ "亜书") ⟫ʷ ≈ ⟪ (ℓ "书亜") ⟫ʷ
wp0082 c4 L = pw1 c4 L (ℓ "亜书") (ℓ "书亜") tt tt Eq.refl

wp0083 : Base 4 → WsL → ⟪ (ℓ "亜亝") ⟫ʷ ≈ ⟪ (ℓ "亝亜乫") ⟫ʷ
wp0083 c4 L = pw1 c4 L (ℓ "亜亝") (ℓ "亝亜乫") tt tt Eq.refl

wp0084 : Base 4 → WsL → ⟪ (ℓ "亜乫亝亜") ⟫ʷ ≈ ⟪ (ℓ "亝") ⟫ʷ
wp0084 c4 L = pw1 c4 L (ℓ "亜乫亝亜") (ℓ "亝") tt tt Eq.refl

wp0085 : Base 4 → WsL → ⟪ (ℓ "亜亝乫") ⟫ʷ ≈ ⟪ (ℓ "亝亜") ⟫ʷ
wp0085 c4 L = pw1 c4 L (ℓ "亜亝乫") (ℓ "亝亜") tt tt Eq.refl

wp0086 : Base 4 → WsL → ⟪ (ℓ "亜亝") ⟫ʷ ≈ ⟪ (ℓ "亝乫亜") ⟫ʷ
wp0086 c4 L = pw1 c4 L (ℓ "亜亝") (ℓ "亝乫亜") tt tt Eq.refl

wp0087 : Base 4 → WsL → ⟪ (ℓ "亜么") ⟫ʷ ≈ ⟪ (ℓ "么亜") ⟫ʷ
wp0087 c4 L = pw3 c4 L (ℓ "亜么") (ℓ "么亜") tt tt Eq.refl

wp0088 : Base 4 → WsL → ⟪ (ℓ "亜专") ⟫ʷ ≈ ⟪ (ℓ "专亜") ⟫ʷ
wp0088 c4 L = pw3 c4 L (ℓ "亜专") (ℓ "专亜") tt tt Eq.refl

wp0089 : Base 4 → WsL → ⟪ (ℓ "亜丒") ⟫ʷ ≈ ⟪ (ℓ "丒亜") ⟫ʷ
wp0089 c4 L = pw3 c4 L (ℓ "亜丒") (ℓ "丒亜") tt tt Eq.refl

wp0090 : Base 4 → WsL → ⟪ (ℓ "亜亰") ⟫ʷ ≈ ⟪ (ℓ "亰亜") ⟫ʷ
wp0090 c4 L = pw1 c4 L (ℓ "亜亰") (ℓ "亰亜") tt tt Eq.refl

wp0091 : Base 4 → WsL → ⟪ (ℓ "亜乣") ⟫ʷ ≈ ⟪ (ℓ "乣亜") ⟫ʷ
wp0091 c4 L = pw1 c4 L (ℓ "亜乣") (ℓ "乣亜") tt tt Eq.refl

wp0092 : Base 4 → WsL → ⟪ (ℓ "亜乢") ⟫ʷ ≈ ⟪ (ℓ "乢亜") ⟫ʷ
wp0092 c4 L = pw1 c4 L (ℓ "亜乢") (ℓ "乢亜") tt tt Eq.refl

wp0093 : Base 4 → WsL → ⟪ (ℓ "云亡亭") ⟫ʷ ≈ ⟪ (ℓ "亭云") ⟫ʷ
wp0093 c4 L = pw2 c4 L (ℓ "云亡亭") (ℓ "亭云") tt tt Eq.refl

wp0094 : Base 4 → WsL → ⟪ (ℓ "乺云") ⟫ʷ ≈ ⟪ (ℓ "云乺") ⟫ʷ
wp0094 c4 L = pw2 c4 L (ℓ "乺云") (ℓ "云乺") tt tt Eq.refl

wp0095 : Base 4 → WsL → ⟪ (ℓ "乹云") ⟫ʷ ≈ ⟪ (ℓ "云乹") ⟫ʷ
wp0095 c4 L = pw2 c4 L (ℓ "乹云") (ℓ "云乹") tt tt Eq.refl

wp0096 : Base 4 → WsL → ⟪ (ℓ "亜亡亰") ⟫ʷ ≈ ⟪ (ℓ "亡亜") ⟫ʷ
wp0096 c4 L = pw1 c4 L (ℓ "亜亡亰") (ℓ "亡亜") tt tt Eq.refl

wp0097 : Base 4 → WsL → ⟪ (ℓ "云亡") ⟫ʷ ≈ ⟪ (ℓ "亡云") ⟫ʷ
wp0097 c4 L = pw2 c4 L (ℓ "云亡") (ℓ "亡云") tt tt Eq.refl

wp0098 : Base 4 → WsL → ⟪ (ℓ "乢亰") ⟫ʷ ≈ ⟪ (ℓ "乢亡亰亡") ⟫ʷ
wp0098 c4 L = pw1 c4 L (ℓ "乢亰") (ℓ "乢亡亰亡") tt tt Eq.refl

wp0099 : Base 4 → WsL → ⟪ (ℓ "亡亡亭") ⟫ʷ ≈ ⟪ (ℓ "亭") ⟫ʷ
wp0099 c4 L = pw2 c4 L (ℓ "亡亡亭") (ℓ "亭") tt tt Eq.refl

wp0100 : Base 4 → WsL → ⟪ (ℓ "亠云京") ⟫ʷ ≈ ⟪ (ℓ "云亠") ⟫ʷ
wp0100 c4 L = pw2 c4 L (ℓ "亠云京") (ℓ "云亠") tt tt Eq.refl

wp0101 : Base 4 → WsL → ⟪ (ℓ "亠乶") ⟫ʷ ≈ ⟪ (ℓ "乶亠") ⟫ʷ
wp0101 c4 L = pw1 c4 L (ℓ "亠乶") (ℓ "乶亠") tt tt Eq.refl

wp0102 : Base 4 → WsL → ⟪ (ℓ "乕亍") ⟫ʷ ≈ ⟪ (ℓ "亍乕") ⟫ʷ
wp0102 c4 L = pw3 c4 L (ℓ "乕亍") (ℓ "亍乕") tt tt Eq.refl

wp0103 : Base 4 → WsL → ⟪ (ℓ "亠京") ⟫ʷ ≈ ⟪ (ℓ "京亠") ⟫ʷ
wp0103 c4 L = pw2 c4 L (ℓ "亠京") (ℓ "京亠") tt tt Eq.refl

wp0104 : Base 4 → WsL → ⟪ (ℓ "亠书亜") ⟫ʷ ≈ ⟪ (ℓ "书亠") ⟫ʷ
wp0104 c4 L = pw1 c4 L (ℓ "亠书亜") (ℓ "书亠") tt tt Eq.refl

wp0105 : Base 4 → WsL → ⟪ (ℓ "亜亍") ⟫ʷ ≈ ⟪ (ℓ "亍亜亨") ⟫ʷ
wp0105 c4 L = pw3 c4 L (ℓ "亜亍") (ℓ "亍亜亨") tt tt Eq.refl

wp0106 : Base 4 → WsL → ⟪ (ℓ "亠乕") ⟫ʷ ≈ ⟪ (ℓ "乕亠") ⟫ʷ
wp0106 c4 L = pw2 c4 L (ℓ "亠乕") (ℓ "乕亠") tt tt Eq.refl

wp0107 : Base 4 → WsL → ⟪ (ℓ "亠乪") ⟫ʷ ≈ ⟪ (ℓ "乪亠") ⟫ʷ
wp0107 c4 L = pw1 c4 L (ℓ "亠乪") (ℓ "乪亠") tt tt Eq.refl

wp0108 : Base 4 → WsL → ⟪ (ℓ "亠乩") ⟫ʷ ≈ ⟪ (ℓ "乩亠") ⟫ʷ
wp0108 c4 L = pw1 c4 L (ℓ "亠乩") (ℓ "乩亠") tt tt Eq.refl

wp0109 : Base 4 → WsL → ⟪ (ℓ "亜亠") ⟫ʷ ≈ ⟪ (ℓ "亠亜") ⟫ʷ
wp0109 c4 L = pw1 c4 L (ℓ "亜亠") (ℓ "亠亜") tt tt Eq.refl

wp0110 : Base 4 → WsL → ⟪ (ℓ "书亜亜") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
wp0110 c4 L = pw1 c4 L (ℓ "书亜亜") (ℓ "书") tt tt Eq.refl

wp0111 : Base 4 → WsL → ⟪ (ℓ "亘亚乫亚亘乫") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0111 c4 L = pw1 c4 L (ℓ "亘亚乫亚亘乫") (ℓ "亠") tt tt Eq.refl

wp0112 : Base 4 → WsL → ⟪ (ℓ "亠乻亡") ⟫ʷ ≈ ⟪ (ℓ "亡亠") ⟫ʷ
wp0112 c4 L = pw1 c4 L (ℓ "亠乻亡") (ℓ "亡亠") tt tt Eq.refl

wp0113 : Base 4 → WsL → ⟪ (ℓ "亠乻") ⟫ʷ ≈ ⟪ (ℓ "亡亠亡") ⟫ʷ
wp0113 c4 L = pw1 c4 L (ℓ "亠乻") (ℓ "亡亠亡") tt tt Eq.refl

wp0114 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "乻亠乻") ⟫ʷ
wp0114 c4 L = pw1 c4 L (ℓ "亠") (ℓ "乻亠乻") tt tt Eq.refl

wp0115 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丽乽举乽丶") ⟫ʷ
wp0115 c4 L = pw1 c4 L (ℓ "亠") (ℓ "丽乽举乽丶") tt tt Eq.refl

wp0116 : Base 4 → WsL → ⟪ (ℓ "二举") ⟫ʷ ≈ ⟪ (ℓ "举二") ⟫ʷ
wp0116 c4 L = pw3 c4 L (ℓ "二举") (ℓ "举二") tt tt Eq.refl

wp0117 : Base 4 → WsL → ⟪ (ℓ "二丽") ⟫ʷ ≈ ⟪ (ℓ "丽二") ⟫ʷ
wp0117 c4 L = pw3 c4 L (ℓ "二丽") (ℓ "丽二") tt tt Eq.refl

wp0118 : Base 4 → WsL → ⟪ (ℓ "亠亡") ⟫ʷ ≈ ⟪ (ℓ "亡亠乻") ⟫ʷ
wp0118 c4 L = pw1 c4 L (ℓ "亠亡") (ℓ "亡亠乻") tt tt Eq.refl

wp0119 : Base 4 → WsL → ⟪ (ℓ "亠乻亡亠") ⟫ʷ ≈ ⟪ (ℓ "亡") ⟫ʷ
wp0119 c4 L = pw1 c4 L (ℓ "亠乻亡亠") (ℓ "亡") tt tt Eq.refl

wp0120 : Base 4 → WsL → ⟪ (ℓ "亠丩") ⟫ʷ ≈ ⟪ (ℓ "丩亠") ⟫ʷ
wp0120 c4 L = pw2 c4 L (ℓ "亠丩") (ℓ "丩亠") tt tt Eq.refl

wp0121 : Base 4 → WsL → ⟪ (ℓ "亠乒五") ⟫ʷ ≈ ⟪ (ℓ "乒亠") ⟫ʷ
wp0121 c4 L = pw2 c4 L (ℓ "亠乒五") (ℓ "乒亠") tt tt Eq.refl

wp0122 : Base 4 → WsL → ⟪ (ℓ "五亍") ⟫ʷ ≈ ⟪ (ℓ "亍五亨") ⟫ʷ
wp0122 c4 L = pw3 c4 L (ℓ "五亍") (ℓ "亍五亨") tt tt Eq.refl

wp0123 : Base 4 → WsL → ⟪ (ℓ "亠乖") ⟫ʷ ≈ ⟪ (ℓ "乖亠") ⟫ʷ
wp0123 c4 L = pw2 c4 L (ℓ "亠乖") (ℓ "乖亠") tt tt Eq.refl

wp0124 : Base 4 → WsL → ⟪ (ℓ "五亠") ⟫ʷ ≈ ⟪ (ℓ "亠五") ⟫ʷ
wp0124 c4 L = pw2 c4 L (ℓ "五亠") (ℓ "亠五") tt tt Eq.refl

wp0125 : Base 4 → WsL → ⟪ (ℓ "乒五五") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wp0125 c4 L = pw2 c4 L (ℓ "乒五五") (ℓ "乒") tt tt Eq.refl

wp0126 : Base 4 → WsL → ⟪ (ℓ "亠亙亰") ⟫ʷ ≈ ⟪ (ℓ "亙亠") ⟫ʷ
wp0126 c4 L = pw1 c4 L (ℓ "亠亙亰") (ℓ "亙亠") tt tt Eq.refl

wp0127 : Base 4 → WsL → ⟪ (ℓ "亠乳") ⟫ʷ ≈ ⟪ (ℓ "乳亠") ⟫ʷ
wp0127 c4 L = pw2 c4 L (ℓ "亠乳") (ℓ "乳亠") tt tt Eq.refl

wp0128 : Base 4 → WsL → ⟪ (ℓ "乩亍") ⟫ʷ ≈ ⟪ (ℓ "亍乩") ⟫ʷ
wp0128 c4 L = pw3 c4 L (ℓ "乩亍") (ℓ "亍乩") tt tt Eq.refl

wp0129 : Base 4 → WsL → ⟪ (ℓ "亠亰") ⟫ʷ ≈ ⟪ (ℓ "亰亠") ⟫ʷ
wp0129 c4 L = pw1 c4 L (ℓ "亠亰") (ℓ "亰亠") tt tt Eq.refl

wp0130 : Base 4 → WsL → ⟪ (ℓ "二于乗于二乗") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp0130 c4 L = pw3 c4 L (ℓ "二于乗于二乗") (ℓ "亜") tt tt Eq.refl

wp0131 : Base 4 → WsL → ⟪ (ℓ "亘些乻些亘乻") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp0131 c4 L = pw1 c4 L (ℓ "亘些乻些亘乻") (ℓ "亜") tt tt Eq.refl

wp0132 : Base 4 → WsL → ⟪ (ℓ "亜乫亝") ⟫ʷ ≈ ⟪ (ℓ "亝亜") ⟫ʷ
wp0132 c4 L = pw1 c4 L (ℓ "亜乫亝") (ℓ "亝亜") tt tt Eq.refl

wp0133 : Base 4 → WsL → ⟪ (ℓ "亜乫") ⟫ʷ ≈ ⟪ (ℓ "亝亜亝") ⟫ʷ
wp0133 c4 L = pw1 c4 L (ℓ "亜乫") (ℓ "亝亜亝") tt tt Eq.refl

wp0134 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "乫亜乫") ⟫ʷ
wp0134 c4 L = pw1 c4 L (ℓ "亜") (ℓ "乫亜乫") tt tt Eq.refl

wp0135 : Base 4 → WsL → ⟪ (ℓ "亜亜") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0135 c4 L = pw1 c4 L (ℓ "亜亜") [] tt tt Eq.refl

wp0136 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "五亗乫亗五乫") ⟫ʷ
wp0136 c4 L = pw3 c4 L (ℓ "二") (ℓ "五亗乫亗五乫") tt tt Eq.refl

wp0137 : Base 4 → WsL → ⟪ (ℓ "亃亡") ⟫ʷ ≈ ⟪ (ℓ "亡亃") ⟫ʷ
wp0137 c4 L = pw2 c4 L (ℓ "亃亡") (ℓ "亡亃") tt tt Eq.refl

wp0138 : Base 4 → WsL → ⟪ (ℓ "二亃亜") ⟫ʷ ≈ ⟪ (ℓ "亃二") ⟫ʷ
wp0138 c4 L = pw3 c4 L (ℓ "二亃亜") (ℓ "亃二") tt tt Eq.refl

wp0139 : Base 4 → WsL → ⟪ (ℓ "亜亡") ⟫ʷ ≈ ⟪ (ℓ "亡亜亰") ⟫ʷ
wp0139 c4 L = pw1 c4 L (ℓ "亜亡") (ℓ "亡亜亰") tt tt Eq.refl

wp0140 : Base 4 → WsL → ⟪ (ℓ "二乪") ⟫ʷ ≈ ⟪ (ℓ "乪二") ⟫ʷ
wp0140 c4 L = pw3 c4 L (ℓ "二乪") (ℓ "乪二") tt tt Eq.refl

wp0141 : Base 4 → WsL → ⟪ (ℓ "二乩") ⟫ʷ ≈ ⟪ (ℓ "乩二") ⟫ʷ
wp0141 c4 L = pw3 c4 L (ℓ "二乩") (ℓ "乩二") tt tt Eq.refl

wp0142 : Base 4 → WsL → ⟪ (ℓ "二亜") ⟫ʷ ≈ ⟪ (ℓ "亜二") ⟫ʷ
wp0142 c4 L = pw3 c4 L (ℓ "二亜") (ℓ "亜二") tt tt Eq.refl

wp0143 : Base 4 → WsL → ⟪ (ℓ "亃亜亜") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wp0143 c4 L = pw3 c4 L (ℓ "亃亜亜") (ℓ "亃") tt tt Eq.refl

wp0144 : Base 4 → WsL → ⟪ (ℓ "乙亡") ⟫ʷ ≈ ⟪ (ℓ "亡乙云") ⟫ʷ
wp0144 c4 L = pw2 c4 L (ℓ "乙亡") (ℓ "亡乙云") tt tt Eq.refl

wp0145 : Base 4 → WsL → ⟪ (ℓ "二乙") ⟫ʷ ≈ ⟪ (ℓ "乙二") ⟫ʷ
wp0145 c4 L = pw3 c4 L (ℓ "二乙") (ℓ "乙二") tt tt Eq.refl

wp0146 : Base 4 → WsL → ⟪ (ℓ "乢亡") ⟫ʷ ≈ ⟪ (ℓ "亡乢") ⟫ʷ
wp0146 c4 L = pw1 c4 L (ℓ "乢亡") (ℓ "亡乢") tt tt Eq.refl

wp0147 : Base 4 → WsL → ⟪ (ℓ "乳亡") ⟫ʷ ≈ ⟪ (ℓ "亡乳") ⟫ʷ
wp0147 c4 L = pw2 c4 L (ℓ "乳亡") (ℓ "亡乳") tt tt Eq.refl

wp0148 : Base 4 → WsL → ⟪ (ℓ "乙云云") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wp0148 c4 L = pw2 c4 L (ℓ "乙云云") (ℓ "乙") tt tt Eq.refl

wp0149 : Base 4 → WsL → ⟪ (ℓ "亐乘") ⟫ʷ ≈ ⟪ (ℓ "乘亠") ⟫ʷ
wp0149 c4 L = pw2 c4 L (ℓ "亐乘") (ℓ "乘亠") tt tt Eq.refl

wp0150 : Base 4 → WsL → ⟪ (ℓ "乘亡") ⟫ʷ ≈ ⟪ (ℓ "云乘") ⟫ʷ
wp0150 c4 L = pw2 c4 L (ℓ "乘亡") (ℓ "云乘") tt tt Eq.refl

wp0151 : Base 4 → WsL → ⟪ (ℓ "亠乘") ⟫ʷ ≈ ⟪ (ℓ "乘亐") ⟫ʷ
wp0151 c4 L = pw2 c4 L (ℓ "亠乘") (ℓ "乘亐") tt tt Eq.refl

wp0152 : Base 4 → WsL → ⟪ (ℓ "乘亓") ⟫ʷ ≈ ⟪ (ℓ "亢乘") ⟫ʷ
wp0152 c4 L = pw2 c4 L (ℓ "乘亓") (ℓ "亢乘") tt tt Eq.refl

wp0153 : Base 4 → WsL → ⟪ (ℓ "二亏乫亏二乫") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp0153 c4 L = pw3 c4 L (ℓ "二亏乫亏二乫") (ℓ "五") tt tt Eq.refl

wp0154 : Base 4 → WsL → ⟪ (ℓ "亐亓乻亓亐乻") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp0154 c4 L = pw2 c4 L (ℓ "亐亓乻亓亐乻") (ℓ "五") tt tt Eq.refl

wp0155 : Base 4 → WsL → ⟪ (ℓ "五丯") ⟫ʷ ≈ ⟪ (ℓ "丯五") ⟫ʷ
wp0155 c4 L = pw3 c4 L (ℓ "五丯") (ℓ "丯五") tt tt Eq.refl

wp0156 : Base 4 → WsL → ⟪ (ℓ "五丷") ⟫ʷ ≈ ⟪ (ℓ "丷五") ⟫ʷ
wp0156 c4 L = pw2 c4 L (ℓ "五丷") (ℓ "丷五") tt tt Eq.refl

wp0157 : Base 4 → WsL → ⟪ (ℓ "五丶") ⟫ʷ ≈ ⟪ (ℓ "丶五") ⟫ʷ
wp0157 c4 L = pw2 c4 L (ℓ "五丶") (ℓ "丶五") tt tt Eq.refl

wp0158 : Base 4 → WsL → ⟪ (ℓ "五乗井") ⟫ʷ ≈ ⟪ (ℓ "井五") ⟫ʷ
wp0158 c4 L = pw2 c4 L (ℓ "五乗井") (ℓ "井五") tt tt Eq.refl

wp0159 : Base 4 → WsL → ⟪ (ℓ "五乗") ⟫ʷ ≈ ⟪ (ℓ "井五井") ⟫ʷ
wp0159 c4 L = pw2 c4 L (ℓ "五乗") (ℓ "井五井") tt tt Eq.refl

wp0160 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "乗五乗") ⟫ʷ
wp0160 c4 L = pw2 c4 L (ℓ "五") (ℓ "乗五乗") tt tt Eq.refl

wp0161 : Base 4 → WsL → ⟪ (ℓ "五五") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0161 c4 L = pw2 c4 L (ℓ "五五") [] tt tt Eq.refl

wp0162 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "亜亟乗亟亜乗") ⟫ʷ
wp0162 c4 L = pw3 c4 L (ℓ "二") (ℓ "亜亟乗亟亜乗") tt tt Eq.refl

wp0163 : Base 4 → WsL → ⟪ (ℓ "了亡") ⟫ʷ ≈ ⟪ (ℓ "亡了") ⟫ʷ
wp0163 c4 L = pw1 c4 L (ℓ "了亡") (ℓ "亡了") tt tt Eq.refl

wp0164 : Base 4 → WsL → ⟪ (ℓ "二了五") ⟫ʷ ≈ ⟪ (ℓ "了二") ⟫ʷ
wp0164 c4 L = pw3 c4 L (ℓ "二了五") (ℓ "了二") tt tt Eq.refl

wp0165 : Base 4 → WsL → ⟪ (ℓ "五亡") ⟫ʷ ≈ ⟪ (ℓ "亡五京") ⟫ʷ
wp0165 c4 L = pw2 c4 L (ℓ "五亡") (ℓ "亡五京") tt tt Eq.refl

wp0166 : Base 4 → WsL → ⟪ (ℓ "二乖") ⟫ʷ ≈ ⟪ (ℓ "乖二") ⟫ʷ
wp0166 c4 L = pw3 c4 L (ℓ "二乖") (ℓ "乖二") tt tt Eq.refl

wp0167 : Base 4 → WsL → ⟪ (ℓ "二五") ⟫ʷ ≈ ⟪ (ℓ "五二") ⟫ʷ
wp0167 c4 L = pw3 c4 L (ℓ "二五") (ℓ "五二") tt tt Eq.refl

wp0168 : Base 4 → WsL → ⟪ (ℓ "了五五") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wp0168 c4 L = pw3 c4 L (ℓ "了五五") (ℓ "了") tt tt Eq.refl

wp0169 : Base 4 → WsL → ⟪ (ℓ "乭亡") ⟫ʷ ≈ ⟪ (ℓ "亡乭亙") ⟫ʷ
wp0169 c4 L = pw1 c4 L (ℓ "乭亡") (ℓ "亡乭亙") tt tt Eq.refl

wp0170 : Base 4 → WsL → ⟪ (ℓ "二乭") ⟫ʷ ≈ ⟪ (ℓ "乭二") ⟫ʷ
wp0170 c4 L = pw3 c4 L (ℓ "二乭") (ℓ "乭二") tt tt Eq.refl

wp0171 : Base 4 → WsL → ⟪ (ℓ "乎亡") ⟫ʷ ≈ ⟪ (ℓ "亡乎") ⟫ʷ
wp0171 c4 L = pw2 c4 L (ℓ "乎亡") (ℓ "亡乎") tt tt Eq.refl

wp0172 : Base 4 → WsL → ⟪ (ℓ "乶亡") ⟫ʷ ≈ ⟪ (ℓ "亡乶") ⟫ʷ
wp0172 c4 L = pw1 c4 L (ℓ "乶亡") (ℓ "亡乶") tt tt Eq.refl

wp0173 : Base 4 → WsL → ⟪ (ℓ "亙亡") ⟫ʷ ≈ ⟪ (ℓ "亡亙") ⟫ʷ
wp0173 c4 L = pw1 c4 L (ℓ "亙亡") (ℓ "亡亙") tt tt Eq.refl

wp0174 : Base 4 → WsL → ⟪ (ℓ "乭亙亙") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wp0174 c4 L = pw1 c4 L (ℓ "乭亙亙") (ℓ "乭") tt tt Eq.refl

wp0175 : Base 4 → WsL → ⟪ (ℓ "亘乬") ⟫ʷ ≈ ⟪ (ℓ "乬亠") ⟫ʷ
wp0175 c4 L = pw1 c4 L (ℓ "亘乬") (ℓ "乬亠") tt tt Eq.refl

wp0176 : Base 4 → WsL → ⟪ (ℓ "乬亡") ⟫ʷ ≈ ⟪ (ℓ "亙乬") ⟫ʷ
wp0176 c4 L = pw1 c4 L (ℓ "乬亡") (ℓ "亙乬") tt tt Eq.refl

wp0177 : Base 4 → WsL → ⟪ (ℓ "亠乬") ⟫ʷ ≈ ⟪ (ℓ "乬亘") ⟫ʷ
wp0177 c4 L = pw1 c4 L (ℓ "亠乬") (ℓ "乬亘") tt tt Eq.refl

wp0178 : Base 4 → WsL → ⟪ (ℓ "乬些") ⟫ʷ ≈ ⟪ (ℓ "亢乬") ⟫ʷ
wp0178 c4 L = pw1 c4 L (ℓ "乬些") (ℓ "亢乬") tt tt Eq.refl

wp0179 : Base 4 → WsL → ⟪ (ℓ "亜丩") ⟫ʷ ≈ ⟪ (ℓ "丩亜") ⟫ʷ
wp0179 c4 L = pw3 c4 L (ℓ "亜丩") (ℓ "丩亜") tt tt Eq.refl

wp0180 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "五亗乻亗五乻") ⟫ʷ
wp0180 c4 L = pw2 c4 L (ℓ "亐") (ℓ "五亗乻亗五乻") tt tt Eq.refl

wp0181 : Base 4 → WsL → ⟪ (ℓ "亃亝") ⟫ʷ ≈ ⟪ (ℓ "亝亃") ⟫ʷ
wp0181 c4 L = pw3 c4 L (ℓ "亃亝") (ℓ "亝亃") tt tt Eq.refl

wp0182 : Base 4 → WsL → ⟪ (ℓ "亐亃亠") ⟫ʷ ≈ ⟪ (ℓ "亃亐") ⟫ʷ
wp0182 c4 L = pw2 c4 L (ℓ "亐亃亠") (ℓ "亃亐") tt tt Eq.refl

wp0183 : Base 4 → WsL → ⟪ (ℓ "亠亝") ⟫ʷ ≈ ⟪ (ℓ "亝亠亰") ⟫ʷ
wp0183 c4 L = pw1 c4 L (ℓ "亠亝") (ℓ "亝亠亰") tt tt Eq.refl

wp0184 : Base 4 → WsL → ⟪ (ℓ "亐乺") ⟫ʷ ≈ ⟪ (ℓ "乺亐") ⟫ʷ
wp0184 c4 L = pw2 c4 L (ℓ "亐乺") (ℓ "乺亐") tt tt Eq.refl

wp0185 : Base 4 → WsL → ⟪ (ℓ "亐乹") ⟫ʷ ≈ ⟪ (ℓ "乹亐") ⟫ʷ
wp0185 c4 L = pw2 c4 L (ℓ "亐乹") (ℓ "乹亐") tt tt Eq.refl

wp0186 : Base 4 → WsL → ⟪ (ℓ "亐亠") ⟫ʷ ≈ ⟪ (ℓ "亠亐") ⟫ʷ
wp0186 c4 L = pw2 c4 L (ℓ "亐亠") (ℓ "亠亐") tt tt Eq.refl

wp0187 : Base 4 → WsL → ⟪ (ℓ "亃亠亠") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wp0187 c4 L = pw2 c4 L (ℓ "亃亠亠") (ℓ "亃") tt tt Eq.refl

wp0188 : Base 4 → WsL → ⟪ (ℓ "乙亝") ⟫ʷ ≈ ⟪ (ℓ "亝乙亍") ⟫ʷ
wp0188 c4 L = pw3 c4 L (ℓ "乙亝") (ℓ "亝乙亍") tt tt Eq.refl

wp0189 : Base 4 → WsL → ⟪ (ℓ "亐乙") ⟫ʷ ≈ ⟪ (ℓ "乙亐") ⟫ʷ
wp0189 c4 L = pw2 c4 L (ℓ "亐乙") (ℓ "乙亐") tt tt Eq.refl

wp0190 : Base 4 → WsL → ⟪ (ℓ "乢亝") ⟫ʷ ≈ ⟪ (ℓ "亝乢") ⟫ʷ
wp0190 c4 L = pw1 c4 L (ℓ "乢亝") (ℓ "亝乢") tt tt Eq.refl

wp0191 : Base 4 → WsL → ⟪ (ℓ "也亝") ⟫ʷ ≈ ⟪ (ℓ "亝也") ⟫ʷ
wp0191 c4 L = pw3 c4 L (ℓ "也亝") (ℓ "亝也") tt tt Eq.refl

wp0192 : Base 4 → WsL → ⟪ (ℓ "亍亝") ⟫ʷ ≈ ⟪ (ℓ "亝亍") ⟫ʷ
wp0192 c4 L = pw3 c4 L (ℓ "亍亝") (ℓ "亝亍") tt tt Eq.refl

wp0193 : Base 4 → WsL → ⟪ (ℓ "乙亍亍") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wp0193 c4 L = pw3 c4 L (ℓ "乙亍亍") (ℓ "乙") tt tt Eq.refl

wp0194 : Base 4 → WsL → ⟪ (ℓ "二乘") ⟫ʷ ≈ ⟪ (ℓ "乘亜") ⟫ʷ
wp0194 c4 L = pw3 c4 L (ℓ "二乘") (ℓ "乘亜") tt tt Eq.refl

wp0195 : Base 4 → WsL → ⟪ (ℓ "乘亝") ⟫ʷ ≈ ⟪ (ℓ "亍乘") ⟫ʷ
wp0195 c4 L = pw3 c4 L (ℓ "乘亝") (ℓ "亍乘") tt tt Eq.refl

wp0196 : Base 4 → WsL → ⟪ (ℓ "亜乘") ⟫ʷ ≈ ⟪ (ℓ "乘二") ⟫ʷ
wp0196 c4 L = pw3 c4 L (ℓ "亜乘") (ℓ "乘二") tt tt Eq.refl

wp0197 : Base 4 → WsL → ⟪ (ℓ "乘亏") ⟫ʷ ≈ ⟪ (ℓ "亞乘") ⟫ʷ
wp0197 c4 L = pw3 c4 L (ℓ "乘亏") (ℓ "亞乘") tt tt Eq.refl

wp0198 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丶争丷争丽") ⟫ʷ
wp0198 c4 L = pw1 c4 L (ℓ "亠") (ℓ "丶争丷争丽") tt tt Eq.refl

wp0199 : Base 4 → WsL → ⟪ (ℓ "亘亡") ⟫ʷ ≈ ⟪ (ℓ "亡亘亰") ⟫ʷ
wp0199 c4 L = pw1 c4 L (ℓ "亘亡") (ℓ "亡亘亰") tt tt Eq.refl

wp0200 : Base 4 → WsL → ⟪ (ℓ "乒亡") ⟫ʷ ≈ ⟪ (ℓ "亡乒井") ⟫ʷ
wp0200 c4 L = pw2 c4 L (ℓ "乒亡") (ℓ "亡乒井") tt tt Eq.refl

wp0201 : Base 4 → WsL → ⟪ (ℓ "二井亨") ⟫ʷ ≈ ⟪ (ℓ "井二") ⟫ʷ
wp0201 c4 L = pw3 c4 L (ℓ "二井亨") (ℓ "井二") tt tt Eq.refl

wp0202 : Base 4 → WsL → ⟪ (ℓ "乩亡") ⟫ʷ ≈ ⟪ (ℓ "亡乩") ⟫ʷ
wp0202 c4 L = pw1 c4 L (ℓ "乩亡") (ℓ "亡乩") tt tt Eq.refl

wp0203 : Base 4 → WsL → ⟪ (ℓ "井亡") ⟫ʷ ≈ ⟪ (ℓ "亡井") ⟫ʷ
wp0203 c4 L = pw2 c4 L (ℓ "井亡") (ℓ "亡井") tt tt Eq.refl

wp0204 : Base 4 → WsL → ⟪ (ℓ "乒井井") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wp0204 c4 L = pw2 c4 L (ℓ "乒井井") (ℓ "乒") tt tt Eq.refl

wp0205 : Base 4 → WsL → ⟪ (ℓ "二亨") ⟫ʷ ≈ ⟪ (ℓ "亨二") ⟫ʷ
wp0205 c4 L = pw3 c4 L (ℓ "二亨") (ℓ "亨二") tt tt Eq.refl

wp0206 : Base 4 → WsL → ⟪ (ℓ "五乑") ⟫ʷ ≈ ⟪ (ℓ "乑亠") ⟫ʷ
wp0206 c4 L = pw2 c4 L (ℓ "五乑") (ℓ "乑亠") tt tt Eq.refl

wp0207 : Base 4 → WsL → ⟪ (ℓ "乑亡") ⟫ʷ ≈ ⟪ (ℓ "井乑") ⟫ʷ
wp0207 c4 L = pw2 c4 L (ℓ "乑亡") (ℓ "井乑") tt tt Eq.refl

wp0208 : Base 4 → WsL → ⟪ (ℓ "亠乑") ⟫ʷ ≈ ⟪ (ℓ "乑五") ⟫ʷ
wp0208 c4 L = pw2 c4 L (ℓ "亠乑") (ℓ "乑五") tt tt Eq.refl

wp0209 : Base 4 → WsL → ⟪ (ℓ "乑亗") ⟫ʷ ≈ ⟪ (ℓ "亣乑") ⟫ʷ
wp0209 c4 L = pw2 c4 L (ℓ "乑亗") (ℓ "亣乑") tt tt Eq.refl

wp0210 : Base 4 → WsL → ⟪ (ℓ "五亖乐亖五乐") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0210 c4 L = pw2 c4 L (ℓ "五亖乐亖五乐") (ℓ "亠") tt tt Eq.refl

wp0211 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亠亢乤亢亠乤") ⟫ʷ
wp0211 c4 L = pw1 c4 L (ℓ "亜") (ℓ "亠亢乤亢亠乤") tt tt Eq.refl

wp0212 : Base 4 → WsL → ⟪ (ℓ "五亖义亖五义") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp0212 c4 L = pw3 c4 L (ℓ "五亖义亖五义") (ℓ "亜") tt tt Eq.refl

wp0213 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丯了丰了丽") ⟫ʷ
wp0213 c4 L = pw1 c4 L (ℓ "亜") (ℓ "丯了丰了丽") tt tt Eq.refl

wp0214 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "亠亣乗亣亠乗") ⟫ʷ
wp0214 c4 L = pw2 c4 L (ℓ "亐") (ℓ "亠亣乗亣亠乗") tt tt Eq.refl

wp0215 : Base 4 → WsL → ⟪ (ℓ "五丰") ⟫ʷ ≈ ⟪ (ℓ "丰五") ⟫ʷ
wp0215 c4 L = pw3 c4 L (ℓ "五丰") (ℓ "丰五") tt tt Eq.refl

wp0216 : Base 4 → WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "亜亟乻亟亜乻") ⟫ʷ
wp0216 c4 L = pw1 c4 L (ℓ "亘") (ℓ "亜亟乻亟亜乻") tt tt Eq.refl

wp0217 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亠亢乐亢亠乐") ⟫ʷ
wp0217 c4 L = pw2 c4 L (ℓ "五") (ℓ "亠亢乐亢亠乐") tt tt Eq.refl

wp0218 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亜亞义亞亜义") ⟫ʷ
wp0218 c4 L = pw3 c4 L (ℓ "五") (ℓ "亜亞义亞亜义") tt tt Eq.refl

wp0219 : Base 4 → WsL → ⟪ (ℓ "丌亠") ⟫ʷ ≈ ⟪ (ℓ "亡丌") ⟫ʷ
wp0219 c4 L = pw1 c4 L (ℓ "丌亠") (ℓ "亡丌") tt tt Eq.refl

wp0220 : Base 4 → WsL → ⟪ (ℓ "不亠") ⟫ʷ ≈ ⟪ (ℓ "亡不") ⟫ʷ
wp0220 c4 L = pw1 c4 L (ℓ "不亠") (ℓ "亡不") tt tt Eq.refl

wp0221 : Base 4 → WsL → ⟪ (ℓ "亠丬") ⟫ʷ ≈ ⟪ (ℓ "丬亠") ⟫ʷ
wp0221 c4 L = pw2 c4 L (ℓ "亠丬") (ℓ "丬亠") tt tt Eq.refl

wp0222 : Base 4 → WsL → ⟪ (ℓ "亠上") ⟫ʷ ≈ ⟪ (ℓ "上亠") ⟫ʷ
wp0222 c4 L = pw1 c4 L (ℓ "亠上") (ℓ "上亠") tt tt Eq.refl

wp0223 : Base 4 → WsL → ⟪ (ℓ "亠下") ⟫ʷ ≈ ⟪ (ℓ "下亠") ⟫ʷ
wp0223 c4 L = pw1 c4 L (ℓ "亠下") (ℓ "下亠") tt tt Eq.refl

wp0224 : Base 4 → WsL → ⟪ (ℓ "亠个") ⟫ʷ ≈ ⟪ (ℓ "个亠") ⟫ʷ
wp0224 c4 L = pw2 c4 L (ℓ "亠个") (ℓ "个亠") tt tt Eq.refl

wp0225 : Base 4 → WsL → ⟪ (ℓ "亠乄京") ⟫ʷ ≈ ⟪ (ℓ "乄亠") ⟫ʷ
wp0225 c4 L = pw2 c4 L (ℓ "亠乄京") (ℓ "乄亠") tt tt Eq.refl

wp0226 : Base 4 → WsL → ⟪ (ℓ "乄京京") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wp0226 c4 L = pw2 c4 L (ℓ "乄京京") (ℓ "乄") tt tt Eq.refl

wp0227 : Base 4 → WsL → ⟪ (ℓ "亠丱") ⟫ʷ ≈ ⟪ (ℓ "丱亠") ⟫ʷ
wp0227 c4 L = pw1 c4 L (ℓ "亠丱") (ℓ "丱亠") tt tt Eq.refl

wp0228 : Base 4 → WsL → ⟪ (ℓ "亠乜亰") ⟫ʷ ≈ ⟪ (ℓ "乜亠") ⟫ʷ
wp0228 c4 L = pw1 c4 L (ℓ "亠乜亰") (ℓ "乜亠") tt tt Eq.refl

wp0229 : Base 4 → WsL → ⟪ (ℓ "乜亰亰") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wp0229 c4 L = pw1 c4 L (ℓ "乜亰亰") (ℓ "乜") tt tt Eq.refl

wp0230 : Base 4 → WsL → ⟪ (ℓ "丶亡") ⟫ʷ ≈ ⟪ (ℓ "亡丶乹亠") ⟫ʷ
wp0230 c4 L = pw1 c4 L (ℓ "丶亡") (ℓ "亡丶乹亠") tt tt Eq.refl

wp0231 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "乹为乺为丽") ⟫ʷ
wp0231 c4 L = pw1 c4 L (ℓ "亠") (ℓ "乹为乺为丽") tt tt Eq.refl

wp0232 : Base 4 → WsL → ⟪ (ℓ "亠亡") ⟫ʷ ≈ ⟪ (ℓ "亡乻亠") ⟫ʷ
wp0232 c4 L = pw1 c4 L (ℓ "亠亡") (ℓ "亡乻亠") tt tt Eq.refl

wp0233 : Base 4 → WsL → ⟪ (ℓ "乹亡") ⟫ʷ ≈ ⟪ (ℓ "亡乹") ⟫ʷ
wp0233 c4 L = pw1 c4 L (ℓ "乹亡") (ℓ "亡乹") tt tt Eq.refl

wp0234 : Base 4 → WsL → ⟪ (ℓ "丶乹亠乹乻亠") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
wp0234 c4 L = pw1 c4 L (ℓ "丶乹亠乹乻亠") (ℓ "丶") tt tt Eq.refl

wp0235 : Base 4 → WsL → ⟪ (ℓ "丷亡") ⟫ʷ ≈ ⟪ (ℓ "亡丷乺亠") ⟫ʷ
wp0235 c4 L = pw1 c4 L (ℓ "丷亡") (ℓ "亡丷乺亠") tt tt Eq.refl

wp0236 : Base 4 → WsL → ⟪ (ℓ "乺亡") ⟫ʷ ≈ ⟪ (ℓ "亡乺") ⟫ʷ
wp0236 c4 L = pw1 c4 L (ℓ "乺亡") (ℓ "亡乺") tt tt Eq.refl

wp0237 : Base 4 → WsL → ⟪ (ℓ "丷乺亠乺乻亠") ⟫ʷ ≈ ⟪ (ℓ "丷") ⟫ʷ
wp0237 c4 L = pw1 c4 L (ℓ "丷乺亠乺乻亠") (ℓ "丷") tt tt Eq.refl

wp0238 : Base 4 → WsL → ⟪ (ℓ "丸亡") ⟫ʷ ≈ ⟪ (ℓ "亡丸乻") ⟫ʷ
wp0238 c4 L = pw1 c4 L (ℓ "丸亡") (ℓ "亡丸乻") tt tt Eq.refl

wp0239 : Base 4 → WsL → ⟪ (ℓ "乻亡") ⟫ʷ ≈ ⟪ (ℓ "亡乻") ⟫ʷ
wp0239 c4 L = pw1 c4 L (ℓ "乻亡") (ℓ "亡乻") tt tt Eq.refl

wp0240 : Base 4 → WsL → ⟪ (ℓ "丸乻乻") ⟫ʷ ≈ ⟪ (ℓ "丸") ⟫ʷ
wp0240 c4 L = pw1 c4 L (ℓ "丸乻乻") (ℓ "丸") tt tt Eq.refl

wp0241 : Base 4 → WsL → ⟪ (ℓ "乣亡") ⟫ʷ ≈ ⟪ (ℓ "亡乣") ⟫ʷ
wp0241 c4 L = pw1 c4 L (ℓ "乣亡") (ℓ "亡乣") tt tt Eq.refl

wp0242 : Base 4 → WsL → ⟪ (ℓ "买亡") ⟫ʷ ≈ ⟪ (ℓ "亡买") ⟫ʷ
wp0242 c4 L = pw1 c4 L (ℓ "买亡") (ℓ "亡买") tt tt Eq.refl

wp0243 : Base 4 → WsL → ⟪ (ℓ "丽亡") ⟫ʷ ≈ ⟪ (ℓ "亡丽乹亠") ⟫ʷ
wp0243 c4 L = pw1 c4 L (ℓ "丽亡") (ℓ "亡丽乹亠") tt tt Eq.refl

wp0244 : Base 4 → WsL → ⟪ (ℓ "丽乹亠乹乻亠") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
wp0244 c4 L = pw1 c4 L (ℓ "丽乹亠乹乻亠") (ℓ "丽") tt tt Eq.refl

wp0245 : Base 4 → WsL → ⟪ (ℓ "举亡") ⟫ʷ ≈ ⟪ (ℓ "亡举乺亠") ⟫ʷ
wp0245 c4 L = pw1 c4 L (ℓ "举亡") (ℓ "亡举乺亠") tt tt Eq.refl

wp0246 : Base 4 → WsL → ⟪ (ℓ "举乺亠乺乻亠") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp0246 c4 L = pw1 c4 L (ℓ "举乺亠乺乻亠") (ℓ "举") tt tt Eq.refl

wp0247 : Base 4 → WsL → ⟪ (ℓ "二丿") ⟫ʷ ≈ ⟪ (ℓ "丿二") ⟫ʷ
wp0247 c4 L = pw3 c4 L (ℓ "二丿") (ℓ "丿二") tt tt Eq.refl

wp0248 : Base 4 → WsL → ⟪ (ℓ "丿亡") ⟫ʷ ≈ ⟪ (ℓ "亡丿乻") ⟫ʷ
wp0248 c4 L = pw1 c4 L (ℓ "丿亡") (ℓ "亡丿乻") tt tt Eq.refl

wp0249 : Base 4 → WsL → ⟪ (ℓ "丿乻乻") ⟫ʷ ≈ ⟪ (ℓ "丿") ⟫ʷ
wp0249 c4 L = pw1 c4 L (ℓ "丿乻乻") (ℓ "丿") tt tt Eq.refl

wp0250 : Base 4 → WsL → ⟪ (ℓ "二亀亨") ⟫ʷ ≈ ⟪ (ℓ "亀二") ⟫ʷ
wp0250 c4 L = pw3 c4 L (ℓ "二亀亨") (ℓ "亀二") tt tt Eq.refl

wp0251 : Base 4 → WsL → ⟪ (ℓ "乕亡") ⟫ʷ ≈ ⟪ (ℓ "亡乕") ⟫ʷ
wp0251 c4 L = pw2 c4 L (ℓ "乕亡") (ℓ "亡乕") tt tt Eq.refl

wp0252 : Base 4 → WsL → ⟪ (ℓ "乪亡") ⟫ʷ ≈ ⟪ (ℓ "亡乪") ⟫ʷ
wp0252 c4 L = pw1 c4 L (ℓ "乪亡") (ℓ "亡乪") tt tt Eq.refl

wp0253 : Base 4 → WsL → ⟪ (ℓ "亀亡") ⟫ʷ ≈ ⟪ (ℓ "亡亀") ⟫ʷ
wp0253 c4 L = pw1 c4 L (ℓ "亀亡") (ℓ "亡亀") tt tt Eq.refl

wp0254 : Base 4 → WsL → ⟪ (ℓ "亀亨亨") ⟫ʷ ≈ ⟪ (ℓ "亀") ⟫ʷ
wp0254 c4 L = pw3 c4 L (ℓ "亀亨亨") (ℓ "亀") tt tt Eq.refl

wp0255 : Base 4 → WsL → ⟪ (ℓ "亁") ⟫ʷ ≈ ⟪ (ℓ "举不举丌举") ⟫ʷ
wp0255 c4 L = pw1 c4 L (ℓ "亁") (ℓ "举不举丌举") tt tt Eq.refl

wp0256 : Base 4 → WsL → ⟪ (ℓ "亂") ⟫ʷ ≈ ⟪ (ℓ "丽不丽丌丽") ⟫ʷ
wp0256 c4 L = pw1 c4 L (ℓ "亂") (ℓ "丽不丽丌丽") tt tt Eq.refl

wp0257 : Base 4 → WsL → ⟪ (ℓ "上举") ⟫ʷ ≈ ⟪ (ℓ "並丽並") ⟫ʷ
wp0257 c4 L = pw1 c4 L (ℓ "上举") (ℓ "並丽並") tt tt Eq.refl

wp0258 : Base 4 → WsL → ⟪ (ℓ "下丽") ⟫ʷ ≈ ⟪ (ℓ "並举並") ⟫ʷ
wp0258 c4 L = pw1 c4 L (ℓ "下丽") (ℓ "並举並") tt tt Eq.refl

wp0259 : Base 4 → WsL → ⟪ (ℓ "丌亂") ⟫ʷ ≈ ⟪ (ℓ "並亁並") ⟫ʷ
wp0259 c4 L = pw1 c4 L (ℓ "丌亂") (ℓ "並亁並") tt tt Eq.refl
