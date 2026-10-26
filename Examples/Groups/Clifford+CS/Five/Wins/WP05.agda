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

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp0919 : Base 4 → WsL → ⟪ (ℓ "亨丨") ⟫ʷ ≈ ⟪ (ℓ "丨亨") ⟫ʷ
wp0919 c4 L = pw3 c4 L (ℓ "亨丨") (ℓ "丨亨") tt tt Eq.refl

wp0920 : Base 4 → WsL → ⟪ (ℓ "亘争亜") ⟫ʷ ≈ ⟪ (ℓ "争亘") ⟫ʷ
wp0920 c4 L = pw1 c4 L (ℓ "亘争亜") (ℓ "争亘") tt tt Eq.refl

wp0921 : Base 4 → WsL → ⟪ (ℓ "亜亪") ⟫ʷ ≈ ⟪ (ℓ "亪亜五") ⟫ʷ
wp0921 c4 L = pw3 c4 L (ℓ "亜亪") (ℓ "亪亜五") tt tt Eq.refl

wp0922 : Base 4 → WsL → ⟪ (ℓ "争亜亜") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wp0922 c4 L = pw1 c4 L (ℓ "争亜亜") (ℓ "争") tt tt Eq.refl

wp0923 : Base 4 → WsL → ⟪ (ℓ "丨亪") ⟫ʷ ≈ ⟪ (ℓ "亪丨") ⟫ʷ
wp0923 c4 L = pw3 c4 L (ℓ "丨亪") (ℓ "亪丨") tt tt Eq.refl

wp0924 : Base 4 → WsL → ⟪ (ℓ "五亐五亐五") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp0924 c4 L = pw2 c4 L (ℓ "五亐五亐五") (ℓ "五") tt tt Eq.refl

wp0925 : Base 4 → WsL → ⟪ (ℓ "亐亁亐亐") ⟫ʷ ≈ ⟪ (ℓ "亐亁") ⟫ʷ
wp0925 c4 L = pw2 c4 L (ℓ "亐亁亐亐") (ℓ "亐亁") tt tt Eq.refl

wp0926 : Base 4 → WsL → ⟪ (ℓ "亜丌") ⟫ʷ ≈ ⟪ (ℓ "丌亝亜亜") ⟫ʷ
wp0926 c4 L = pw1 c4 L (ℓ "亜丌") (ℓ "丌亝亜亜") tt tt Eq.refl

wp0927 : Base 4 → WsL → ⟪ (ℓ "亜亁") ⟫ʷ ≈ ⟪ (ℓ "丱亁丱亜") ⟫ʷ
wp0927 c4 L = pw3 c4 L (ℓ "亜亁") (ℓ "丱亁丱亜") tt tt Eq.refl

wp0928 : Base 4 → WsL → ⟪ (ℓ "丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亝亜丱亁丱丢") ⟫ʷ
wp0928 c4 L = pw3 c4 L (ℓ "丌亁丢") (ℓ "丌亝亜丱亁丱丢") tt tt Eq.refl

wp0929 : Base 4 → WsL → ⟪ (ℓ "亐亁亐並") ⟫ʷ ≈ ⟪ (ℓ "並亐丌亁丢亐") ⟫ʷ
wp0929 c4 L = pw2 c4 L (ℓ "亐亁亐並") (ℓ "並亐丌亁丢亐") tt tt Eq.refl

wp0930 : Base 4 → WsL → ⟪ (ℓ "亐丽丽") ⟫ʷ ≈ ⟪ (ℓ "丽丽亐") ⟫ʷ
wp0930 c4 L = pw2 c4 L (ℓ "亐丽丽") (ℓ "丽丽亐") tt tt Eq.refl

wp0931 : Base 4 → WsL → ⟪ (ℓ "亁丽丽亁丢") ⟫ʷ ≈ ⟪ (ℓ "亀") ⟫ʷ
wp0931 c4 L = pw1 c4 L (ℓ "亁丽丽亁丢") (ℓ "亀") tt tt Eq.refl

wp0932 : Base 4 → WsL → ⟪ (ℓ "亀亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶五亮丷亐亁丽丽亁亐丢乕") ⟫ʷ
wp0932 c4 L = pw2 c4 L (ℓ "亀亮丶亮丷") (ℓ "亮丶五亮丷亐亁丽丽亁亐丢乕") tt tt Eq.refl

wp0933 : Base 4 → WsL → ⟪ (ℓ "五丒") ⟫ʷ ≈ ⟪ (ℓ "丒亖五五") ⟫ʷ
wp0933 c4 L = pw2 c4 L (ℓ "五丒") (ℓ "丒亖五五") tt tt Eq.refl

wp0934 : Base 4 → WsL → ⟪ (ℓ "五亄") ⟫ʷ ≈ ⟪ (ℓ "个亄个五") ⟫ʷ
wp0934 c4 L = pw2 c4 L (ℓ "五亄") (ℓ "个亄个五") tt tt Eq.refl

wp0935 : Base 4 → WsL → ⟪ (ℓ "丒亄丢") ⟫ʷ ≈ ⟪ (ℓ "丒亖五个亄个丢") ⟫ʷ
wp0935 c4 L = pw2 c4 L (ℓ "丒亄丢") (ℓ "丒亖五个亄个丢") tt tt Eq.refl

wp0936 : Base 4 → WsL → ⟪ (ℓ "亜丘") ⟫ʷ ≈ ⟪ (ℓ "丘亞亜亜") ⟫ʷ
wp0936 c4 L = pw1 c4 L (ℓ "亜丘") (ℓ "丘亞亜亜") tt tt Eq.refl

wp0937 : Base 4 → WsL → ⟪ (ℓ "亜亇") ⟫ʷ ≈ ⟪ (ℓ "丱亇丱亜") ⟫ʷ
wp0937 c4 L = pw1 c4 L (ℓ "亜亇") (ℓ "丱亇丱亜") tt tt Eq.refl

wp0938 : Base 4 → WsL → ⟪ (ℓ "丘亇丢") ⟫ʷ ≈ ⟪ (ℓ "丘亞亜丱亇丱丢") ⟫ʷ
wp0938 c4 L = pw1 c4 L (ℓ "丘亇丢") (ℓ "丘亞亜丱亇丱丢") tt tt Eq.refl

wp0939 : Base 4 → WsL → ⟪ (ℓ "乽亚") ⟫ʷ ≈ ⟪ (ℓ "亚乽") ⟫ʷ
wp0939 c4 L = pw1 c4 L (ℓ "乽亚") (ℓ "亚乽") tt tt Eq.refl

wp0940 : Base 4 → WsL → ⟪ (ℓ "争亚") ⟫ʷ ≈ ⟪ (ℓ "亚争亞") ⟫ʷ
wp0940 c4 L = pw1 c4 L (ℓ "争亚") (ℓ "亚争亞") tt tt Eq.refl

wp0941 : Base 4 → WsL → ⟪ (ℓ "亨亞五") ⟫ʷ ≈ ⟪ (ℓ "亞亨") ⟫ʷ
wp0941 c4 L = pw3 c4 L (ℓ "亨亞五") (ℓ "亞亨") tt tt Eq.refl

wp0942 : Base 4 → WsL → ⟪ (ℓ "乁亚") ⟫ʷ ≈ ⟪ (ℓ "亚乁") ⟫ʷ
wp0942 c4 L = pw1 c4 L (ℓ "乁亚") (ℓ "亚乁") tt tt Eq.refl

wp0943 : Base 4 → WsL → ⟪ (ℓ "亚亞") ⟫ʷ ≈ ⟪ (ℓ "亞亚") ⟫ʷ
wp0943 c4 L = pw1 c4 L (ℓ "亚亞") (ℓ "亞亚") tt tt Eq.refl

wp0944 : Base 4 → WsL → ⟪ (ℓ "争亞亞") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wp0944 c4 L = pw1 c4 L (ℓ "争亞亞") (ℓ "争") tt tt Eq.refl

wp0945 : Base 4 → WsL → ⟪ (ℓ "争亞") ⟫ʷ ≈ ⟪ (ℓ "亞争") ⟫ʷ
wp0945 c4 L = pw1 c4 L (ℓ "争亞") (ℓ "亞争") tt tt Eq.refl

wp0946 : Base 4 → WsL → ⟪ (ℓ "亨亞") ⟫ʷ ≈ ⟪ (ℓ "亞亨五") ⟫ʷ
wp0946 c4 L = pw3 c4 L (ℓ "亨亞") (ℓ "亞亨五") tt tt Eq.refl

wp0947 : Base 4 → WsL → ⟪ (ℓ "乽亞") ⟫ʷ ≈ ⟪ (ℓ "亞乽亚") ⟫ʷ
wp0947 c4 L = pw1 c4 L (ℓ "乽亞") (ℓ "亞乽亚") tt tt Eq.refl

wp0948 : Base 4 → WsL → ⟪ (ℓ "丨亞") ⟫ʷ ≈ ⟪ (ℓ "亞丨") ⟫ʷ
wp0948 c4 L = pw3 c4 L (ℓ "丨亞") (ℓ "亞丨") tt tt Eq.refl

wp0949 : Base 4 → WsL → ⟪ (ℓ "为亞") ⟫ʷ ≈ ⟪ (ℓ "亞为") ⟫ʷ
wp0949 c4 L = pw1 c4 L (ℓ "为亞") (ℓ "亞为") tt tt Eq.refl

wp0950 : Base 4 → WsL → ⟪ (ℓ "乽亚亚") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wp0950 c4 L = pw1 c4 L (ℓ "乽亚亚") (ℓ "乽") tt tt Eq.refl

wp0951 : Base 4 → WsL → ⟪ (ℓ "亐亄亐亐") ⟫ʷ ≈ ⟪ (ℓ "亐亄") ⟫ʷ
wp0951 c4 L = pw2 c4 L (ℓ "亐亄亐亐") (ℓ "亐亄") tt tt Eq.refl

wp0952 : Base 4 → WsL → ⟪ (ℓ "亐亄亐並") ⟫ʷ ≈ ⟪ (ℓ "並亐丒亄丢亐") ⟫ʷ
wp0952 c4 L = pw2 c4 L (ℓ "亐亄亐並") (ℓ "並亐丒亄丢亐") tt tt Eq.refl

wp0953 : Base 4 → WsL → ⟪ (ℓ "亐乕乕") ⟫ʷ ≈ ⟪ (ℓ "乕乕亐") ⟫ʷ
wp0953 c4 L = pw2 c4 L (ℓ "亐乕乕") (ℓ "乕乕亐") tt tt Eq.refl

wp0954 : Base 4 → WsL → ⟪ (ℓ "亃亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶五亮丷亐亄乕乕亄亐丢丽") ⟫ʷ
wp0954 c4 L = pw2 c4 L (ℓ "亃亮丶亮丷") (ℓ "亮丶五亮丷亐亄乕乕亄亐丢丽") tt tt Eq.refl

wp0955 : Base 4 → WsL → ⟪ (ℓ "争云") ⟫ʷ ≈ ⟪ (ℓ "云争井") ⟫ʷ
wp0955 c4 L = pw2 c4 L (ℓ "争云") (ℓ "云争井") tt tt Eq.refl

wp0956 : Base 4 → WsL → ⟪ (ℓ "争井井") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wp0956 c4 L = pw2 c4 L (ℓ "争井井") (ℓ "争") tt tt Eq.refl

wp0957 : Base 4 → WsL → ⟪ (ℓ "乼云") ⟫ʷ ≈ ⟪ (ℓ "井乼") ⟫ʷ
wp0957 c4 L = pw2 c4 L (ℓ "乼云") (ℓ "井乼") tt tt Eq.refl

wp0958 : Base 4 → WsL → ⟪ (ℓ "亐乼") ⟫ʷ ≈ ⟪ (ℓ "乼五") ⟫ʷ
wp0958 c4 L = pw2 c4 L (ℓ "亐乼") (ℓ "乼五") tt tt Eq.refl

wp0959 : Base 4 → WsL → ⟪ (ℓ "乼亖") ⟫ʷ ≈ ⟪ (ℓ "互乼") ⟫ʷ
wp0959 c4 L = pw2 c4 L (ℓ "乼亖") (ℓ "互乼") tt tt Eq.refl

wp0960 : Base 4 → WsL → ⟪ (ℓ "争井") ⟫ʷ ≈ ⟪ (ℓ "井争") ⟫ʷ
wp0960 c4 L = pw2 c4 L (ℓ "争井") (ℓ "井争") tt tt Eq.refl

wp0961 : Base 4 → WsL → ⟪ (ℓ "乽井") ⟫ʷ ≈ ⟪ (ℓ "井乽云") ⟫ʷ
wp0961 c4 L = pw2 c4 L (ℓ "乽井") (ℓ "井乽云") tt tt Eq.refl

wp0962 : Base 4 → WsL → ⟪ (ℓ "乇井") ⟫ʷ ≈ ⟪ (ℓ "井乇") ⟫ʷ
wp0962 c4 L = pw3 c4 L (ℓ "乇井") (ℓ "井乇") tt tt Eq.refl

wp0963 : Base 4 → WsL → ⟪ (ℓ "乒井") ⟫ʷ ≈ ⟪ (ℓ "井乒") ⟫ʷ
wp0963 c4 L = pw2 c4 L (ℓ "乒井") (ℓ "井乒") tt tt Eq.refl

wp0964 : Base 4 → WsL → ⟪ (ℓ "乽云云") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wp0964 c4 L = pw2 c4 L (ℓ "乽云云") (ℓ "乽") tt tt Eq.refl

wp0965 : Base 4 → WsL → ⟪ (ℓ "乼井") ⟫ʷ ≈ ⟪ (ℓ "云乼") ⟫ʷ
wp0965 c4 L = pw2 c4 L (ℓ "乼井") (ℓ "云乼") tt tt Eq.refl

wp0966 : Base 4 → WsL → ⟪ (ℓ "乼互") ⟫ʷ ≈ ⟪ (ℓ "亖乼") ⟫ʷ
wp0966 c4 L = pw2 c4 L (ℓ "乼互") (ℓ "亖乼") tt tt Eq.refl

wp0967 : Base 4 → WsL → ⟪ (ℓ "亘亝") ⟫ʷ ≈ ⟪ (ℓ "亝亘亰") ⟫ʷ
wp0967 c4 L = pw1 c4 L (ℓ "亘亝") (ℓ "亝亘亰") tt tt Eq.refl

wp0968 : Base 4 → WsL → ⟪ (ℓ "之亝") ⟫ʷ ≈ ⟪ (ℓ "亝之井") ⟫ʷ
wp0968 c4 L = pw3 c4 L (ℓ "之亝") (ℓ "亝之井") tt tt Eq.refl

wp0969 : Base 4 → WsL → ⟪ (ℓ "亐井京") ⟫ʷ ≈ ⟪ (ℓ "井亐") ⟫ʷ
wp0969 c4 L = pw2 c4 L (ℓ "亐井京") (ℓ "井亐") tt tt Eq.refl

wp0970 : Base 4 → WsL → ⟪ (ℓ "乹亝") ⟫ʷ ≈ ⟪ (ℓ "亝乹") ⟫ʷ
wp0970 c4 L = pw1 c4 L (ℓ "乹亝") (ℓ "亝乹") tt tt Eq.refl

wp0971 : Base 4 → WsL → ⟪ (ℓ "之井井") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wp0971 c4 L = pw3 c4 L (ℓ "之井井") (ℓ "之") tt tt Eq.refl

wp0972 : Base 4 → WsL → ⟪ (ℓ "乊亝") ⟫ʷ ≈ ⟪ (ℓ "井乊") ⟫ʷ
wp0972 c4 L = pw3 c4 L (ℓ "乊亝") (ℓ "井乊") tt tt Eq.refl

wp0973 : Base 4 → WsL → ⟪ (ℓ "乊亗") ⟫ʷ ≈ ⟪ (ℓ "亟乊") ⟫ʷ
wp0973 c4 L = pw3 c4 L (ℓ "乊亗") (ℓ "亟乊") tt tt Eq.refl

wp0974 : Base 4 → WsL → ⟪ (ℓ "乙亍") ⟫ʷ ≈ ⟪ (ℓ "亍乙") ⟫ʷ
wp0974 c4 L = pw3 c4 L (ℓ "乙亍") (ℓ "亍乙") tt tt Eq.refl

wp0975 : Base 4 → WsL → ⟪ (ℓ "亃亍") ⟫ʷ ≈ ⟪ (ℓ "亍亃亝") ⟫ʷ
wp0975 c4 L = pw3 c4 L (ℓ "亃亍") (ℓ "亍亃亝") tt tt Eq.refl

wp0976 : Base 4 → WsL → ⟪ (ℓ "亠亝亰") ⟫ʷ ≈ ⟪ (ℓ "亝亠") ⟫ʷ
wp0976 c4 L = pw1 c4 L (ℓ "亠亝亰") (ℓ "亝亠") tt tt Eq.refl

wp0977 : Base 4 → WsL → ⟪ (ℓ "乭亍") ⟫ʷ ≈ ⟪ (ℓ "亍乭") ⟫ʷ
wp0977 c4 L = pw3 c4 L (ℓ "乭亍") (ℓ "亍乭") tt tt Eq.refl

wp0978 : Base 4 → WsL → ⟪ (ℓ "亃亝亝") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wp0978 c4 L = pw3 c4 L (ℓ "亃亝亝") (ℓ "亃") tt tt Eq.refl

wp0979 : Base 4 → WsL → ⟪ (ℓ "亠丞") ⟫ʷ ≈ ⟪ (ℓ "丞亢亠亠") ⟫ʷ
wp0979 c4 L = pw1 c4 L (ℓ "亠丞") (ℓ "丞亢亠亠") tt tt Eq.refl

wp0980 : Base 4 → WsL → ⟪ (ℓ "亠亊") ⟫ʷ ≈ ⟪ (ℓ "丸亊丸亠") ⟫ʷ
wp0980 c4 L = pw1 c4 L (ℓ "亠亊") (ℓ "丸亊丸亠") tt tt Eq.refl

wp0981 : Base 4 → WsL → ⟪ (ℓ "亠丢") ⟫ʷ ≈ ⟪ (ℓ "丢亠") ⟫ʷ
wp0981 c4 L = pw1 c4 L (ℓ "亠丢") (ℓ "丢亠") tt tt Eq.refl

wp0982 : Base 4 → WsL → ⟪ (ℓ "丞亊丢") ⟫ʷ ≈ ⟪ (ℓ "丞亢亠丸亊丸丢") ⟫ʷ
wp0982 c4 L = pw1 c4 L (ℓ "丞亊丢") (ℓ "丞亢亠丸亊丸丢") tt tt Eq.refl

wp0983 : Base 4 → WsL → ⟪ (ℓ "书亡") ⟫ʷ ≈ ⟪ (ℓ "亡书亝") ⟫ʷ
wp0983 c4 L = pw1 c4 L (ℓ "书亡") (ℓ "亡书亝") tt tt Eq.refl

wp0984 : Base 4 → WsL → ⟪ (ℓ "二亝亨") ⟫ʷ ≈ ⟪ (ℓ "亝二") ⟫ʷ
wp0984 c4 L = pw3 c4 L (ℓ "二亝亨") (ℓ "亝二") tt tt Eq.refl

wp0985 : Base 4 → WsL → ⟪ (ℓ "书亝亝") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
wp0985 c4 L = pw1 c4 L (ℓ "书亝亝") (ℓ "书") tt tt Eq.refl

wp0986 : Base 4 → WsL → ⟪ (ℓ "乥亡") ⟫ʷ ≈ ⟪ (ℓ "亝乥") ⟫ʷ
wp0986 c4 L = pw1 c4 L (ℓ "乥亡") (ℓ "亝乥") tt tt Eq.refl

wp0987 : Base 4 → WsL → ⟪ (ℓ "乥亟") ⟫ʷ ≈ ⟪ (ℓ "亣乥") ⟫ʷ
wp0987 c4 L = pw1 c4 L (ℓ "乥亟") (ℓ "亣乥") tt tt Eq.refl

wp0988 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "京亯丿亯京丿") ⟫ʷ
wp0988 c4 L = pw2 c4 L (ℓ "亐") (ℓ "京亯丿亯京丿") tt tt Eq.refl

wp0989 : Base 4 → WsL → ⟪ (ℓ "亘亲") ⟫ʷ ≈ ⟪ (ℓ "亲亘亜") ⟫ʷ
wp0989 c4 L = pw1 c4 L (ℓ "亘亲") (ℓ "亲亘亜") tt tt Eq.refl

wp0990 : Base 4 → WsL → ⟪ (ℓ "亐亮五") ⟫ʷ ≈ ⟪ (ℓ "亮亐") ⟫ʷ
wp0990 c4 L = pw2 c4 L (ℓ "亐亮五") (ℓ "亮亐") tt tt Eq.refl

wp0991 : Base 4 → WsL → ⟪ (ℓ "亜五亜五亜") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp0991 c4 L = pw3 c4 L (ℓ "亜五亜五亜") (ℓ "亜") tt tt Eq.refl

wp0992 : Base 4 → WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "亰亳丿亳亰丿") ⟫ʷ
wp0992 c4 L = pw1 c4 L (ℓ "亘") (ℓ "亰亳丿亳亰丿") tt tt Eq.refl

wp0993 : Base 4 → WsL → ⟪ (ℓ "亘亝") ⟫ʷ ≈ ⟪ (ℓ "亝亰亘") ⟫ʷ
wp0993 c4 L = pw1 c4 L (ℓ "亘亝") (ℓ "亝亰亘") tt tt Eq.refl

wp0994 : Base 4 → WsL → ⟪ (ℓ "亰亘亝") ⟫ʷ ≈ ⟪ (ℓ "亝亘") ⟫ʷ
wp0994 c4 L = pw1 c4 L (ℓ "亰亘亝") (ℓ "亝亘") tt tt Eq.refl

wp0995 : Base 4 → WsL → ⟪ (ℓ "乖亝") ⟫ʷ ≈ ⟪ (ℓ "亝乖") ⟫ʷ
wp0995 c4 L = pw3 c4 L (ℓ "乖亝") (ℓ "亝乖") tt tt Eq.refl

wp0996 : Base 4 → WsL → ⟪ (ℓ "五亨五") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp0996 c4 L = pw3 c4 L (ℓ "五亨五") (ℓ "亨") tt tt Eq.refl

wp0997 : Base 4 → WsL → ⟪ (ℓ "亐亮") ⟫ʷ ≈ ⟪ (ℓ "亮亐五") ⟫ʷ
wp0997 c4 L = pw2 c4 L (ℓ "亐亮") (ℓ "亮亐五") tt tt Eq.refl

wp0998 : Base 4 → WsL → ⟪ (ℓ "丽亮") ⟫ʷ ≈ ⟪ (ℓ "亮丽") ⟫ʷ
wp0998 c4 L = pw2 c4 L (ℓ "丽亮") (ℓ "亮丽") tt tt Eq.refl

wp0999 : Base 4 → WsL → ⟪ (ℓ "为亝") ⟫ʷ ≈ ⟪ (ℓ "亝亲为") ⟫ʷ
wp0999 c4 L = pw1 c4 L (ℓ "为亝") (ℓ "亝亲为") tt tt Eq.refl

wp1000 : Base 4 → WsL → ⟪ (ℓ "亨个") ⟫ʷ ≈ ⟪ (ℓ "个亨") ⟫ʷ
wp1000 c4 L = pw3 c4 L (ℓ "亨个") (ℓ "个亨") tt tt Eq.refl

wp1001 : Base 4 → WsL → ⟪ (ℓ "亝亲") ⟫ʷ ≈ ⟪ (ℓ "亲亝") ⟫ʷ
wp1001 c4 L = pw1 c4 L (ℓ "亝亲") (ℓ "亲亝") tt tt Eq.refl

wp1002 : Base 4 → WsL → ⟪ (ℓ "丌丯了丰了丽不") ⟫ʷ ≈ ⟪ (ℓ "亝") ⟫ʷ
wp1002 c4 L = pw1 c4 L (ℓ "丌丯了丰了丽不") (ℓ "亝") tt tt Eq.refl

wp1003 : Base 4 → WsL → ⟪ (ℓ "京丽") ⟫ʷ ≈ ⟪ (ℓ "丽京") ⟫ʷ
wp1003 c4 L = pw2 c4 L (ℓ "京丽") (ℓ "丽京") tt tt Eq.refl

wp1004 : Base 4 → WsL → ⟪ (ℓ "亝些") ⟫ʷ ≈ ⟪ (ℓ "些亝亲") ⟫ʷ
wp1004 c4 L = pw1 c4 L (ℓ "亝些") (ℓ "些亝亲") tt tt Eq.refl

wp1005 : Base 4 → WsL → ⟪ (ℓ "乪些") ⟫ʷ ≈ ⟪ (ℓ "些乪") ⟫ʷ
wp1005 c4 L = pw1 c4 L (ℓ "乪些") (ℓ "些乪") tt tt Eq.refl

wp1006 : Base 4 → WsL → ⟪ (ℓ "乩些") ⟫ʷ ≈ ⟪ (ℓ "些乩") ⟫ʷ
wp1006 c4 L = pw1 c4 L (ℓ "乩些") (ℓ "些乩") tt tt Eq.refl

wp1007 : Base 4 → WsL → ⟪ (ℓ "些亲") ⟫ʷ ≈ ⟪ (ℓ "亲些") ⟫ʷ
wp1007 c4 L = pw1 c4 L (ℓ "些亲") (ℓ "亲些") tt tt Eq.refl

wp1008 : Base 4 → WsL → ⟪ (ℓ "亝亲亲") ⟫ʷ ≈ ⟪ (ℓ "亝") ⟫ʷ
wp1008 c4 L = pw1 c4 L (ℓ "亝亲亲") (ℓ "亝") tt tt Eq.refl

wp1009 : Base 4 → WsL → ⟪ (ℓ "为亲") ⟫ʷ ≈ ⟪ (ℓ "亲为") ⟫ʷ
wp1009 c4 L = pw1 c4 L (ℓ "为亲") (ℓ "亲为") tt tt Eq.refl

wp1010 : Base 4 → WsL → ⟪ (ℓ "五买京") ⟫ʷ ≈ ⟪ (ℓ "买五") ⟫ʷ
wp1010 c4 L = pw2 c4 L (ℓ "五买京") (ℓ "买五") tt tt Eq.refl

wp1011 : Base 4 → WsL → ⟪ (ℓ "买京京") ⟫ʷ ≈ ⟪ (ℓ "买") ⟫ʷ
wp1011 c4 L = pw2 c4 L (ℓ "买京京") (ℓ "买") tt tt Eq.refl

wp1012 : Base 4 → WsL → ⟪ (ℓ "买亲") ⟫ʷ ≈ ⟪ (ℓ "亲买亝") ⟫ʷ
wp1012 c4 L = pw1 c4 L (ℓ "买亲") (ℓ "亲买亝") tt tt Eq.refl

wp1013 : Base 4 → WsL → ⟪ (ℓ "买亝亲") ⟫ʷ ≈ ⟪ (ℓ "亲买") ⟫ʷ
wp1013 c4 L = pw1 c4 L (ℓ "买亝亲") (ℓ "亲买") tt tt Eq.refl

wp1014 : Base 4 → WsL → ⟪ (ℓ "京丹") ⟫ʷ ≈ ⟪ (ℓ "丹五") ⟫ʷ
wp1014 c4 L = pw2 c4 L (ℓ "京丹") (ℓ "丹五") tt tt Eq.refl

wp1015 : Base 4 → WsL → ⟪ (ℓ "丹井") ⟫ʷ ≈ ⟪ (ℓ "亮丹") ⟫ʷ
wp1015 c4 L = pw2 c4 L (ℓ "丹井") (ℓ "亮丹") tt tt Eq.refl

wp1016 : Base 4 → WsL → ⟪ (ℓ "丹亲") ⟫ʷ ≈ ⟪ (ℓ "亝丹") ⟫ʷ
wp1016 c4 L = pw1 c4 L (ℓ "丹亲") (ℓ "亝丹") tt tt Eq.refl

wp1017 : Base 4 → WsL → ⟪ (ℓ "亠乭亘") ⟫ʷ ≈ ⟪ (ℓ "乭亠") ⟫ʷ
wp1017 c4 L = pw1 c4 L (ℓ "亠乭亘") (ℓ "乭亠") tt tt Eq.refl

wp1018 : Base 4 → WsL → ⟪ (ℓ "乭亘亘") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wp1018 c4 L = pw1 c4 L (ℓ "乭亘亘") (ℓ "乭") tt tt Eq.refl

wp1019 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "乭二乭") ⟫ʷ
wp1019 c4 L = pw3 c4 L (ℓ "二") (ℓ "乭二乭") tt tt Eq.refl

wp1020 : Base 4 → WsL → ⟪ (ℓ "亠了") ⟫ʷ ≈ ⟪ (ℓ "了亠") ⟫ʷ
wp1020 c4 L = pw1 c4 L (ℓ "亠了") (ℓ "了亠") tt tt Eq.refl

wp1021 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "了五了") ⟫ʷ
wp1021 c4 L = pw3 c4 L (ℓ "五") (ℓ "了五了") tt tt Eq.refl

wp1022 : Base 4 → WsL → ⟪ (ℓ "二了") ⟫ʷ ≈ ⟪ (ℓ "了五二") ⟫ʷ
wp1022 c4 L = pw3 c4 L (ℓ "二了") (ℓ "了五二") tt tt Eq.refl

wp1023 : Base 4 → WsL → ⟪ (ℓ "五乭") ⟫ʷ ≈ ⟪ (ℓ "乭二五") ⟫ʷ
wp1023 c4 L = pw3 c4 L (ℓ "五乭") (ℓ "乭二五") tt tt Eq.refl

wp1024 : Base 4 → WsL → ⟪ (ℓ "二五二五二") ⟫ʷ ≈ ⟪ (ℓ "二") ⟫ʷ
wp1024 c4 L = pw3 c4 L (ℓ "二五二五二") (ℓ "二") tt tt Eq.refl

wp1025 : Base 4 → WsL → ⟪ (ℓ "亝亲些") ⟫ʷ ≈ ⟪ (ℓ "些亝") ⟫ʷ
wp1025 c4 L = pw1 c4 L (ℓ "亝亲些") (ℓ "些亝") tt tt Eq.refl

wp1026 : Base 4 → WsL → ⟪ (ℓ "丌乩丳乪丳丽不") ⟫ʷ ≈ ⟪ (ℓ "亝") ⟫ʷ
wp1026 c4 L = pw1 c4 L (ℓ "丌乩丳乪丳丽不") (ℓ "亝") tt tt Eq.refl

wp1027 : Base 4 → WsL → ⟪ (ℓ "京丩") ⟫ʷ ≈ ⟪ (ℓ "丩京") ⟫ʷ
wp1027 c4 L = pw2 c4 L (ℓ "京丩") (ℓ "丩京") tt tt Eq.refl

wp1028 : Base 4 → WsL → ⟪ (ℓ "丌乩乁乪乁丯不") ⟫ʷ ≈ ⟪ (ℓ "亝") ⟫ʷ
wp1028 c4 L = pw1 c4 L (ℓ "丌乩乁乪乁丯不") (ℓ "亝") tt tt Eq.refl

wp1029 : Base 4 → WsL → ⟪ (ℓ "亠亝") ⟫ʷ ≈ ⟪ (ℓ "亝亰亠") ⟫ʷ
wp1029 c4 L = pw1 c4 L (ℓ "亠亝") (ℓ "亝亰亠") tt tt Eq.refl

wp1030 : Base 4 → WsL → ⟪ (ℓ "五丯亪") ⟫ʷ ≈ ⟪ (ℓ "丯亪五") ⟫ʷ
wp1030 c4 L = pw3 c4 L (ℓ "五丯亪") (ℓ "丯亪五") tt tt Eq.refl

wp1031 : Base 4 → WsL → ⟪ (ℓ "亠亮") ⟫ʷ ≈ ⟪ (ℓ "亮亠五") ⟫ʷ
wp1031 c4 L = pw2 c4 L (ℓ "亠亮") (ℓ "亮亠五") tt tt Eq.refl

wp1032 : Base 4 → WsL → ⟪ (ℓ "五二五二五") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp1032 c4 L = pw3 c4 L (ℓ "五二五二五") (ℓ "五") tt tt Eq.refl

wp1033 : Base 4 → WsL → ⟪ (ℓ "亠亢丿") ⟫ʷ ≈ ⟪ (ℓ "亢亠") ⟫ʷ
wp1033 c4 L = pw1 c4 L (ℓ "亠亢丿") (ℓ "亢亠") tt tt Eq.refl

wp1034 : Base 4 → WsL → ⟪ (ℓ "亠亢") ⟫ʷ ≈ ⟪ (ℓ "亢丿亠") ⟫ʷ
wp1034 c4 L = pw1 c4 L (ℓ "亠亢") (ℓ "亢丿亠") tt tt Eq.refl

wp1035 : Base 4 → WsL → ⟪ (ℓ "丘亢") ⟫ʷ ≈ ⟪ (ℓ "亢丘") ⟫ʷ
wp1035 c4 L = pw1 c4 L (ℓ "丘亢") (ℓ "亢丘") tt tt Eq.refl

wp1036 : Base 4 → WsL → ⟪ (ℓ "乪亢") ⟫ʷ ≈ ⟪ (ℓ "亢乪") ⟫ʷ
wp1036 c4 L = pw1 c4 L (ℓ "乪亢") (ℓ "亢乪") tt tt Eq.refl

wp1037 : Base 4 → WsL → ⟪ (ℓ "乕亢") ⟫ʷ ≈ ⟪ (ℓ "亢乕") ⟫ʷ
wp1037 c4 L = pw2 c4 L (ℓ "乕亢") (ℓ "亢乕") tt tt Eq.refl

wp1038 : Base 4 → WsL → ⟪ (ℓ "丙亢") ⟫ʷ ≈ ⟪ (ℓ "亢丙") ⟫ʷ
wp1038 c4 L = pw1 c4 L (ℓ "丙亢") (ℓ "亢丙") tt tt Eq.refl

wp1039 : Base 4 → WsL → ⟪ (ℓ "五京亢") ⟫ʷ ≈ ⟪ (ℓ "亢京") ⟫ʷ
wp1039 c4 L = pw2 c4 L (ℓ "五京亢") (ℓ "亢京") tt tt Eq.refl

wp1040 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "京五京") ⟫ʷ
wp1040 c4 L = pw2 c4 L (ℓ "五") (ℓ "京五京") tt tt Eq.refl

wp1041 : Base 4 → WsL → ⟪ (ℓ "丽些") ⟫ʷ ≈ ⟪ (ℓ "些丽") ⟫ʷ
wp1041 c4 L = pw1 c4 L (ℓ "丽些") (ℓ "些丽") tt tt Eq.refl

wp1042 : Base 4 → WsL → ⟪ (ℓ "亨丨亝") ⟫ʷ ≈ ⟪ (ℓ "丨亝亨") ⟫ʷ
wp1042 c4 L = pw3 c4 L (ℓ "亨丨亝") (ℓ "丨亝亨") tt tt Eq.refl

wp1043 : Base 4 → WsL → ⟪ (ℓ "亝丨亝丩亪丯亪丰") ⟫ʷ ≈ ⟪ (ℓ "亪丯亪丰亝丨亝丩") ⟫ʷ
wp1043 c4 L = pw3 c4 L (ℓ "亝丨亝丩亪丯亪丰") (ℓ "亪丯亪丰亝丨亝丩") tt tt Eq.refl

wp1044 : Base 4 → WsL → ⟪ (ℓ "五亭") ⟫ʷ ≈ ⟪ (ℓ "亭亠五") ⟫ʷ
wp1044 c4 L = pw2 c4 L (ℓ "五亭") (ℓ "亭亠五") tt tt Eq.refl

wp1045 : Base 4 → WsL → ⟪ (ℓ "亠亰亙") ⟫ʷ ≈ ⟪ (ℓ "亙亠") ⟫ʷ
wp1045 c4 L = pw1 c4 L (ℓ "亠亰亙") (ℓ "亙亠") tt tt Eq.refl

wp1046 : Base 4 → WsL → ⟪ (ℓ "亘亲") ⟫ʷ ≈ ⟪ (ℓ "亲亜亘") ⟫ʷ
wp1046 c4 L = pw1 c4 L (ℓ "亘亲") (ℓ "亲亜亘") tt tt Eq.refl

wp1047 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亝丨亝丩亝丨亝丩") ⟫ʷ
wp1047 c4 L = pw3 c4 L (ℓ "亨") (ℓ "亝丨亝丩亝丨亝丩") tt tt Eq.refl

wp1048 : Base 4 → WsL → ⟪ (ℓ "亠亡个亡亠个") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wp1048 c4 L = pw2 c4 L (ℓ "亠亡个亡亠个") (ℓ "京") tt tt Eq.refl

wp1049 : Base 4 → WsL → ⟪ (ℓ "乭些") ⟫ʷ ≈ ⟪ (ℓ "些乭") ⟫ʷ
wp1049 c4 L = pw1 c4 L (ℓ "乭些") (ℓ "些乭") tt tt Eq.refl

wp1050 : Base 4 → WsL → ⟪ (ℓ "了些") ⟫ʷ ≈ ⟪ (ℓ "些了亢") ⟫ʷ
wp1050 c4 L = pw1 c4 L (ℓ "了些") (ℓ "些了亢") tt tt Eq.refl

wp1051 : Base 4 → WsL → ⟪ (ℓ "京亢五") ⟫ʷ ≈ ⟪ (ℓ "亢京") ⟫ʷ
wp1051 c4 L = pw2 c4 L (ℓ "京亢五") (ℓ "亢京") tt tt Eq.refl

wp1052 : Base 4 → WsL → ⟪ (ℓ "乁些") ⟫ʷ ≈ ⟪ (ℓ "些乁") ⟫ʷ
wp1052 c4 L = pw1 c4 L (ℓ "乁些") (ℓ "些乁") tt tt Eq.refl

wp1053 : Base 4 → WsL → ⟪ (ℓ "些亢") ⟫ʷ ≈ ⟪ (ℓ "亢些") ⟫ʷ
wp1053 c4 L = pw1 c4 L (ℓ "些亢") (ℓ "亢些") tt tt Eq.refl

wp1054 : Base 4 → WsL → ⟪ (ℓ "了亢亢") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wp1054 c4 L = pw1 c4 L (ℓ "了亢亢") (ℓ "了") tt tt Eq.refl

wp1055 : Base 4 → WsL → ⟪ (ℓ "了亢") ⟫ʷ ≈ ⟪ (ℓ "亢了") ⟫ʷ
wp1055 c4 L = pw1 c4 L (ℓ "了亢") (ℓ "亢了") tt tt Eq.refl

wp1056 : Base 4 → WsL → ⟪ (ℓ "京亢") ⟫ʷ ≈ ⟪ (ℓ "亢京五") ⟫ʷ
wp1056 c4 L = pw2 c4 L (ℓ "京亢") (ℓ "亢京五") tt tt Eq.refl

wp1057 : Base 4 → WsL → ⟪ (ℓ "乭亢") ⟫ʷ ≈ ⟪ (ℓ "亢乭些") ⟫ʷ
wp1057 c4 L = pw1 c4 L (ℓ "乭亢") (ℓ "亢乭些") tt tt Eq.refl

wp1058 : Base 4 → WsL → ⟪ (ℓ "丨亢") ⟫ʷ ≈ ⟪ (ℓ "亢丨") ⟫ʷ
wp1058 c4 L = pw2 c4 L (ℓ "丨亢") (ℓ "亢丨") tt tt Eq.refl

wp1059 : Base 4 → WsL → ⟪ (ℓ "丳亢") ⟫ʷ ≈ ⟪ (ℓ "亢丳") ⟫ʷ
wp1059 c4 L = pw1 c4 L (ℓ "丳亢") (ℓ "亢丳") tt tt Eq.refl

wp1060 : Base 4 → WsL → ⟪ (ℓ "乭些些") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wp1060 c4 L = pw1 c4 L (ℓ "乭些些") (ℓ "乭") tt tt Eq.refl

wp1061 : Base 4 → WsL → ⟪ (ℓ "二亄二二") ⟫ʷ ≈ ⟪ (ℓ "二亄") ⟫ʷ
wp1061 c4 L = pw3 c4 L (ℓ "二亄二二") (ℓ "二亄") tt tt Eq.refl

wp1062 : Base 4 → WsL → ⟪ (ℓ "二亄二並") ⟫ʷ ≈ ⟪ (ℓ "並二丒亄丢二") ⟫ʷ
wp1062 c4 L = pw3 c4 L (ℓ "二亄二並") (ℓ "並二丒亄丢二") tt tt Eq.refl

wp1063 : Base 4 → WsL → ⟪ (ℓ "亰亢") ⟫ʷ ≈ ⟪ (ℓ "亢亰亜") ⟫ʷ
wp1063 c4 L = pw1 c4 L (ℓ "亰亢") (ℓ "亢亰亜") tt tt Eq.refl

wp1064 : Base 4 → WsL → ⟪ (ℓ "乙亢") ⟫ʷ ≈ ⟪ (ℓ "亢乙亓") ⟫ʷ
wp1064 c4 L = pw2 c4 L (ℓ "乙亢") (ℓ "亢乙亓") tt tt Eq.refl

wp1065 : Base 4 → WsL → ⟪ (ℓ "丯亢") ⟫ʷ ≈ ⟪ (ℓ "亢丯") ⟫ʷ
wp1065 c4 L = pw1 c4 L (ℓ "丯亢") (ℓ "亢丯") tt tt Eq.refl

wp1066 : Base 4 → WsL → ⟪ (ℓ "亓亢") ⟫ʷ ≈ ⟪ (ℓ "亢亓") ⟫ʷ
wp1066 c4 L = pw2 c4 L (ℓ "亓亢") (ℓ "亢亓") tt tt Eq.refl

wp1067 : Base 4 → WsL → ⟪ (ℓ "乙亓亓") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wp1067 c4 L = pw2 c4 L (ℓ "乙亓亓") (ℓ "乙") tt tt Eq.refl

wp1068 : Base 4 → WsL → ⟪ (ℓ "亠亡丱亡亠丱") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wp1068 c4 L = pw1 c4 L (ℓ "亠亡丱亡亠丱") (ℓ "亰") tt tt Eq.refl

wp1069 : Base 4 → WsL → ⟪ (ℓ "乙亓") ⟫ʷ ≈ ⟪ (ℓ "亓乙") ⟫ʷ
wp1069 c4 L = pw2 c4 L (ℓ "乙亓") (ℓ "亓乙") tt tt Eq.refl

wp1070 : Base 4 → WsL → ⟪ (ℓ "亃亓") ⟫ʷ ≈ ⟪ (ℓ "亓亃亢") ⟫ʷ
wp1070 c4 L = pw2 c4 L (ℓ "亃亓") (ℓ "亓亃亢") tt tt Eq.refl

wp1071 : Base 4 → WsL → ⟪ (ℓ "亰亢亜") ⟫ʷ ≈ ⟪ (ℓ "亢亰") ⟫ʷ
wp1071 c4 L = pw1 c4 L (ℓ "亰亢亜") (ℓ "亢亰") tt tt Eq.refl

wp1072 : Base 4 → WsL → ⟪ (ℓ "乁亓") ⟫ʷ ≈ ⟪ (ℓ "亓乁") ⟫ʷ
wp1072 c4 L = pw2 c4 L (ℓ "乁亓") (ℓ "亓乁") tt tt Eq.refl

wp1073 : Base 4 → WsL → ⟪ (ℓ "亃亢亢") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wp1073 c4 L = pw2 c4 L (ℓ "亃亢亢") (ℓ "亃") tt tt Eq.refl

wp1074 : Base 4 → WsL → ⟪ (ℓ "二亇二二") ⟫ʷ ≈ ⟪ (ℓ "二亇") ⟫ʷ
wp1074 c4 L = pw3 c4 L (ℓ "二亇二二") (ℓ "二亇") tt tt Eq.refl

wp1075 : Base 4 → WsL → ⟪ (ℓ "二亇二並") ⟫ʷ ≈ ⟪ (ℓ "並二丘亇丢二") ⟫ʷ
wp1075 c4 L = pw3 c4 L (ℓ "二亇二並") (ℓ "並二丘亇丢二") tt tt Eq.refl

wp1076 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "亪丯亪丰亪丯亪丰") ⟫ʷ
wp1076 c4 L = pw3 c4 L (ℓ "五") (ℓ "亪丯亪丰亪丯亪丰") tt tt Eq.refl

wp1077 : Base 4 → WsL → ⟪ (ℓ "京乁亐") ⟫ʷ ≈ ⟪ (ℓ "乁京") ⟫ʷ
wp1077 c4 L = pw2 c4 L (ℓ "京乁亐") (ℓ "乁京") tt tt Eq.refl

wp1078 : Base 4 → WsL → ⟪ (ℓ "乁亐亐") ⟫ʷ ≈ ⟪ (ℓ "乁") ⟫ʷ
wp1078 c4 L = pw2 c4 L (ℓ "乁亐亐") (ℓ "乁") tt tt Eq.refl

wp1079 : Base 4 → WsL → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "乁二乁") ⟫ʷ
wp1079 c4 L = pw3 c4 L (ℓ "二") (ℓ "乁二乁") tt tt Eq.refl

wp1080 : Base 4 → WsL → ⟪ (ℓ "亀些") ⟫ʷ ≈ ⟪ (ℓ "些亀亲") ⟫ʷ
wp1080 c4 L = pw1 c4 L (ℓ "亀些") (ℓ "些亀亲") tt tt Eq.refl

wp1081 : Base 4 → WsL → ⟪ (ℓ "京亀") ⟫ʷ ≈ ⟪ (ℓ "亀京") ⟫ʷ
wp1081 c4 L = pw2 c4 L (ℓ "京亀") (ℓ "亀京") tt tt Eq.refl

wp1082 : Base 4 → WsL → ⟪ (ℓ "亀亲亲") ⟫ʷ ≈ ⟪ (ℓ "亀") ⟫ʷ
wp1082 c4 L = pw1 c4 L (ℓ "亀亲亲") (ℓ "亀") tt tt Eq.refl

wp1083 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "亀亨亀") ⟫ʷ
wp1083 c4 L = pw3 c4 L (ℓ "亨") (ℓ "亀亨亀") tt tt Eq.refl

wp1084 : Base 4 → WsL → ⟪ (ℓ "乁亀乁") ⟫ʷ ≈ ⟪ (ℓ "乀") ⟫ʷ
wp1084 c4 L = pw1 c4 L (ℓ "乁亀乁") (ℓ "乀") tt tt Eq.refl

wp1085 : Base 4 → WsL → ⟪ (ℓ "二亀") ⟫ʷ ≈ ⟪ (ℓ "亀亨二") ⟫ʷ
wp1085 c4 L = pw3 c4 L (ℓ "二亀") (ℓ "亀亨二") tt tt Eq.refl

wp1086 : Base 4 → WsL → ⟪ (ℓ "二乁") ⟫ʷ ≈ ⟪ (ℓ "乁二") ⟫ʷ
wp1086 c4 L = pw3 c4 L (ℓ "二乁") (ℓ "乁二") tt tt Eq.refl

wp1087 : Base 4 → WsL → ⟪ (ℓ "亨乁") ⟫ʷ ≈ ⟪ (ℓ "乁二亨") ⟫ʷ
wp1087 c4 L = pw3 c4 L (ℓ "亨乁") (ℓ "乁二亨") tt tt Eq.refl

wp1088 : Base 4 → WsL → ⟪ (ℓ "二亨二亨二") ⟫ʷ ≈ ⟪ (ℓ "二") ⟫ʷ
wp1088 c4 L = pw3 c4 L (ℓ "二亨二亨二") (ℓ "二") tt tt Eq.refl

wp1089 : Base 4 → WsL → ⟪ (ℓ "亰乀") ⟫ʷ ≈ ⟪ (ℓ "乀亘") ⟫ʷ
wp1089 c4 L = pw1 c4 L (ℓ "亰乀") (ℓ "乀亘") tt tt Eq.refl

wp1090 : Base 4 → WsL → ⟪ (ℓ "乀些") ⟫ʷ ≈ ⟪ (ℓ "亲乀") ⟫ʷ
wp1090 c4 L = pw1 c4 L (ℓ "乀些") (ℓ "亲乀") tt tt Eq.refl

wp1091 : Base 4 → WsL → ⟪ (ℓ "亘乀") ⟫ʷ ≈ ⟪ (ℓ "乀亰") ⟫ʷ
wp1091 c4 L = pw1 c4 L (ℓ "亘乀") (ℓ "乀亰") tt tt Eq.refl

wp1092 : Base 4 → WsL → ⟪ (ℓ "乀亱") ⟫ʷ ≈ ⟪ (ℓ "亚乀") ⟫ʷ
wp1092 c4 L = pw1 c4 L (ℓ "乀亱") (ℓ "亚乀") tt tt Eq.refl

wp1093 : Base 4 → WsL → ⟪ (ℓ "乀乀") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1093 c4 L = pw1 c4 L (ℓ "乀乀") [] tt tt Eq.refl

wp1094 : Base 4 → WsL → ⟪ (ℓ "亀亲") ⟫ʷ ≈ ⟪ (ℓ "亲亀") ⟫ʷ
wp1094 c4 L = pw1 c4 L (ℓ "亀亲") (ℓ "亲亀") tt tt Eq.refl

wp1095 : Base 4 → WsL → ⟪ (ℓ "亐亀京") ⟫ʷ ≈ ⟪ (ℓ "亀亐") ⟫ʷ
wp1095 c4 L = pw2 c4 L (ℓ "亐亀京") (ℓ "亀亐") tt tt Eq.refl

wp1096 : Base 4 → WsL → ⟪ (ℓ "亀京京") ⟫ʷ ≈ ⟪ (ℓ "亀") ⟫ʷ
wp1096 c4 L = pw2 c4 L (ℓ "亀京京") (ℓ "亀") tt tt Eq.refl

wp1097 : Base 4 → WsL → ⟪ (ℓ "乁亲") ⟫ʷ ≈ ⟪ (ℓ "亲乁些") ⟫ʷ
wp1097 c4 L = pw1 c4 L (ℓ "乁亲") (ℓ "亲乁些") tt tt Eq.refl

wp1098 : Base 4 → WsL → ⟪ (ℓ "亐乁") ⟫ʷ ≈ ⟪ (ℓ "乁亐") ⟫ʷ
wp1098 c4 L = pw2 c4 L (ℓ "亐乁") (ℓ "乁亐") tt tt Eq.refl

wp1099 : Base 4 → WsL → ⟪ (ℓ "乜亲") ⟫ʷ ≈ ⟪ (ℓ "亲乜") ⟫ʷ
wp1099 c4 L = pw1 c4 L (ℓ "乜亲") (ℓ "亲乜") tt tt Eq.refl

wp1100 : Base 4 → WsL → ⟪ (ℓ "乁些些") ⟫ʷ ≈ ⟪ (ℓ "乁") ⟫ʷ
wp1100 c4 L = pw1 c4 L (ℓ "乁些些") (ℓ "乁") tt tt Eq.refl

wp1101 : Base 4 → WsL → ⟪ (ℓ "亀乁亀") ⟫ʷ ≈ ⟪ (ℓ "乀") ⟫ʷ
wp1101 c4 L = pw1 c4 L (ℓ "亀乁亀") (ℓ "乀") tt tt Eq.refl

wp1102 : Base 4 → WsL → ⟪ (ℓ "亨二亨二亨") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp1102 c4 L = pw3 c4 L (ℓ "亨二亨二亨") (ℓ "亨") tt tt Eq.refl

wp1103 : Base 4 → WsL → ⟪ (ℓ "乀亲") ⟫ʷ ≈ ⟪ (ℓ "些乀") ⟫ʷ
wp1103 c4 L = pw1 c4 L (ℓ "乀亲") (ℓ "些乀") tt tt Eq.refl

wp1104 : Base 4 → WsL → ⟪ (ℓ "乀亚") ⟫ʷ ≈ ⟪ (ℓ "亱乀") ⟫ʷ
wp1104 c4 L = pw1 c4 L (ℓ "乀亚") (ℓ "亱乀") tt tt Eq.refl

wp1105 : Base 4 → WsL → ⟪ (ℓ "二亁二二") ⟫ʷ ≈ ⟪ (ℓ "二亁") ⟫ʷ
wp1105 c4 L = pw3 c4 L (ℓ "二亁二二") (ℓ "二亁") tt tt Eq.refl

wp1106 : Base 4 → WsL → ⟪ (ℓ "亠丌") ⟫ʷ ≈ ⟪ (ℓ "丌亡亠亠") ⟫ʷ
wp1106 c4 L = pw1 c4 L (ℓ "亠丌") (ℓ "丌亡亠亠") tt tt Eq.refl

wp1107 : Base 4 → WsL → ⟪ (ℓ "亠亁") ⟫ʷ ≈ ⟪ (ℓ "丸亁丸亠") ⟫ʷ
wp1107 c4 L = pw1 c4 L (ℓ "亠亁") (ℓ "丸亁丸亠") tt tt Eq.refl

wp1108 : Base 4 → WsL → ⟪ (ℓ "丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亡亠丸亁丸丢") ⟫ʷ
wp1108 c4 L = pw1 c4 L (ℓ "丌亁丢") (ℓ "丌亡亠丸亁丸丢") tt tt Eq.refl

wp1109 : Base 4 → WsL → ⟪ (ℓ "二亁二並") ⟫ʷ ≈ ⟪ (ℓ "並二丌亁丢二") ⟫ʷ
wp1109 c4 L = pw3 c4 L (ℓ "二亁二並") (ℓ "並二丌亁丢二") tt tt Eq.refl

wp1110 : Base 4 → WsL → ⟪ (ℓ "亁五亁丢亄五亄丢") ⟫ʷ ≈ ⟪ (ℓ "井亖") ⟫ʷ
wp1110 c4 L = pw2 c4 L (ℓ "亁五亁丢亄五亄丢") (ℓ "井亖") tt tt Eq.refl

wp1111 : Base 4 → WsL → ⟪ (ℓ "丢些") ⟫ʷ ≈ ⟪ (ℓ "些丢") ⟫ʷ
wp1111 c4 L = pw1 c4 L (ℓ "丢些") (ℓ "些丢") tt tt Eq.refl

wp1112 : Base 4 → WsL → ⟪ (ℓ "井亖亝丨亝丩二亄五亄丢亁五亁二丢") ⟫ʷ ≈ ⟪ (ℓ "亪亩亪丯亪丰二亄亨亄丢亇亨亇二丢") ⟫ʷ
wp1112 c4 L = pw3 c4 L (ℓ "井亖亝丨亝丩二亄五亄丢亁五亁二丢") (ℓ "亪亩亪丯亪丰二亄亨亄丢亇亨亇二丢") tt tt Eq.refl

wp1113 : Base 4 → WsL → ⟪ (ℓ "了亍") ⟫ʷ ≈ ⟪ (ℓ "亍了井") ⟫ʷ
wp1113 c4 L = pw3 c4 L (ℓ "了亍") (ℓ "亍了井") tt tt Eq.refl

wp1114 : Base 4 → WsL → ⟪ (ℓ "亠井京") ⟫ʷ ≈ ⟪ (ℓ "井亠") ⟫ʷ
wp1114 c4 L = pw2 c4 L (ℓ "亠井京") (ℓ "井亠") tt tt Eq.refl

wp1115 : Base 4 → WsL → ⟪ (ℓ "了井井") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wp1115 c4 L = pw3 c4 L (ℓ "了井井") (ℓ "了") tt tt Eq.refl

wp1116 : Base 4 → WsL → ⟪ (ℓ "乬亍") ⟫ʷ ≈ ⟪ (ℓ "井乬") ⟫ʷ
wp1116 c4 L = pw3 c4 L (ℓ "乬亍") (ℓ "井乬") tt tt Eq.refl

wp1117 : Base 4 → WsL → ⟪ (ℓ "乬亖") ⟫ʷ ≈ ⟪ (ℓ "于乬") ⟫ʷ
wp1117 c4 L = pw3 c4 L (ℓ "乬亖") (ℓ "于乬") tt tt Eq.refl

wp1118 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亄五亄丢亨亄五亄丢亨") ⟫ʷ
wp1118 c4 L = pw3 c4 L (ℓ "亜") (ℓ "亄五亄丢亨亄五亄丢亨") tt tt Eq.refl

wp1119 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亁五亁丢亄五亄丢亨亄五亄丢亁五亁丢") ⟫ʷ
wp1119 c4 L = pw3 c4 L (ℓ "亜") (ℓ "亁五亁丢亄五亄丢亨亄五亄丢亁五亁丢") tt tt Eq.refl

wp1120 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
wp1120 c4 L = pw1 c4 L (ℓ "亜") (ℓ "亜") tt tt Eq.refl

wp1121 : Base 4 → WsL → ⟪ (ℓ "二亄二亨二亄二丢五亪五五丯亪五五丰二二亄二二亨二二亄") ⟫ʷ ≈ ⟪ (ℓ "亄二亨二亄二丢五亪五五丯亪五五丰二二亄二二亨二二亄二") ⟫ʷ
wp1121 c4 L = pw3 c4 L (ℓ "二亄二亨二亄二丢五亪五五丯亪五五丰二二亄二二亨二二亄") (ℓ "亄二亨二亄二丢五亪五五丯亪五五丰二二亄二二亨二二亄二") tt tt Eq.refl

wp1122 : Base 4 → WsL → ⟪ (ℓ "二丢五亪五五丯亪五五丰") ⟫ʷ ≈ ⟪ (ℓ "丢五亪五五丯亪五五丰二") ⟫ʷ
wp1122 c4 L = pw3 c4 L (ℓ "二丢五亪五五丯亪五五丰") (ℓ "丢五亪五五丯亪五五丰二") tt tt Eq.refl
