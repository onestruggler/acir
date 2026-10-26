------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP02 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp0260 : Base 4 → WsL → ⟪ (ℓ "不亁") ⟫ʷ ≈ ⟪ (ℓ "並亂並") ⟫ʷ
wp0260 c4 L = pw1 c4 L (ℓ "不亁") (ℓ "並亂並") tt tt Eq.refl

wp0261 : Base 4 → WsL → ⟪ (ℓ "京丨") ⟫ʷ ≈ ⟪ (ℓ "丨京") ⟫ʷ
wp0261 c4 L = pw2 c4 L (ℓ "京丨") (ℓ "丨京") tt tt Eq.refl

wp0262 : Base 4 → WsL → ⟪ (ℓ "亐云丿云亐丿") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wp0262 c4 L = pw2 c4 L (ℓ "亐云丿云亐丿") (ℓ "京") tt tt Eq.refl

wp0263 : Base 4 → WsL → ⟪ (ℓ "乭亙") ⟫ʷ ≈ ⟪ (ℓ "亙乭") ⟫ʷ
wp0263 c4 L = pw1 c4 L (ℓ "乭亙") (ℓ "亙乭") tt tt Eq.refl

wp0264 : Base 4 → WsL → ⟪ (ℓ "五乭二") ⟫ʷ ≈ ⟪ (ℓ "乭五") ⟫ʷ
wp0264 c4 L = pw3 c4 L (ℓ "五乭二") (ℓ "乭五") tt tt Eq.refl

wp0265 : Base 4 → WsL → ⟪ (ℓ "五么") ⟫ʷ ≈ ⟪ (ℓ "么五") ⟫ʷ
wp0265 c4 L = pw3 c4 L (ℓ "五么") (ℓ "么五") tt tt Eq.refl

wp0266 : Base 4 → WsL → ⟪ (ℓ "乭二二") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wp0266 c4 L = pw3 c4 L (ℓ "乭二二") (ℓ "乭") tt tt Eq.refl

wp0267 : Base 4 → WsL → ⟪ (ℓ "了亙") ⟫ʷ ≈ ⟪ (ℓ "亙了亡") ⟫ʷ
wp0267 c4 L = pw1 c4 L (ℓ "了亙") (ℓ "亙了亡") tt tt Eq.refl

wp0268 : Base 4 → WsL → ⟪ (ℓ "五亡京") ⟫ʷ ≈ ⟪ (ℓ "亡五") ⟫ʷ
wp0268 c4 L = pw2 c4 L (ℓ "五亡京") (ℓ "亡五") tt tt Eq.refl

wp0269 : Base 4 → WsL → ⟪ (ℓ "五了") ⟫ʷ ≈ ⟪ (ℓ "了五") ⟫ʷ
wp0269 c4 L = pw3 c4 L (ℓ "五了") (ℓ "了五") tt tt Eq.refl

wp0270 : Base 4 → WsL → ⟪ (ℓ "乽亙") ⟫ʷ ≈ ⟪ (ℓ "亙乽") ⟫ʷ
wp0270 c4 L = pw1 c4 L (ℓ "乽亙") (ℓ "亙乽") tt tt Eq.refl

wp0271 : Base 4 → WsL → ⟪ (ℓ "了亡亡") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wp0271 c4 L = pw1 c4 L (ℓ "了亡亡") (ℓ "了") tt tt Eq.refl

wp0272 : Base 4 → WsL → ⟪ (ℓ "五京") ⟫ʷ ≈ ⟪ (ℓ "京五") ⟫ʷ
wp0272 c4 L = pw2 c4 L (ℓ "五京") (ℓ "京五") tt tt Eq.refl

wp0273 : Base 4 → WsL → ⟪ (ℓ "乬亙") ⟫ʷ ≈ ⟪ (ℓ "亡乬") ⟫ʷ
wp0273 c4 L = pw1 c4 L (ℓ "乬亙") (ℓ "亡乬") tt tt Eq.refl

wp0274 : Base 4 → WsL → ⟪ (ℓ "乬亢") ⟫ʷ ≈ ⟪ (ℓ "些乬") ⟫ʷ
wp0274 c4 L = pw1 c4 L (ℓ "乬亢") (ℓ "些乬") tt tt Eq.refl

wp0275 : Base 4 → WsL → ⟪ (ℓ "五亭") ⟫ʷ ≈ ⟪ (ℓ "亭五亠") ⟫ʷ
wp0275 c4 L = pw2 c4 L (ℓ "五亭") (ℓ "亭五亠") tt tt Eq.refl

wp0276 : Base 4 → WsL → ⟪ (ℓ "五亠亭") ⟫ʷ ≈ ⟪ (ℓ "亭五") ⟫ʷ
wp0276 c4 L = pw2 c4 L (ℓ "五亠亭") (ℓ "亭五") tt tt Eq.refl

wp0277 : Base 4 → WsL → ⟪ (ℓ "丶亭") ⟫ʷ ≈ ⟪ (ℓ "亭丶") ⟫ʷ
wp0277 c4 L = pw2 c4 L (ℓ "丶亭") (ℓ "亭丶") tt tt Eq.refl

wp0278 : Base 4 → WsL → ⟪ (ℓ "亰亙") ⟫ʷ ≈ ⟪ (ℓ "亙亰") ⟫ʷ
wp0278 c4 L = pw1 c4 L (ℓ "亰亙") (ℓ "亙亰") tt tt Eq.refl

wp0279 : Base 4 → WsL → ⟪ (ℓ "亰丯") ⟫ʷ ≈ ⟪ (ℓ "丯亰") ⟫ʷ
wp0279 c4 L = pw1 c4 L (ℓ "亰丯") (ℓ "丯亰") tt tt Eq.refl

wp0280 : Base 4 → WsL → ⟪ (ℓ "亘亙丿亙亘丿") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wp0280 c4 L = pw1 c4 L (ℓ "亘亙丿亙亘丿") (ℓ "亰") tt tt Eq.refl

wp0281 : Base 4 → WsL → ⟪ (ℓ "乙云") ⟫ʷ ≈ ⟪ (ℓ "云乙") ⟫ʷ
wp0281 c4 L = pw2 c4 L (ℓ "乙云") (ℓ "云乙") tt tt Eq.refl

wp0282 : Base 4 → WsL → ⟪ (ℓ "亜乙二") ⟫ʷ ≈ ⟪ (ℓ "乙亜") ⟫ʷ
wp0282 c4 L = pw3 c4 L (ℓ "亜乙二") (ℓ "乙亜") tt tt Eq.refl

wp0283 : Base 4 → WsL → ⟪ (ℓ "乙二二") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wp0283 c4 L = pw3 c4 L (ℓ "乙二二") (ℓ "乙") tt tt Eq.refl

wp0284 : Base 4 → WsL → ⟪ (ℓ "亃云") ⟫ʷ ≈ ⟪ (ℓ "云亃亡") ⟫ʷ
wp0284 c4 L = pw2 c4 L (ℓ "亃云") (ℓ "云亃亡") tt tt Eq.refl

wp0285 : Base 4 → WsL → ⟪ (ℓ "亜亃") ⟫ʷ ≈ ⟪ (ℓ "亃亜") ⟫ʷ
wp0285 c4 L = pw3 c4 L (ℓ "亜亃") (ℓ "亃亜") tt tt Eq.refl

wp0286 : Base 4 → WsL → ⟪ (ℓ "乽云") ⟫ʷ ≈ ⟪ (ℓ "云乽") ⟫ʷ
wp0286 c4 L = pw2 c4 L (ℓ "乽云") (ℓ "云乽") tt tt Eq.refl

wp0287 : Base 4 → WsL → ⟪ (ℓ "亃亡亡") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wp0287 c4 L = pw2 c4 L (ℓ "亃亡亡") (ℓ "亃") tt tt Eq.refl

wp0288 : Base 4 → WsL → ⟪ (ℓ "乘云") ⟫ʷ ≈ ⟪ (ℓ "亡乘") ⟫ʷ
wp0288 c4 L = pw2 c4 L (ℓ "乘云") (ℓ "亡乘") tt tt Eq.refl

wp0289 : Base 4 → WsL → ⟪ (ℓ "乘亢") ⟫ʷ ≈ ⟪ (ℓ "亓乘") ⟫ʷ
wp0289 c4 L = pw2 c4 L (ℓ "乘亢") (ℓ "亓乘") tt tt Eq.refl

wp0290 : Base 4 → WsL → ⟪ (ℓ "亜亱") ⟫ʷ ≈ ⟪ (ℓ "亱亜亠") ⟫ʷ
wp0290 c4 L = pw1 c4 L (ℓ "亜亱") (ℓ "亱亜亠") tt tt Eq.refl

wp0291 : Base 4 → WsL → ⟪ (ℓ "亜亠亱") ⟫ʷ ≈ ⟪ (ℓ "亱亜") ⟫ʷ
wp0291 c4 L = pw1 c4 L (ℓ "亜亠亱") (ℓ "亱亜") tt tt Eq.refl

wp0292 : Base 4 → WsL → ⟪ (ℓ "丶亱") ⟫ʷ ≈ ⟪ (ℓ "亱丶") ⟫ʷ
wp0292 c4 L = pw1 c4 L (ℓ "丶亱") (ℓ "亱丶") tt tt Eq.refl

wp0293 : Base 4 → WsL → ⟪ (ℓ "京云") ⟫ʷ ≈ ⟪ (ℓ "云京") ⟫ʷ
wp0293 c4 L = pw2 c4 L (ℓ "京云") (ℓ "云京") tt tt Eq.refl

wp0294 : Base 4 → WsL → ⟪ (ℓ "亰丶") ⟫ʷ ≈ ⟪ (ℓ "丶亰") ⟫ʷ
wp0294 c4 L = pw1 c4 L (ℓ "亰丶") (ℓ "丶亰") tt tt Eq.refl

wp0295 : Base 4 → WsL → ⟪ (ℓ "亠亲") ⟫ʷ ≈ ⟪ (ℓ "亲亜亠") ⟫ʷ
wp0295 c4 L = pw1 c4 L (ℓ "亠亲") (ℓ "亲亜亠") tt tt Eq.refl

wp0296 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "乩丳乪丳丽") ⟫ʷ
wp0296 c4 L = pw1 c4 L (ℓ "亜") (ℓ "乩丳乪丳丽") tt tt Eq.refl

wp0297 : Base 4 → WsL → ⟪ (ℓ "亜亠亲") ⟫ʷ ≈ ⟪ (ℓ "亲亠") ⟫ʷ
wp0297 c4 L = pw1 c4 L (ℓ "亜亠亲") (ℓ "亲亠") tt tt Eq.refl

wp0298 : Base 4 → WsL → ⟪ (ℓ "丯亲") ⟫ʷ ≈ ⟪ (ℓ "亲丯") ⟫ʷ
wp0298 c4 L = pw1 c4 L (ℓ "丯亲") (ℓ "亲丯") tt tt Eq.refl

wp0299 : Base 4 → WsL → ⟪ (ℓ "亐乕") ⟫ʷ ≈ ⟪ (ℓ "乕亐") ⟫ʷ
wp0299 c4 L = pw2 c4 L (ℓ "亐乕") (ℓ "乕亐") tt tt Eq.refl

wp0300 : Base 4 → WsL → ⟪ (ℓ "亨亍") ⟫ʷ ≈ ⟪ (ℓ "亍亨") ⟫ʷ
wp0300 c4 L = pw3 c4 L (ℓ "亨亍") (ℓ "亍亨") tt tt Eq.refl

wp0301 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "乕丬乖丬丽") ⟫ʷ
wp0301 c4 L = pw2 c4 L (ℓ "五") (ℓ "乕丬乖丬丽") tt tt Eq.refl

wp0302 : Base 4 → WsL → ⟪ (ℓ "亰丽") ⟫ʷ ≈ ⟪ (ℓ "丽亰") ⟫ʷ
wp0302 c4 L = pw1 c4 L (ℓ "亰丽") (ℓ "丽亰") tt tt Eq.refl

wp0303 : Base 4 → WsL → ⟪ (ℓ "两五严") ⟫ʷ ≈ ⟪ (ℓ "亗") ⟫ʷ
wp0303 c4 L = pw2 c4 L (ℓ "两五严") (ℓ "亗") tt tt Eq.refl

wp0304 : Base 4 → WsL → ⟪ (ℓ "丩丢亗丣") ⟫ʷ ≈ ⟪ (ℓ "亗五") ⟫ʷ
wp0304 c4 L = pw2 c4 L (ℓ "丩丢亗丣") (ℓ "亗五") tt tt Eq.refl

wp0305 : Base 4 → WsL → ⟪ (ℓ "亜亝丸亝亜丸") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wp0305 c4 L = pw1 c4 L (ℓ "亜亝丸亝亜丸") (ℓ "亰") tt tt Eq.refl

wp0306 : Base 4 → WsL → ⟪ (ℓ "亗亗") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0306 c4 L = pw2 c4 L (ℓ "亗亗") [] tt tt Eq.refl

wp0307 : Base 4 → WsL → ⟪ (ℓ "亠亳") ⟫ʷ ≈ ⟪ (ℓ "亳亘亠") ⟫ʷ
wp0307 c4 L = pw1 c4 L (ℓ "亠亳") (ℓ "亳亘亠") tt tt Eq.refl

wp0308 : Base 4 → WsL → ⟪ (ℓ "五丳") ⟫ʷ ≈ ⟪ (ℓ "丳五") ⟫ʷ
wp0308 c4 L = pw3 c4 L (ℓ "五丳") (ℓ "丳五") tt tt Eq.refl

wp0309 : Base 4 → WsL → ⟪ (ℓ "亘亠亳") ⟫ʷ ≈ ⟪ (ℓ "亳亠") ⟫ʷ
wp0309 c4 L = pw1 c4 L (ℓ "亘亠亳") (ℓ "亳亠") tt tt Eq.refl

wp0310 : Base 4 → WsL → ⟪ (ℓ "五亍亨") ⟫ʷ ≈ ⟪ (ℓ "亍五") ⟫ʷ
wp0310 c4 L = pw3 c4 L (ℓ "五亍亨") (ℓ "亍五") tt tt Eq.refl

wp0311 : Base 4 → WsL → ⟪ (ℓ "丯亳") ⟫ʷ ≈ ⟪ (ℓ "亳丯") ⟫ʷ
wp0311 c4 L = pw1 c4 L (ℓ "丯亳") (ℓ "亳丯") tt tt Eq.refl

wp0312 : Base 4 → WsL → ⟪ (ℓ "亠乎") ⟫ʷ ≈ ⟪ (ℓ "乎亠") ⟫ʷ
wp0312 c4 L = pw2 c4 L (ℓ "亠乎") (ℓ "乎亠") tt tt Eq.refl

wp0313 : Base 4 → WsL → ⟪ (ℓ "亠乣") ⟫ʷ ≈ ⟪ (ℓ "乣亠") ⟫ʷ
wp0313 c4 L = pw1 c4 L (ℓ "亠乣") (ℓ "乣亠") tt tt Eq.refl

wp0314 : Base 4 → WsL → ⟪ (ℓ "亠乢") ⟫ʷ ≈ ⟪ (ℓ "乢亠") ⟫ʷ
wp0314 c4 L = pw1 c4 L (ℓ "亠乢") (ℓ "乢亠") tt tt Eq.refl

wp0315 : Base 4 → WsL → ⟪ (ℓ "两亠严") ⟫ʷ ≈ ⟪ (ℓ "亣") ⟫ʷ
wp0315 c4 L = pw1 c4 L (ℓ "两亠严") (ℓ "亣") tt tt Eq.refl

wp0316 : Base 4 → WsL → ⟪ (ℓ "丷丢亣丣") ⟫ʷ ≈ ⟪ (ℓ "亣亠") ⟫ʷ
wp0316 c4 L = pw1 c4 L (ℓ "丷丢亣丣") (ℓ "亣亠") tt tt Eq.refl

wp0317 : Base 4 → WsL → ⟪ (ℓ "亣亣") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0317 c4 L = pw1 c4 L (ℓ "亣亣") [] tt tt Eq.refl

wp0318 : Base 4 → WsL → ⟪ (ℓ "亨举") ⟫ʷ ≈ ⟪ (ℓ "举亨") ⟫ʷ
wp0318 c4 L = pw3 c4 L (ℓ "亨举") (ℓ "举亨") tt tt Eq.refl

wp0319 : Base 4 → WsL → ⟪ (ℓ "举亣") ⟫ʷ ≈ ⟪ (ℓ "亣举丷亠") ⟫ʷ
wp0319 c4 L = pw1 c4 L (ℓ "举亣") (ℓ "亣举丷亠") tt tt Eq.refl

wp0320 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丶亀丷亀乹") ⟫ʷ
wp0320 c4 L = pw1 c4 L (ℓ "亠") (ℓ "丶亀丷亀乹") tt tt Eq.refl

wp0321 : Base 4 → WsL → ⟪ (ℓ "亨亀") ⟫ʷ ≈ ⟪ (ℓ "亀亨") ⟫ʷ
wp0321 c4 L = pw3 c4 L (ℓ "亨亀") (ℓ "亀亨") tt tt Eq.refl

wp0322 : Base 4 → WsL → ⟪ (ℓ "亠亣") ⟫ʷ ≈ ⟪ (ℓ "亣丸亠") ⟫ʷ
wp0322 c4 L = pw1 c4 L (ℓ "亠亣") (ℓ "亣丸亠") tt tt Eq.refl

wp0323 : Base 4 → WsL → ⟪ (ℓ "丷亣") ⟫ʷ ≈ ⟪ (ℓ "亣丷") ⟫ʷ
wp0323 c4 L = pw1 c4 L (ℓ "丷亣") (ℓ "亣丷") tt tt Eq.refl

wp0324 : Base 4 → WsL → ⟪ (ℓ "举丷亠丷丸亠") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp0324 c4 L = pw1 c4 L (ℓ "举丷亠丷丸亠") (ℓ "举") tt tt Eq.refl

wp0325 : Base 4 → WsL → ⟪ (ℓ "丽丶亠乽") ⟫ʷ ≈ ⟪ (ℓ "乽丽") ⟫ʷ
wp0325 c4 L = pw1 c4 L (ℓ "丽丶亠乽") (ℓ "乽丽") tt tt Eq.refl

wp0326 : Base 4 → WsL → ⟪ (ℓ "举丷亠乽") ⟫ʷ ≈ ⟪ (ℓ "乽举") ⟫ʷ
wp0326 c4 L = pw1 c4 L (ℓ "举丷亠乽") (ℓ "乽举") tt tt Eq.refl

wp0327 : Base 4 → WsL → ⟪ (ℓ "亠丶") ⟫ʷ ≈ ⟪ (ℓ "丶亠") ⟫ʷ
wp0327 c4 L = pw1 c4 L (ℓ "亠丶") (ℓ "丶亠") tt tt Eq.refl

wp0328 : Base 4 → WsL → ⟪ (ℓ "丶举丷") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp0328 c4 L = pw1 c4 L (ℓ "丶举丷") (ℓ "举") tt tt Eq.refl

wp0329 : Base 4 → WsL → ⟪ (ℓ "亠举") ⟫ʷ ≈ ⟪ (ℓ "举亠") ⟫ʷ
wp0329 c4 L = pw1 c4 L (ℓ "亠举") (ℓ "举亠") tt tt Eq.refl

wp0330 : Base 4 → WsL → ⟪ (ℓ "乜享") ⟫ʷ ≈ ⟪ (ℓ "享乜") ⟫ʷ
wp0330 c4 L = pw3 c4 L (ℓ "乜享") (ℓ "享乜") tt tt Eq.refl

wp0331 : Base 4 → WsL → ⟪ (ℓ "丳享") ⟫ʷ ≈ ⟪ (ℓ "享丳亗") ⟫ʷ
wp0331 c4 L = pw3 c4 L (ℓ "丳享") (ℓ "享丳亗") tt tt Eq.refl

wp0332 : Base 4 → WsL → ⟪ (ℓ "亠亗亐") ⟫ʷ ≈ ⟪ (ℓ "亗亠") ⟫ʷ
wp0332 c4 L = pw2 c4 L (ℓ "亠亗亐") (ℓ "亗亠") tt tt Eq.refl

wp0333 : Base 4 → WsL → ⟪ (ℓ "亠丳") ⟫ʷ ≈ ⟪ (ℓ "丳亠") ⟫ʷ
wp0333 c4 L = pw1 c4 L (ℓ "亠丳") (ℓ "丳亠") tt tt Eq.refl

wp0334 : Base 4 → WsL → ⟪ (ℓ "乄享") ⟫ʷ ≈ ⟪ (ℓ "享乄") ⟫ʷ
wp0334 c4 L = pw3 c4 L (ℓ "乄享") (ℓ "享乄") tt tt Eq.refl

wp0335 : Base 4 → WsL → ⟪ (ℓ "亗享") ⟫ʷ ≈ ⟪ (ℓ "享亗") ⟫ʷ
wp0335 c4 L = pw3 c4 L (ℓ "亗享") (ℓ "享亗") tt tt Eq.refl

wp0336 : Base 4 → WsL → ⟪ (ℓ "丳亗亗") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
wp0336 c4 L = pw3 c4 L (ℓ "丳亗亗") (ℓ "丳") tt tt Eq.refl

wp0337 : Base 4 → WsL → ⟪ (ℓ "五串") ⟫ʷ ≈ ⟪ (ℓ "串亨") ⟫ʷ
wp0337 c4 L = pw3 c4 L (ℓ "五串") (ℓ "串亨") tt tt Eq.refl

wp0338 : Base 4 → WsL → ⟪ (ℓ "串享") ⟫ʷ ≈ ⟪ (ℓ "亗串") ⟫ʷ
wp0338 c4 L = pw3 c4 L (ℓ "串享") (ℓ "亗串") tt tt Eq.refl

wp0339 : Base 4 → WsL → ⟪ (ℓ "亨串") ⟫ʷ ≈ ⟪ (ℓ "串五") ⟫ʷ
wp0339 c4 L = pw3 c4 L (ℓ "亨串") (ℓ "串五") tt tt Eq.refl

wp0340 : Base 4 → WsL → ⟪ (ℓ "串亖") ⟫ʷ ≈ ⟪ (ℓ "亩串") ⟫ʷ
wp0340 c4 L = pw3 c4 L (ℓ "串亖") (ℓ "亩串") tt tt Eq.refl

wp0341 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "丽乄举乄乕") ⟫ʷ
wp0341 c4 L = pw2 c4 L (ℓ "五") (ℓ "丽乄举乄乕") tt tt Eq.refl

wp0342 : Base 4 → WsL → ⟪ (ℓ "亰举") ⟫ʷ ≈ ⟪ (ℓ "举亰") ⟫ʷ
wp0342 c4 L = pw1 c4 L (ℓ "亰举") (ℓ "举亰") tt tt Eq.refl

wp0343 : Base 4 → WsL → ⟪ (ℓ "丞亠丟") ⟫ʷ ≈ ⟪ (ℓ "亢") ⟫ʷ
wp0343 c4 L = pw1 c4 L (ℓ "丞亠丟") (ℓ "亢") tt tt Eq.refl

wp0344 : Base 4 → WsL → ⟪ (ℓ "亠丿亢") ⟫ʷ ≈ ⟪ (ℓ "亢亠") ⟫ʷ
wp0344 c4 L = pw1 c4 L (ℓ "亠丿亢") (ℓ "亢亠") tt tt Eq.refl

wp0345 : Base 4 → WsL → ⟪ (ℓ "亠丿") ⟫ʷ ≈ ⟪ (ℓ "亢亠亢") ⟫ʷ
wp0345 c4 L = pw1 c4 L (ℓ "亠丿") (ℓ "亢亠亢") tt tt Eq.refl

wp0346 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丿亠丿") ⟫ʷ
wp0346 c4 L = pw1 c4 L (ℓ "亠") (ℓ "丿亠丿") tt tt Eq.refl

wp0347 : Base 4 → WsL → ⟪ (ℓ "举东亢丝") ⟫ʷ ≈ ⟪ (ℓ "亢亠") ⟫ʷ
wp0347 c4 L = pw1 c4 L (ℓ "举东亢丝") (ℓ "亢亠") tt tt Eq.refl

wp0348 : Base 4 → WsL → ⟪ (ℓ "举丝") ⟫ʷ ≈ ⟪ (ℓ "丝举") ⟫ʷ
wp0348 c4 L = pw1 c4 L (ℓ "举丝") (ℓ "丝举") tt tt Eq.refl

wp0349 : Base 4 → WsL → ⟪ (ℓ "举东") ⟫ʷ ≈ ⟪ (ℓ "东举") ⟫ʷ
wp0349 c4 L = pw1 c4 L (ℓ "举东") (ℓ "东举") tt tt Eq.refl

wp0350 : Base 4 → WsL → ⟪ (ℓ "举么") ⟫ʷ ≈ ⟪ (ℓ "么举") ⟫ʷ
wp0350 c4 L = pw3 c4 L (ℓ "举么") (ℓ "么举") tt tt Eq.refl

wp0351 : Base 4 → WsL → ⟪ (ℓ "亢亢") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0351 c4 L = pw1 c4 L (ℓ "亢亢") [] tt tt Eq.refl

wp0352 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "乹乁乺乁丶") ⟫ʷ
wp0352 c4 L = pw1 c4 L (ℓ "亠") (ℓ "乹乁乺乁丶") tt tt Eq.refl

wp0353 : Base 4 → WsL → ⟪ (ℓ "亠亢") ⟫ʷ ≈ ⟪ (ℓ "亢亠丿") ⟫ʷ
wp0353 c4 L = pw1 c4 L (ℓ "亠亢") (ℓ "亢亠丿") tt tt Eq.refl

wp0354 : Base 4 → WsL → ⟪ (ℓ "亠丿亢亠") ⟫ʷ ≈ ⟪ (ℓ "亢") ⟫ʷ
wp0354 c4 L = pw1 c4 L (ℓ "亠丿亢亠") (ℓ "亢") tt tt Eq.refl

wp0355 : Base 4 → WsL → ⟪ (ℓ "五亗") ⟫ʷ ≈ ⟪ (ℓ "亗五个") ⟫ʷ
wp0355 c4 L = pw2 c4 L (ℓ "五亗") (ℓ "亗五个") tt tt Eq.refl

wp0356 : Base 4 → WsL → ⟪ (ℓ "五个亗五") ⟫ʷ ≈ ⟪ (ℓ "亗") ⟫ʷ
wp0356 c4 L = pw2 c4 L (ℓ "五个亗五") (ℓ "亗") tt tt Eq.refl

wp0357 : Base 4 → WsL → ⟪ (ℓ "亠亃") ⟫ʷ ≈ ⟪ (ℓ "亃亠") ⟫ʷ
wp0357 c4 L = pw2 c4 L (ℓ "亠亃") (ℓ "亃亠") tt tt Eq.refl

wp0358 : Base 4 → WsL → ⟪ (ℓ "两丨亀丩亀乕严") ⟫ʷ ≈ ⟪ (ℓ "亗") ⟫ʷ
wp0358 c4 L = pw2 c4 L (ℓ "两丨亀丩亀乕严") (ℓ "亗") tt tt Eq.refl

wp0359 : Base 4 → WsL → ⟪ (ℓ "二亗") ⟫ʷ ≈ ⟪ (ℓ "亗二") ⟫ʷ
wp0359 c4 L = pw3 c4 L (ℓ "二亗") (ℓ "亗二") tt tt Eq.refl

wp0360 : Base 4 → WsL → ⟪ (ℓ "丳亗") ⟫ʷ ≈ ⟪ (ℓ "亗丳") ⟫ʷ
wp0360 c4 L = pw3 c4 L (ℓ "丳亗") (ℓ "亗丳") tt tt Eq.refl

wp0361 : Base 4 → WsL → ⟪ (ℓ "亰丳亠") ⟫ʷ ≈ ⟪ (ℓ "丳亰") ⟫ʷ
wp0361 c4 L = pw1 c4 L (ℓ "亰丳亠") (ℓ "丳亰") tt tt Eq.refl

wp0362 : Base 4 → WsL → ⟪ (ℓ "亠亗") ⟫ʷ ≈ ⟪ (ℓ "亗亠亐") ⟫ʷ
wp0362 c4 L = pw2 c4 L (ℓ "亠亗") (ℓ "亗亠亐") tt tt Eq.refl

wp0363 : Base 4 → WsL → ⟪ (ℓ "亰丷") ⟫ʷ ≈ ⟪ (ℓ "丷亰") ⟫ʷ
wp0363 c4 L = pw1 c4 L (ℓ "亰丷") (ℓ "丷亰") tt tt Eq.refl

wp0364 : Base 4 → WsL → ⟪ (ℓ "丳亠亠") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
wp0364 c4 L = pw1 c4 L (ℓ "丳亠亠") (ℓ "丳") tt tt Eq.refl

wp0365 : Base 4 → WsL → ⟪ (ℓ "乜亗") ⟫ʷ ≈ ⟪ (ℓ "亗乜享") ⟫ʷ
wp0365 c4 L = pw3 c4 L (ℓ "乜亗") (ℓ "亗乜享") tt tt Eq.refl

wp0366 : Base 4 → WsL → ⟪ (ℓ "亰乜") ⟫ʷ ≈ ⟪ (ℓ "乜亰") ⟫ʷ
wp0366 c4 L = pw1 c4 L (ℓ "亰乜") (ℓ "乜亰") tt tt Eq.refl

wp0367 : Base 4 → WsL → ⟪ (ℓ "乎亗") ⟫ʷ ≈ ⟪ (ℓ "亗乎") ⟫ʷ
wp0367 c4 L = pw2 c4 L (ℓ "乎亗") (ℓ "亗乎") tt tt Eq.refl

wp0368 : Base 4 → WsL → ⟪ (ℓ "之亗") ⟫ʷ ≈ ⟪ (ℓ "亗之") ⟫ʷ
wp0368 c4 L = pw3 c4 L (ℓ "之亗") (ℓ "亗之") tt tt Eq.refl

wp0369 : Base 4 → WsL → ⟪ (ℓ "乜享享") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wp0369 c4 L = pw3 c4 L (ℓ "乜享享") (ℓ "乜") tt tt Eq.refl

wp0370 : Base 4 → WsL → ⟪ (ℓ "串亗") ⟫ʷ ≈ ⟪ (ℓ "享串") ⟫ʷ
wp0370 c4 L = pw3 c4 L (ℓ "串亗") (ℓ "享串") tt tt Eq.refl

wp0371 : Base 4 → WsL → ⟪ (ℓ "串亩") ⟫ʷ ≈ ⟪ (ℓ "亖串") ⟫ʷ
wp0371 c4 L = pw3 c4 L (ℓ "串亩") (ℓ "亖串") tt tt Eq.refl

wp0372 : Base 4 → WsL → ⟪ (ℓ "亠丸乽") ⟫ʷ ≈ ⟪ (ℓ "乽亠") ⟫ʷ
wp0372 c4 L = pw1 c4 L (ℓ "亠丸乽") (ℓ "乽亠") tt tt Eq.refl

wp0373 : Base 4 → WsL → ⟪ (ℓ "亠丸") ⟫ʷ ≈ ⟪ (ℓ "乽亠乽") ⟫ʷ
wp0373 c4 L = pw1 c4 L (ℓ "亠丸") (ℓ "乽亠乽") tt tt Eq.refl

wp0374 : Base 4 → WsL → ⟪ (ℓ "二享") ⟫ʷ ≈ ⟪ (ℓ "享二") ⟫ʷ
wp0374 c4 L = pw3 c4 L (ℓ "二享") (ℓ "享二") tt tt Eq.refl

wp0375 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丸亠丸") ⟫ʷ
wp0375 c4 L = pw1 c4 L (ℓ "亠") (ℓ "丸亠丸") tt tt Eq.refl

wp0376 : Base 4 → WsL → ⟪ (ℓ "五享二") ⟫ʷ ≈ ⟪ (ℓ "享五") ⟫ʷ
wp0376 c4 L = pw3 c4 L (ℓ "五享二") (ℓ "享五") tt tt Eq.refl

wp0377 : Base 4 → WsL → ⟪ (ℓ "亠亓") ⟫ʷ ≈ ⟪ (ℓ "亓亠五") ⟫ʷ
wp0377 c4 L = pw2 c4 L (ℓ "亠亓") (ℓ "亓亠五") tt tt Eq.refl

wp0378 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "丳五丳") ⟫ʷ
wp0378 c4 L = pw3 c4 L (ℓ "五") (ℓ "丳五丳") tt tt Eq.refl

wp0379 : Base 4 → WsL → ⟪ (ℓ "乕亓") ⟫ʷ ≈ ⟪ (ℓ "亓乕") ⟫ʷ
wp0379 c4 L = pw2 c4 L (ℓ "乕亓") (ℓ "亓乕") tt tt Eq.refl

wp0380 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乜亨乜") ⟫ʷ
wp0380 c4 L = pw3 c4 L (ℓ "亨") (ℓ "乜亨乜") tt tt Eq.refl

wp0381 : Base 4 → WsL → ⟪ (ℓ "五乜") ⟫ʷ ≈ ⟪ (ℓ "乜亨五") ⟫ʷ
wp0381 c4 L = pw3 c4 L (ℓ "五乜") (ℓ "乜亨五") tt tt Eq.refl

wp0382 : Base 4 → WsL → ⟪ (ℓ "亨丳") ⟫ʷ ≈ ⟪ (ℓ "丳五亨") ⟫ʷ
wp0382 c4 L = pw3 c4 L (ℓ "亨丳") (ℓ "丳五亨") tt tt Eq.refl

wp0383 : Base 4 → WsL → ⟪ (ℓ "五亨五亨五") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
wp0383 c4 L = pw3 c4 L (ℓ "五亨五亨五") (ℓ "五") tt tt Eq.refl

wp0384 : Base 4 → WsL → ⟪ (ℓ "亨丽") ⟫ʷ ≈ ⟪ (ℓ "丽亨") ⟫ʷ
wp0384 c4 L = pw3 c4 L (ℓ "亨丽") (ℓ "丽亨") tt tt Eq.refl

wp0385 : Base 4 → WsL → ⟪ (ℓ "丽亣") ⟫ʷ ≈ ⟪ (ℓ "亣丽丶亠") ⟫ʷ
wp0385 c4 L = pw1 c4 L (ℓ "丽亣") (ℓ "亣丽丶亠") tt tt Eq.refl

wp0386 : Base 4 → WsL → ⟪ (ℓ "丶亣") ⟫ʷ ≈ ⟪ (ℓ "亣丶") ⟫ʷ
wp0386 c4 L = pw1 c4 L (ℓ "丶亣") (ℓ "亣丶") tt tt Eq.refl

wp0387 : Base 4 → WsL → ⟪ (ℓ "丽丶亠丶丸亠") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
wp0387 c4 L = pw1 c4 L (ℓ "丽丶亠丶丸亠") (ℓ "丽") tt tt Eq.refl

wp0388 : Base 4 → WsL → ⟪ (ℓ "亠亓五") ⟫ʷ ≈ ⟪ (ℓ "亓亠") ⟫ʷ
wp0388 c4 L = pw2 c4 L (ℓ "亠亓五") (ℓ "亓亠") tt tt Eq.refl

wp0389 : Base 4 → WsL → ⟪ (ℓ "亨乜") ⟫ʷ ≈ ⟪ (ℓ "乜亨") ⟫ʷ
wp0389 c4 L = pw3 c4 L (ℓ "亨乜") (ℓ "乜亨") tt tt Eq.refl

wp0390 : Base 4 → WsL → ⟪ (ℓ "亨五亨五亨") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp0390 c4 L = pw3 c4 L (ℓ "亨五亨五亨") (ℓ "亨") tt tt Eq.refl

wp0391 : Base 4 → WsL → ⟪ (ℓ "五享") ⟫ʷ ≈ ⟪ (ℓ "享二五") ⟫ʷ
wp0391 c4 L = pw3 c4 L (ℓ "五享") (ℓ "享二五") tt tt Eq.refl

wp0392 : Base 4 → WsL → ⟪ (ℓ "亐争五") ⟫ʷ ≈ ⟪ (ℓ "争亐") ⟫ʷ
wp0392 c4 L = pw2 c4 L (ℓ "亐争五") (ℓ "争亐") tt tt Eq.refl

wp0393 : Base 4 → WsL → ⟪ (ℓ "丽亲") ⟫ʷ ≈ ⟪ (ℓ "亲丽") ⟫ʷ
wp0393 c4 L = pw1 c4 L (ℓ "丽亲") (ℓ "亲丽") tt tt Eq.refl

wp0394 : Base 4 → WsL → ⟪ (ℓ "亐五") ⟫ʷ ≈ ⟪ (ℓ "五亐") ⟫ʷ
wp0394 c4 L = pw2 c4 L (ℓ "亐五") (ℓ "五亐") tt tt Eq.refl

wp0395 : Base 4 → WsL → ⟪ (ℓ "争五五") ⟫ʷ ≈ ⟪ (ℓ "争") ⟫ʷ
wp0395 c4 L = pw2 c4 L (ℓ "争五五") (ℓ "争") tt tt Eq.refl

wp0396 : Base 4 → WsL → ⟪ (ℓ "丽争") ⟫ʷ ≈ ⟪ (ℓ "争丽") ⟫ʷ
wp0396 c4 L = pw1 c4 L (ℓ "丽争") (ℓ "争丽") tt tt Eq.refl

wp0397 : Base 4 → WsL → ⟪ (ℓ "举争") ⟫ʷ ≈ ⟪ (ℓ "争举") ⟫ʷ
wp0397 c4 L = pw1 c4 L (ℓ "举争") (ℓ "争举") tt tt Eq.refl

wp0398 : Base 4 → WsL → ⟪ (ℓ "五乼") ⟫ʷ ≈ ⟪ (ℓ "乼亐") ⟫ʷ
wp0398 c4 L = pw2 c4 L (ℓ "五乼") (ℓ "乼亐") tt tt Eq.refl

wp0399 : Base 4 → WsL → ⟪ (ℓ "乼亓") ⟫ʷ ≈ ⟪ (ℓ "亗乼") ⟫ʷ
wp0399 c4 L = pw2 c4 L (ℓ "乼亓") (ℓ "亗乼") tt tt Eq.refl

wp0400 : Base 4 → WsL → ⟪ (ℓ "亜亝丸亝亜丸乼") ⟫ʷ ≈ ⟪ (ℓ "乼亘亙丿亙亘丿") ⟫ʷ
wp0400 c4 L = pw1 c4 L (ℓ "亜亝丸亝亜丸乼") (ℓ "乼亘亙丿亙亘丿") tt tt Eq.refl

wp0401 : Base 4 → WsL → ⟪ (ℓ "丶乼") ⟫ʷ ≈ ⟪ (ℓ "乼丽") ⟫ʷ
wp0401 c4 L = pw1 c4 L (ℓ "丶乼") (ℓ "乼丽") tt tt Eq.refl

wp0402 : Base 4 → WsL → ⟪ (ℓ "丷乼") ⟫ʷ ≈ ⟪ (ℓ "乼举") ⟫ʷ
wp0402 c4 L = pw1 c4 L (ℓ "丷乼") (ℓ "乼举") tt tt Eq.refl

wp0403 : Base 4 → WsL → ⟪ (ℓ "丽並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並丽") ⟫ʷ
wp0403 c4 L = pw1 c4 L (ℓ "丽並丢並") (ℓ "並丢並丽") tt tt Eq.refl

wp0404 : Base 4 → WsL → ⟪ (ℓ "亁並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亁") ⟫ʷ
wp0404 c4 L = pw1 c4 L (ℓ "亁並丢並") (ℓ "並丢並亁") tt tt Eq.refl

wp0405 : Base 4 → WsL → ⟪ (ℓ "亜並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亜") ⟫ʷ
wp0405 c4 L = pw1 c4 L (ℓ "亜並丢並") (ℓ "並丢並亜") tt tt Eq.refl

wp0406 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亮丶亮丷") ⟫ʷ
wp0406 c4 L = pw2 c4 L (ℓ "亮丶亮丷並丢並") (ℓ "並丢並亮丶亮丷") tt tt Eq.refl

wp0407 : Base 4 → WsL → ⟪ (ℓ "五並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並五") ⟫ʷ
wp0407 c4 L = pw2 c4 L (ℓ "五並丢並") (ℓ "並丢並五") tt tt Eq.refl

wp0408 : Base 4 → WsL → ⟪ (ℓ "亙並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亙") ⟫ʷ
wp0408 c4 L = pw1 c4 L (ℓ "亙並丢並") (ℓ "並丢並亙") tt tt Eq.refl

wp0409 : Base 4 → WsL → ⟪ (ℓ "云並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並云") ⟫ʷ
wp0409 c4 L = pw2 c4 L (ℓ "云並丢並") (ℓ "並丢並云") tt tt Eq.refl

wp0410 : Base 4 → WsL → ⟪ (ℓ "丢並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並丢") ⟫ʷ
wp0410 c4 L = pw1 c4 L (ℓ "丢並丽並") (ℓ "並丽並丢") tt tt Eq.refl

wp0411 : Base 4 → WsL → ⟪ (ℓ "丽並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並丽") ⟫ʷ
wp0411 c4 L = pw1 c4 L (ℓ "丽並丽並") (ℓ "並丽並丽") tt tt Eq.refl

wp0412 : Base 4 → WsL → ⟪ (ℓ "乕並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並乕") ⟫ʷ
wp0412 c4 L = pw2 c4 L (ℓ "乕並丽並") (ℓ "並丽並乕") tt tt Eq.refl

wp0413 : Base 4 → WsL → ⟪ (ℓ "乩並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並乩") ⟫ʷ
wp0413 c4 L = pw1 c4 L (ℓ "乩並丽並") (ℓ "並丽並乩") tt tt Eq.refl

wp0414 : Base 4 → WsL → ⟪ (ℓ "乹並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並乹") ⟫ʷ
wp0414 c4 L = pw1 c4 L (ℓ "乹並丽並") (ℓ "並丽並乹") tt tt Eq.refl

wp0415 : Base 4 → WsL → ⟪ (ℓ "亁並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亁") ⟫ʷ
wp0415 c4 L = pw1 c4 L (ℓ "亁並丽並") (ℓ "並丽並亁") tt tt Eq.refl

wp0416 : Base 4 → WsL → ⟪ (ℓ "亄並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亄") ⟫ʷ
wp0416 c4 L = pw2 c4 L (ℓ "亄並丽並") (ℓ "並丽並亄") tt tt Eq.refl

wp0417 : Base 4 → WsL → ⟪ (ℓ "亇並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亇") ⟫ʷ
wp0417 c4 L = pw1 c4 L (ℓ "亇並丽並") (ℓ "並丽並亇") tt tt Eq.refl

wp0418 : Base 4 → WsL → ⟪ (ℓ "亊並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亊") ⟫ʷ
wp0418 c4 L = pw1 c4 L (ℓ "亊並丽並") (ℓ "並丽並亊") tt tt Eq.refl

wp0419 : Base 4 → WsL → ⟪ (ℓ "亜並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亜") ⟫ʷ
wp0419 c4 L = pw1 c4 L (ℓ "亜並丽並") (ℓ "並丽並亜") tt tt Eq.refl

wp0420 : Base 4 → WsL → ⟪ (ℓ "亜上举") ⟫ʷ ≈ ⟪ (ℓ "上举亜") ⟫ʷ
wp0420 c4 L = pw1 c4 L (ℓ "亜上举") (ℓ "上举亜") tt tt Eq.refl

wp0421 : Base 4 → WsL → ⟪ (ℓ "上举亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷上举") ⟫ʷ
wp0421 c4 L = pw2 c4 L (ℓ "上举亮丶亮丷") (ℓ "亮丶亮丷上举") tt tt Eq.refl

wp0422 : Base 4 → WsL → ⟪ (ℓ "举井") ⟫ʷ ≈ ⟪ (ℓ "井举乖五") ⟫ʷ
wp0422 c4 L = pw2 c4 L (ℓ "举井") (ℓ "井举乖五") tt tt Eq.refl

wp0423 : Base 4 → WsL → ⟪ (ℓ "乖井") ⟫ʷ ≈ ⟪ (ℓ "井乖") ⟫ʷ
wp0423 c4 L = pw2 c4 L (ℓ "乖井") (ℓ "井乖") tt tt Eq.refl

wp0424 : Base 4 → WsL → ⟪ (ℓ "举乖五乖乗五") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp0424 c4 L = pw2 c4 L (ℓ "举乖五乖乗五") (ℓ "举") tt tt Eq.refl

wp0425 : Base 4 → WsL → ⟪ (ℓ "上井") ⟫ʷ ≈ ⟪ (ℓ "井上乕五") ⟫ʷ
wp0425 c4 L = pw2 c4 L (ℓ "上井") (ℓ "井上乕五") tt tt Eq.refl

wp0426 : Base 4 → WsL → ⟪ (ℓ "乕井") ⟫ʷ ≈ ⟪ (ℓ "井乕") ⟫ʷ
wp0426 c4 L = pw2 c4 L (ℓ "乕井") (ℓ "井乕") tt tt Eq.refl

wp0427 : Base 4 → WsL → ⟪ (ℓ "上乕五乕乗五") ⟫ʷ ≈ ⟪ (ℓ "上") ⟫ʷ
wp0427 c4 L = pw2 c4 L (ℓ "上乕五乕乗五") (ℓ "上") tt tt Eq.refl

wp0428 : Base 4 → WsL → ⟪ (ℓ "亲並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亲") ⟫ʷ
wp0428 c4 L = pw1 c4 L (ℓ "亲並丽並") (ℓ "並丽並亲") tt tt Eq.refl

wp0429 : Base 4 → WsL → ⟪ (ℓ "乎並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並乎") ⟫ʷ
wp0429 c4 L = pw2 c4 L (ℓ "乎並丽並") (ℓ "並丽並乎") tt tt Eq.refl

wp0430 : Base 4 → WsL → ⟪ (ℓ "乏並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並乏") ⟫ʷ
wp0430 c4 L = pw2 c4 L (ℓ "乏並丽並") (ℓ "並丽並乏") tt tt Eq.refl

wp0431 : Base 4 → WsL → ⟪ (ℓ "举亝") ⟫ʷ ≈ ⟪ (ℓ "亝举乪亜") ⟫ʷ
wp0431 c4 L = pw1 c4 L (ℓ "举亝") (ℓ "亝举乪亜") tt tt Eq.refl

wp0432 : Base 4 → WsL → ⟪ (ℓ "乪亝") ⟫ʷ ≈ ⟪ (ℓ "亝乪") ⟫ʷ
wp0432 c4 L = pw1 c4 L (ℓ "乪亝") (ℓ "亝乪") tt tt Eq.refl

wp0433 : Base 4 → WsL → ⟪ (ℓ "举乪亜乪乫亜") ⟫ʷ ≈ ⟪ (ℓ "举") ⟫ʷ
wp0433 c4 L = pw1 c4 L (ℓ "举乪亜乪乫亜") (ℓ "举") tt tt Eq.refl

wp0434 : Base 4 → WsL → ⟪ (ℓ "上亝") ⟫ʷ ≈ ⟪ (ℓ "亝上乩亜") ⟫ʷ
wp0434 c4 L = pw1 c4 L (ℓ "上亝") (ℓ "亝上乩亜") tt tt Eq.refl

wp0435 : Base 4 → WsL → ⟪ (ℓ "乩亝") ⟫ʷ ≈ ⟪ (ℓ "亝乩") ⟫ʷ
wp0435 c4 L = pw1 c4 L (ℓ "乩亝") (ℓ "亝乩") tt tt Eq.refl

wp0436 : Base 4 → WsL → ⟪ (ℓ "上乩亜乩乫亜") ⟫ʷ ≈ ⟪ (ℓ "上") ⟫ʷ
wp0436 c4 L = pw1 c4 L (ℓ "上乩亜乩乫亜") (ℓ "上") tt tt Eq.refl

wp0437 : Base 4 → WsL → ⟪ (ℓ "亭並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並亭") ⟫ʷ
wp0437 c4 L = pw2 c4 L (ℓ "亭並丽並") (ℓ "並丽並亭") tt tt Eq.refl

wp0438 : Base 4 → WsL → ⟪ (ℓ "乇並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並乇") ⟫ʷ
wp0438 c4 L = pw3 c4 L (ℓ "乇並丽並") (ℓ "並丽並乇") tt tt Eq.refl

wp0439 : Base 4 → WsL → ⟪ (ℓ "么並丽並") ⟫ʷ ≈ ⟪ (ℓ "並丽並么") ⟫ʷ
wp0439 c4 L = pw3 c4 L (ℓ "么並丽並") (ℓ "並丽並么") tt tt Eq.refl

wp0440 : Base 4 → WsL → ⟪ (ℓ "丽並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並丽") ⟫ʷ
wp0440 c4 L = pw2 c4 L (ℓ "丽並乕並") (ℓ "並乕並丽") tt tt Eq.refl

wp0441 : Base 4 → WsL → ⟪ (ℓ "亁並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亁") ⟫ʷ
wp0441 c4 L = pw2 c4 L (ℓ "亁並乕並") (ℓ "並乕並亁") tt tt Eq.refl

wp0442 : Base 4 → WsL → ⟪ (ℓ "亜並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亜") ⟫ʷ
wp0442 c4 L = pw3 c4 L (ℓ "亜並乕並") (ℓ "並乕並亜") tt tt Eq.refl

wp0443 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亮丶亮丷") ⟫ʷ
wp0443 c4 L = pw2 c4 L (ℓ "亮丶亮丷並乕並") (ℓ "並乕並亮丶亮丷") tt tt Eq.refl

wp0444 : Base 4 → WsL → ⟪ (ℓ "五並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並五") ⟫ʷ
wp0444 c4 L = pw2 c4 L (ℓ "五並乕並") (ℓ "並乕並五") tt tt Eq.refl

wp0445 : Base 4 → WsL → ⟪ (ℓ "五丐乖") ⟫ʷ ≈ ⟪ (ℓ "丐乖五") ⟫ʷ
wp0445 c4 L = pw2 c4 L (ℓ "五丐乖") (ℓ "丐乖五") tt tt Eq.refl

wp0446 : Base 4 → WsL → ⟪ (ℓ "云並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並云") ⟫ʷ
wp0446 c4 L = pw2 c4 L (ℓ "云並乕並") (ℓ "並乕並云") tt tt Eq.refl

wp0447 : Base 4 → WsL → ⟪ (ℓ "丽並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並丽") ⟫ʷ
wp0447 c4 L = pw1 c4 L (ℓ "丽並乩並") (ℓ "並乩並丽") tt tt Eq.refl

wp0448 : Base 4 → WsL → ⟪ (ℓ "亁並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亁") ⟫ʷ
wp0448 c4 L = pw1 c4 L (ℓ "亁並乩並") (ℓ "並乩並亁") tt tt Eq.refl

wp0449 : Base 4 → WsL → ⟪ (ℓ "乪亞") ⟫ʷ ≈ ⟪ (ℓ "亞乪举亜") ⟫ʷ
wp0449 c4 L = pw1 c4 L (ℓ "乪亞") (ℓ "亞乪举亜") tt tt Eq.refl

wp0450 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丽乜举乜乩") ⟫ʷ
wp0450 c4 L = pw3 c4 L (ℓ "亜") (ℓ "丽乜举乜乩") tt tt Eq.refl

wp0451 : Base 4 → WsL → ⟪ (ℓ "举亞") ⟫ʷ ≈ ⟪ (ℓ "亞举") ⟫ʷ
wp0451 c4 L = pw1 c4 L (ℓ "举亞") (ℓ "亞举") tt tt Eq.refl

wp0452 : Base 4 → WsL → ⟪ (ℓ "乪举亜举丿亜") ⟫ʷ ≈ ⟪ (ℓ "乪") ⟫ʷ
wp0452 c4 L = pw1 c4 L (ℓ "乪举亜举丿亜") (ℓ "乪") tt tt Eq.refl

wp0453 : Base 4 → WsL → ⟪ (ℓ "世亞") ⟫ʷ ≈ ⟪ (ℓ "亞世丽亜") ⟫ʷ
wp0453 c4 L = pw1 c4 L (ℓ "世亞") (ℓ "亞世丽亜") tt tt Eq.refl

wp0454 : Base 4 → WsL → ⟪ (ℓ "丽亞") ⟫ʷ ≈ ⟪ (ℓ "亞丽") ⟫ʷ
wp0454 c4 L = pw1 c4 L (ℓ "丽亞") (ℓ "亞丽") tt tt Eq.refl

wp0455 : Base 4 → WsL → ⟪ (ℓ "世丽亜丽丿亜") ⟫ʷ ≈ ⟪ (ℓ "世") ⟫ʷ
wp0455 c4 L = pw1 c4 L (ℓ "世丽亜丽丿亜") (ℓ "世") tt tt Eq.refl

wp0456 : Base 4 → WsL → ⟪ (ℓ "丶並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並丶") ⟫ʷ
wp0456 c4 L = pw1 c4 L (ℓ "丶並乩並") (ℓ "並乩並丶") tt tt Eq.refl

wp0457 : Base 4 → WsL → ⟪ (ℓ "丷並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並丷") ⟫ʷ
wp0457 c4 L = pw1 c4 L (ℓ "丷並乩並") (ℓ "並乩並丷") tt tt Eq.refl

wp0458 : Base 4 → WsL → ⟪ (ℓ "五並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並五") ⟫ʷ
wp0458 c4 L = pw3 c4 L (ℓ "五並乩並") (ℓ "並乩並五") tt tt Eq.refl

wp0459 : Base 4 → WsL → ⟪ (ℓ "亙並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亙") ⟫ʷ
wp0459 c4 L = pw1 c4 L (ℓ "亙並乩並") (ℓ "並乩並亙") tt tt Eq.refl

wp0460 : Base 4 → WsL → ⟪ (ℓ "亜並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亜") ⟫ʷ
wp0460 c4 L = pw1 c4 L (ℓ "亜並乩並") (ℓ "並乩並亜") tt tt Eq.refl

wp0461 : Base 4 → WsL → ⟪ (ℓ "亜世乪") ⟫ʷ ≈ ⟪ (ℓ "世乪亜") ⟫ʷ
wp0461 c4 L = pw1 c4 L (ℓ "亜世乪") (ℓ "世乪亜") tt tt Eq.refl

wp0462 : Base 4 → WsL → ⟪ (ℓ "丽並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並丽") ⟫ʷ
wp0462 c4 L = pw1 c4 L (ℓ "丽並乹並") (ℓ "並乹並丽") tt tt Eq.refl

wp0463 : Base 4 → WsL → ⟪ (ℓ "亁並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亁") ⟫ʷ
wp0463 c4 L = pw1 c4 L (ℓ "亁並乹並") (ℓ "並乹並亁") tt tt Eq.refl

wp0464 : Base 4 → WsL → ⟪ (ℓ "亜並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亜") ⟫ʷ
wp0464 c4 L = pw1 c4 L (ℓ "亜並乹並") (ℓ "並乹並亜") tt tt Eq.refl

wp0465 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亮丶亮丷") ⟫ʷ
wp0465 c4 L = pw2 c4 L (ℓ "亮丶亮丷並乹並") (ℓ "並乹並亮丶亮丷") tt tt Eq.refl

wp0466 : Base 4 → WsL → ⟪ (ℓ "五並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並五") ⟫ʷ
wp0466 c4 L = pw2 c4 L (ℓ "五並乹並") (ℓ "並乹並五") tt tt Eq.refl

wp0467 : Base 4 → WsL → ⟪ (ℓ "亙並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亙") ⟫ʷ
wp0467 c4 L = pw1 c4 L (ℓ "亙並乹並") (ℓ "並乹並亙") tt tt Eq.refl

wp0468 : Base 4 → WsL → ⟪ (ℓ "云並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並云") ⟫ʷ
wp0468 c4 L = pw2 c4 L (ℓ "云並乹並") (ℓ "並乹並云") tt tt Eq.refl

wp0469 : Base 4 → WsL → ⟪ (ℓ "丢並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並丢") ⟫ʷ
wp0469 c4 L = pw1 c4 L (ℓ "丢並亁並") (ℓ "並亁並丢") tt tt Eq.refl

wp0470 : Base 4 → WsL → ⟪ (ℓ "丽並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並丽") ⟫ʷ
wp0470 c4 L = pw1 c4 L (ℓ "丽並亁並") (ℓ "並亁並丽") tt tt Eq.refl

wp0471 : Base 4 → WsL → ⟪ (ℓ "乕並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並乕") ⟫ʷ
wp0471 c4 L = pw2 c4 L (ℓ "乕並亁並") (ℓ "並亁並乕") tt tt Eq.refl

wp0472 : Base 4 → WsL → ⟪ (ℓ "乩並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並乩") ⟫ʷ
wp0472 c4 L = pw1 c4 L (ℓ "乩並亁並") (ℓ "並亁並乩") tt tt Eq.refl

wp0473 : Base 4 → WsL → ⟪ (ℓ "乹並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並乹") ⟫ʷ
wp0473 c4 L = pw1 c4 L (ℓ "乹並亁並") (ℓ "並亁並乹") tt tt Eq.refl
