------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP03 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wp0474 : Base 4 → WsL → ⟪ (ℓ "亁並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亁") ⟫ʷ
wp0474 c4 L = pw1 c4 L (ℓ "亁並亁並") (ℓ "並亁並亁") tt tt Eq.refl

wp0475 : Base 4 → WsL → ⟪ (ℓ "亄並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亄") ⟫ʷ
wp0475 c4 L = pw2 c4 L (ℓ "亄並亁並") (ℓ "並亁並亄") tt tt Eq.refl

wp0476 : Base 4 → WsL → ⟪ (ℓ "亇並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亇") ⟫ʷ
wp0476 c4 L = pw1 c4 L (ℓ "亇並亁並") (ℓ "並亁並亇") tt tt Eq.refl

wp0477 : Base 4 → WsL → ⟪ (ℓ "亊並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亊") ⟫ʷ
wp0477 c4 L = pw1 c4 L (ℓ "亊並亁並") (ℓ "並亁並亊") tt tt Eq.refl

wp0478 : Base 4 → WsL → ⟪ (ℓ "亜並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亜") ⟫ʷ
wp0478 c4 L = pw1 c4 L (ℓ "亜並亁並") (ℓ "並亁並亜") tt tt Eq.refl

wp0479 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亮丶亮丷") ⟫ʷ
wp0479 c4 L = pw2 c4 L (ℓ "亮丶亮丷並亁並") (ℓ "並亁並亮丶亮丷") tt tt Eq.refl

wp0480 : Base 4 → WsL → ⟪ (ℓ "丽井") ⟫ʷ ≈ ⟪ (ℓ "井丽乕五") ⟫ʷ
wp0480 c4 L = pw2 c4 L (ℓ "丽井") (ℓ "井丽乕五") tt tt Eq.refl

wp0481 : Base 4 → WsL → ⟪ (ℓ "丽乕五乕乗五") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
wp0481 c4 L = pw2 c4 L (ℓ "丽乕五乕乗五") (ℓ "丽") tt tt Eq.refl

wp0482 : Base 4 → WsL → ⟪ (ℓ "五丌") ⟫ʷ ≈ ⟪ (ℓ "丌井") ⟫ʷ
wp0482 c4 L = pw2 c4 L (ℓ "五丌") (ℓ "丌井") tt tt Eq.refl

wp0483 : Base 4 → WsL → ⟪ (ℓ "五不") ⟫ʷ ≈ ⟪ (ℓ "不井") ⟫ʷ
wp0483 c4 L = pw2 c4 L (ℓ "五不") (ℓ "不井") tt tt Eq.refl

wp0484 : Base 4 → WsL → ⟪ (ℓ "亲並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亲") ⟫ʷ
wp0484 c4 L = pw1 c4 L (ℓ "亲並亁並") (ℓ "並亁並亲") tt tt Eq.refl

wp0485 : Base 4 → WsL → ⟪ (ℓ "乎並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並乎") ⟫ʷ
wp0485 c4 L = pw2 c4 L (ℓ "乎並亁並") (ℓ "並亁並乎") tt tt Eq.refl

wp0486 : Base 4 → WsL → ⟪ (ℓ "乏並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並乏") ⟫ʷ
wp0486 c4 L = pw2 c4 L (ℓ "乏並亁並") (ℓ "並亁並乏") tt tt Eq.refl

wp0487 : Base 4 → WsL → ⟪ (ℓ "丽亝") ⟫ʷ ≈ ⟪ (ℓ "亝丽乩亜") ⟫ʷ
wp0487 c4 L = pw1 c4 L (ℓ "丽亝") (ℓ "亝丽乩亜") tt tt Eq.refl

wp0488 : Base 4 → WsL → ⟪ (ℓ "丽乩亜乩乫亜") ⟫ʷ ≈ ⟪ (ℓ "丽") ⟫ʷ
wp0488 c4 L = pw1 c4 L (ℓ "丽乩亜乩乫亜") (ℓ "丽") tt tt Eq.refl

wp0489 : Base 4 → WsL → ⟪ (ℓ "亜丌") ⟫ʷ ≈ ⟪ (ℓ "丌亝") ⟫ʷ
wp0489 c4 L = pw1 c4 L (ℓ "亜丌") (ℓ "丌亝") tt tt Eq.refl

wp0490 : Base 4 → WsL → ⟪ (ℓ "亜不") ⟫ʷ ≈ ⟪ (ℓ "不亝") ⟫ʷ
wp0490 c4 L = pw1 c4 L (ℓ "亜不") (ℓ "不亝") tt tt Eq.refl

wp0491 : Base 4 → WsL → ⟪ (ℓ "亭並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並亭") ⟫ʷ
wp0491 c4 L = pw2 c4 L (ℓ "亭並亁並") (ℓ "並亁並亭") tt tt Eq.refl

wp0492 : Base 4 → WsL → ⟪ (ℓ "乇並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並乇") ⟫ʷ
wp0492 c4 L = pw3 c4 L (ℓ "乇並亁並") (ℓ "並亁並乇") tt tt Eq.refl

wp0493 : Base 4 → WsL → ⟪ (ℓ "么並亁並") ⟫ʷ ≈ ⟪ (ℓ "並亁並么") ⟫ʷ
wp0493 c4 L = pw3 c4 L (ℓ "么並亁並") (ℓ "並亁並么") tt tt Eq.refl

wp0494 : Base 4 → WsL → ⟪ (ℓ "丽並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並丽") ⟫ʷ
wp0494 c4 L = pw2 c4 L (ℓ "丽並亄並") (ℓ "並亄並丽") tt tt Eq.refl

wp0495 : Base 4 → WsL → ⟪ (ℓ "亁並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亁") ⟫ʷ
wp0495 c4 L = pw2 c4 L (ℓ "亁並亄並") (ℓ "並亄並亁") tt tt Eq.refl

wp0496 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丯亀丰亀乩") ⟫ʷ
wp0496 c4 L = pw3 c4 L (ℓ "亜") (ℓ "丯亀丰亀乩") tt tt Eq.refl

wp0497 : Base 4 → WsL → ⟪ (ℓ "丬亞") ⟫ʷ ≈ ⟪ (ℓ "亞丬") ⟫ʷ
wp0497 c4 L = pw3 c4 L (ℓ "丬亞") (ℓ "亞丬") tt tt Eq.refl

wp0498 : Base 4 → WsL → ⟪ (ℓ "亘亞") ⟫ʷ ≈ ⟪ (ℓ "亞亘亠") ⟫ʷ
wp0498 c4 L = pw1 c4 L (ℓ "亘亞") (ℓ "亞亘亠") tt tt Eq.refl

wp0499 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丬亠丬") ⟫ʷ
wp0499 c4 L = pw2 c4 L (ℓ "亠") (ℓ "丬亠丬") tt tt Eq.refl

wp0500 : Base 4 → WsL → ⟪ (ℓ "乄亞") ⟫ʷ ≈ ⟪ (ℓ "亞乄亪") ⟫ʷ
wp0500 c4 L = pw3 c4 L (ℓ "乄亞") (ℓ "亞乄亪") tt tt Eq.refl

wp0501 : Base 4 → WsL → ⟪ (ℓ "乹亞") ⟫ʷ ≈ ⟪ (ℓ "亞乹") ⟫ʷ
wp0501 c4 L = pw1 c4 L (ℓ "乹亞") (ℓ "亞乹") tt tt Eq.refl

wp0502 : Base 4 → WsL → ⟪ (ℓ "亃亞") ⟫ʷ ≈ ⟪ (ℓ "亞亃") ⟫ʷ
wp0502 c4 L = pw3 c4 L (ℓ "亃亞") (ℓ "亞亃") tt tt Eq.refl

wp0503 : Base 4 → WsL → ⟪ (ℓ "亞亪") ⟫ʷ ≈ ⟪ (ℓ "亪亞") ⟫ʷ
wp0503 c4 L = pw3 c4 L (ℓ "亞亪") (ℓ "亪亞") tt tt Eq.refl

wp0504 : Base 4 → WsL → ⟪ (ℓ "乄亪亪") ⟫ʷ ≈ ⟪ (ℓ "乄") ⟫ʷ
wp0504 c4 L = pw3 c4 L (ℓ "乄亪亪") (ℓ "乄") tt tt Eq.refl

wp0505 : Base 4 → WsL → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乄京乄") ⟫ʷ
wp0505 c4 L = pw2 c4 L (ℓ "京") (ℓ "乄京乄") tt tt Eq.refl

wp0506 : Base 4 → WsL → ⟪ (ℓ "亠乄") ⟫ʷ ≈ ⟪ (ℓ "乄京亠") ⟫ʷ
wp0506 c4 L = pw2 c4 L (ℓ "亠乄") (ℓ "乄京亠") tt tt Eq.refl

wp0507 : Base 4 → WsL → ⟪ (ℓ "京丬") ⟫ʷ ≈ ⟪ (ℓ "丬亠京") ⟫ʷ
wp0507 c4 L = pw2 c4 L (ℓ "京丬") (ℓ "丬亠京") tt tt Eq.refl

wp0508 : Base 4 → WsL → ⟪ (ℓ "亠京亠京亠") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0508 c4 L = pw2 c4 L (ℓ "亠京亠京亠") (ℓ "亠") tt tt Eq.refl

wp0509 : Base 4 → WsL → ⟪ (ℓ "亨丫") ⟫ʷ ≈ ⟪ (ℓ "丫亜") ⟫ʷ
wp0509 c4 L = pw3 c4 L (ℓ "亨丫") (ℓ "丫亜") tt tt Eq.refl

wp0510 : Base 4 → WsL → ⟪ (ℓ "丫亞") ⟫ʷ ≈ ⟪ (ℓ "亪丫") ⟫ʷ
wp0510 c4 L = pw3 c4 L (ℓ "丫亞") (ℓ "亪丫") tt tt Eq.refl

wp0511 : Base 4 → WsL → ⟪ (ℓ "亜丫") ⟫ʷ ≈ ⟪ (ℓ "丫亨") ⟫ʷ
wp0511 c4 L = pw3 c4 L (ℓ "亜丫") (ℓ "丫亨") tt tt Eq.refl

wp0512 : Base 4 → WsL → ⟪ (ℓ "丫享") ⟫ʷ ≈ ⟪ (ℓ "亟丫") ⟫ʷ
wp0512 c4 L = pw3 c4 L (ℓ "丫享") (ℓ "亟丫") tt tt Eq.refl

wp0513 : Base 4 → WsL → ⟪ (ℓ "亘乩") ⟫ʷ ≈ ⟪ (ℓ "乩亘") ⟫ʷ
wp0513 c4 L = pw1 c4 L (ℓ "亘乩") (ℓ "乩亘") tt tt Eq.refl

wp0514 : Base 4 → WsL → ⟪ (ℓ "丷乖") ⟫ʷ ≈ ⟪ (ℓ "乖丷") ⟫ʷ
wp0514 c4 L = pw2 c4 L (ℓ "丷乖") (ℓ "乖丷") tt tt Eq.refl

wp0515 : Base 4 → WsL → ⟪ (ℓ "亨丯") ⟫ʷ ≈ ⟪ (ℓ "丯亨") ⟫ʷ
wp0515 c4 L = pw3 c4 L (ℓ "亨丯") (ℓ "丯亨") tt tt Eq.refl

wp0516 : Base 4 → WsL → ⟪ (ℓ "亜亝个亝亜个") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp0516 c4 L = pw3 c4 L (ℓ "亜亝个亝亜个") (ℓ "亨") tt tt Eq.refl

wp0517 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亮丶亮丷") ⟫ʷ
wp0517 c4 L = pw2 c4 L (ℓ "亮丶亮丷並亄並") (ℓ "並亄並亮丶亮丷") tt tt Eq.refl

wp0518 : Base 4 → WsL → ⟪ (ℓ "五並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並五") ⟫ʷ
wp0518 c4 L = pw2 c4 L (ℓ "五並亄並") (ℓ "並亄並五") tt tt Eq.refl

wp0519 : Base 4 → WsL → ⟪ (ℓ "争亝") ⟫ʷ ≈ ⟪ (ℓ "亝争") ⟫ʷ
wp0519 c4 L = pw1 c4 L (ℓ "争亝") (ℓ "亝争") tt tt Eq.refl

wp0520 : Base 4 → WsL → ⟪ (ℓ "五亝") ⟫ʷ ≈ ⟪ (ℓ "亝五亨") ⟫ʷ
wp0520 c4 L = pw3 c4 L (ℓ "五亝") (ℓ "亝五亨") tt tt Eq.refl

wp0521 : Base 4 → WsL → ⟪ (ℓ "亐乖") ⟫ʷ ≈ ⟪ (ℓ "乖亐") ⟫ʷ
wp0521 c4 L = pw2 c4 L (ℓ "亐乖") (ℓ "乖亐") tt tt Eq.refl

wp0522 : Base 4 → WsL → ⟪ (ℓ "乽亝") ⟫ʷ ≈ ⟪ (ℓ "亝乽亙") ⟫ʷ
wp0522 c4 L = pw1 c4 L (ℓ "乽亝") (ℓ "亝乽亙") tt tt Eq.refl

wp0523 : Base 4 → WsL → ⟪ (ℓ "亐乽") ⟫ʷ ≈ ⟪ (ℓ "乽亐") ⟫ʷ
wp0523 c4 L = pw2 c4 L (ℓ "亐乽") (ℓ "乽亐") tt tt Eq.refl

wp0524 : Base 4 → WsL → ⟪ (ℓ "乇亝") ⟫ʷ ≈ ⟪ (ℓ "亝乇") ⟫ʷ
wp0524 c4 L = pw3 c4 L (ℓ "乇亝") (ℓ "亝乇") tt tt Eq.refl

wp0525 : Base 4 → WsL → ⟪ (ℓ "书亝") ⟫ʷ ≈ ⟪ (ℓ "亝书") ⟫ʷ
wp0525 c4 L = pw1 c4 L (ℓ "书亝") (ℓ "亝书") tt tt Eq.refl

wp0526 : Base 4 → WsL → ⟪ (ℓ "乽亙亙") ⟫ʷ ≈ ⟪ (ℓ "乽") ⟫ʷ
wp0526 c4 L = pw1 c4 L (ℓ "乽亙亙") (ℓ "乽") tt tt Eq.refl

wp0527 : Base 4 → WsL → ⟪ (ℓ "亘乼") ⟫ʷ ≈ ⟪ (ℓ "乼亜") ⟫ʷ
wp0527 c4 L = pw1 c4 L (ℓ "亘乼") (ℓ "乼亜") tt tt Eq.refl

wp0528 : Base 4 → WsL → ⟪ (ℓ "乼亝") ⟫ʷ ≈ ⟪ (ℓ "亙乼") ⟫ʷ
wp0528 c4 L = pw1 c4 L (ℓ "乼亝") (ℓ "亙乼") tt tt Eq.refl

wp0529 : Base 4 → WsL → ⟪ (ℓ "亜乼") ⟫ʷ ≈ ⟪ (ℓ "乼亘") ⟫ʷ
wp0529 c4 L = pw1 c4 L (ℓ "亜乼") (ℓ "乼亘") tt tt Eq.refl

wp0530 : Base 4 → WsL → ⟪ (ℓ "乼亚") ⟫ʷ ≈ ⟪ (ℓ "亞乼") ⟫ʷ
wp0530 c4 L = pw1 c4 L (ℓ "乼亚") (ℓ "亞乼") tt tt Eq.refl

wp0531 : Base 4 → WsL → ⟪ (ℓ "井並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並井") ⟫ʷ
wp0531 c4 L = pw2 c4 L (ℓ "井並亄並") (ℓ "並亄並井") tt tt Eq.refl

wp0532 : Base 4 → WsL → ⟪ (ℓ "丽並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並丽") ⟫ʷ
wp0532 c4 L = pw1 c4 L (ℓ "丽並亇並") (ℓ "並亇並丽") tt tt Eq.refl

wp0533 : Base 4 → WsL → ⟪ (ℓ "亁並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亁") ⟫ʷ
wp0533 c4 L = pw1 c4 L (ℓ "亁並亇並") (ℓ "並亇並亁") tt tt Eq.refl

wp0534 : Base 4 → WsL → ⟪ (ℓ "乩亞") ⟫ʷ ≈ ⟪ (ℓ "亞乩丽亜") ⟫ʷ
wp0534 c4 L = pw1 c4 L (ℓ "乩亞") (ℓ "亞乩丽亜") tt tt Eq.refl

wp0535 : Base 4 → WsL → ⟪ (ℓ "乩丽亜丽丿亜") ⟫ʷ ≈ ⟪ (ℓ "乩") ⟫ʷ
wp0535 c4 L = pw1 c4 L (ℓ "乩丽亜丽丿亜") (ℓ "乩") tt tt Eq.refl

wp0536 : Base 4 → WsL → ⟪ (ℓ "亜丘") ⟫ʷ ≈ ⟪ (ℓ "丘亞") ⟫ʷ
wp0536 c4 L = pw1 c4 L (ℓ "亜丘") (ℓ "丘亞") tt tt Eq.refl

wp0537 : Base 4 → WsL → ⟪ (ℓ "亜丙") ⟫ʷ ≈ ⟪ (ℓ "丙亞") ⟫ʷ
wp0537 c4 L = pw1 c4 L (ℓ "亜丙") (ℓ "丙亞") tt tt Eq.refl

wp0538 : Base 4 → WsL → ⟪ (ℓ "丶並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並丶") ⟫ʷ
wp0538 c4 L = pw1 c4 L (ℓ "丶並亇並") (ℓ "並亇並丶") tt tt Eq.refl

wp0539 : Base 4 → WsL → ⟪ (ℓ "丷並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並丷") ⟫ʷ
wp0539 c4 L = pw1 c4 L (ℓ "丷並亇並") (ℓ "並亇並丷") tt tt Eq.refl

wp0540 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "丨亃丩亃丽") ⟫ʷ
wp0540 c4 L = pw2 c4 L (ℓ "五") (ℓ "丨亃丩亃丽") tt tt Eq.refl

wp0541 : Base 4 → WsL → ⟪ (ℓ "之井") ⟫ʷ ≈ ⟪ (ℓ "井之") ⟫ʷ
wp0541 c4 L = pw3 c4 L (ℓ "之井") (ℓ "井之") tt tt Eq.refl

wp0542 : Base 4 → WsL → ⟪ (ℓ "亐井") ⟫ʷ ≈ ⟪ (ℓ "井亐京") ⟫ʷ
wp0542 c4 L = pw2 c4 L (ℓ "亐井") (ℓ "井亐京") tt tt Eq.refl

wp0543 : Base 4 → WsL → ⟪ (ℓ "亘乹") ⟫ʷ ≈ ⟪ (ℓ "乹亘") ⟫ʷ
wp0543 c4 L = pw1 c4 L (ℓ "亘乹") (ℓ "乹亘") tt tt Eq.refl

wp0544 : Base 4 → WsL → ⟪ (ℓ "也井") ⟫ʷ ≈ ⟪ (ℓ "井也亝") ⟫ʷ
wp0544 c4 L = pw3 c4 L (ℓ "也井") (ℓ "井也亝") tt tt Eq.refl

wp0545 : Base 4 → WsL → ⟪ (ℓ "亘亝亰") ⟫ʷ ≈ ⟪ (ℓ "亝亘") ⟫ʷ
wp0545 c4 L = pw1 c4 L (ℓ "亘亝亰") (ℓ "亝亘") tt tt Eq.refl

wp0546 : Base 4 → WsL → ⟪ (ℓ "乹井") ⟫ʷ ≈ ⟪ (ℓ "井乹") ⟫ʷ
wp0546 c4 L = pw2 c4 L (ℓ "乹井") (ℓ "井乹") tt tt Eq.refl

wp0547 : Base 4 → WsL → ⟪ (ℓ "了井") ⟫ʷ ≈ ⟪ (ℓ "井了") ⟫ʷ
wp0547 c4 L = pw3 c4 L (ℓ "了井") (ℓ "井了") tt tt Eq.refl

wp0548 : Base 4 → WsL → ⟪ (ℓ "井亝") ⟫ʷ ≈ ⟪ (ℓ "亝井") ⟫ʷ
wp0548 c4 L = pw3 c4 L (ℓ "井亝") (ℓ "亝井") tt tt Eq.refl

wp0549 : Base 4 → WsL → ⟪ (ℓ "也亝亝") ⟫ʷ ≈ ⟪ (ℓ "也") ⟫ʷ
wp0549 c4 L = pw3 c4 L (ℓ "也亝亝") (ℓ "也") tt tt Eq.refl

wp0550 : Base 4 → WsL → ⟪ (ℓ "亘亰") ⟫ʷ ≈ ⟪ (ℓ "亰亘") ⟫ʷ
wp0550 c4 L = pw1 c4 L (ℓ "亘亰") (ℓ "亰亘") tt tt Eq.refl

wp0551 : Base 4 → WsL → ⟪ (ℓ "亜乊") ⟫ʷ ≈ ⟪ (ℓ "乊五") ⟫ʷ
wp0551 c4 L = pw3 c4 L (ℓ "亜乊") (ℓ "乊五") tt tt Eq.refl

wp0552 : Base 4 → WsL → ⟪ (ℓ "乊井") ⟫ʷ ≈ ⟪ (ℓ "亝乊") ⟫ʷ
wp0552 c4 L = pw3 c4 L (ℓ "乊井") (ℓ "亝乊") tt tt Eq.refl

wp0553 : Base 4 → WsL → ⟪ (ℓ "五乊") ⟫ʷ ≈ ⟪ (ℓ "乊亜") ⟫ʷ
wp0553 c4 L = pw3 c4 L (ℓ "五乊") (ℓ "乊亜") tt tt Eq.refl

wp0554 : Base 4 → WsL → ⟪ (ℓ "乊亟") ⟫ʷ ≈ ⟪ (ℓ "亗乊") ⟫ʷ
wp0554 c4 L = pw3 c4 L (ℓ "乊亟") (ℓ "亗乊") tt tt Eq.refl

wp0555 : Base 4 → WsL → ⟪ (ℓ "亝並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亝") ⟫ʷ
wp0555 c4 L = pw1 c4 L (ℓ "亝並亇並") (ℓ "並亇並亝") tt tt Eq.refl

wp0556 : Base 4 → WsL → ⟪ (ℓ "亜並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亜") ⟫ʷ
wp0556 c4 L = pw1 c4 L (ℓ "亜並亇並") (ℓ "並亇並亜") tt tt Eq.refl

wp0557 : Base 4 → WsL → ⟪ (ℓ "丽並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並丽") ⟫ʷ
wp0557 c4 L = pw1 c4 L (ℓ "丽並亊並") (ℓ "並亊並丽") tt tt Eq.refl

wp0558 : Base 4 → WsL → ⟪ (ℓ "亁並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亁") ⟫ʷ
wp0558 c4 L = pw1 c4 L (ℓ "亁並亊並") (ℓ "並亊並亁") tt tt Eq.refl

wp0559 : Base 4 → WsL → ⟪ (ℓ "亰亞") ⟫ʷ ≈ ⟪ (ℓ "亞亰亠") ⟫ʷ
wp0559 c4 L = pw1 c4 L (ℓ "亰亞") (ℓ "亞亰亠") tt tt Eq.refl

wp0560 : Base 4 → WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "亃亠亃") ⟫ʷ
wp0560 c4 L = pw2 c4 L (ℓ "亠") (ℓ "亃亠亃") tt tt Eq.refl

wp0561 : Base 4 → WsL → ⟪ (ℓ "乙亞") ⟫ʷ ≈ ⟪ (ℓ "亞乙亏") ⟫ʷ
wp0561 c4 L = pw3 c4 L (ℓ "乙亞") (ℓ "亞乙亏") tt tt Eq.refl

wp0562 : Base 4 → WsL → ⟪ (ℓ "丶亞") ⟫ʷ ≈ ⟪ (ℓ "亞丶") ⟫ʷ
wp0562 c4 L = pw1 c4 L (ℓ "丶亞") (ℓ "亞丶") tt tt Eq.refl

wp0563 : Base 4 → WsL → ⟪ (ℓ "亏亞") ⟫ʷ ≈ ⟪ (ℓ "亞亏") ⟫ʷ
wp0563 c4 L = pw3 c4 L (ℓ "亏亞") (ℓ "亞亏") tt tt Eq.refl

wp0564 : Base 4 → WsL → ⟪ (ℓ "乙亏亏") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wp0564 c4 L = pw3 c4 L (ℓ "乙亏亏") (ℓ "乙") tt tt Eq.refl

wp0565 : Base 4 → WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乙亐乙") ⟫ʷ
wp0565 c4 L = pw2 c4 L (ℓ "亐") (ℓ "乙亐乙") tt tt Eq.refl

wp0566 : Base 4 → WsL → ⟪ (ℓ "亠乙") ⟫ʷ ≈ ⟪ (ℓ "乙亐亠") ⟫ʷ
wp0566 c4 L = pw2 c4 L (ℓ "亠乙") (ℓ "乙亐亠") tt tt Eq.refl

wp0567 : Base 4 → WsL → ⟪ (ℓ "亐亃") ⟫ʷ ≈ ⟪ (ℓ "亃亠亐") ⟫ʷ
wp0567 c4 L = pw2 c4 L (ℓ "亐亃") (ℓ "亃亠亐") tt tt Eq.refl

wp0568 : Base 4 → WsL → ⟪ (ℓ "亠亐亠亐亠") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0568 c4 L = pw2 c4 L (ℓ "亠亐亠亐亠") (ℓ "亠") tt tt Eq.refl

wp0569 : Base 4 → WsL → ⟪ (ℓ "乘亞") ⟫ʷ ≈ ⟪ (ℓ "亏乘") ⟫ʷ
wp0569 c4 L = pw3 c4 L (ℓ "乘亞") (ℓ "亏乘") tt tt Eq.refl

wp0570 : Base 4 → WsL → ⟪ (ℓ "乘亍") ⟫ʷ ≈ ⟪ (ℓ "亝乘") ⟫ʷ
wp0570 c4 L = pw3 c4 L (ℓ "乘亍") (ℓ "亝乘") tt tt Eq.refl

wp0571 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亮丶亮丷") ⟫ʷ
wp0571 c4 L = pw2 c4 L (ℓ "亮丶亮丷並亊並") (ℓ "並亊並亮丶亮丷") tt tt Eq.refl

wp0572 : Base 4 → WsL → ⟪ (ℓ "亘了亠") ⟫ʷ ≈ ⟪ (ℓ "了亘") ⟫ʷ
wp0572 c4 L = pw1 c4 L (ℓ "亘了亠") (ℓ "了亘") tt tt Eq.refl

wp0573 : Base 4 → WsL → ⟪ (ℓ "亠井") ⟫ʷ ≈ ⟪ (ℓ "井亠京") ⟫ʷ
wp0573 c4 L = pw2 c4 L (ℓ "亠井") (ℓ "井亠京") tt tt Eq.refl

wp0574 : Base 4 → WsL → ⟪ (ℓ "亘乺") ⟫ʷ ≈ ⟪ (ℓ "乺亘") ⟫ʷ
wp0574 c4 L = pw1 c4 L (ℓ "亘乺") (ℓ "乺亘") tt tt Eq.refl

wp0575 : Base 4 → WsL → ⟪ (ℓ "亘亠") ⟫ʷ ≈ ⟪ (ℓ "亠亘") ⟫ʷ
wp0575 c4 L = pw1 c4 L (ℓ "亘亠") (ℓ "亠亘") tt tt Eq.refl

wp0576 : Base 4 → WsL → ⟪ (ℓ "了亠亠") ⟫ʷ ≈ ⟪ (ℓ "了") ⟫ʷ
wp0576 c4 L = pw1 c4 L (ℓ "了亠亠") (ℓ "了") tt tt Eq.refl

wp0577 : Base 4 → WsL → ⟪ (ℓ "乭井") ⟫ʷ ≈ ⟪ (ℓ "井乭亍") ⟫ʷ
wp0577 c4 L = pw3 c4 L (ℓ "乭井") (ℓ "井乭亍") tt tt Eq.refl

wp0578 : Base 4 → WsL → ⟪ (ℓ "亘乭") ⟫ʷ ≈ ⟪ (ℓ "乭亘") ⟫ʷ
wp0578 c4 L = pw1 c4 L (ℓ "亘乭") (ℓ "乭亘") tt tt Eq.refl

wp0579 : Base 4 → WsL → ⟪ (ℓ "乎井") ⟫ʷ ≈ ⟪ (ℓ "井乎") ⟫ʷ
wp0579 c4 L = pw2 c4 L (ℓ "乎井") (ℓ "井乎") tt tt Eq.refl

wp0580 : Base 4 → WsL → ⟪ (ℓ "亍井") ⟫ʷ ≈ ⟪ (ℓ "井亍") ⟫ʷ
wp0580 c4 L = pw3 c4 L (ℓ "亍井") (ℓ "井亍") tt tt Eq.refl

wp0581 : Base 4 → WsL → ⟪ (ℓ "乭亍亍") ⟫ʷ ≈ ⟪ (ℓ "乭") ⟫ʷ
wp0581 c4 L = pw3 c4 L (ℓ "乭亍亍") (ℓ "乭") tt tt Eq.refl

wp0582 : Base 4 → WsL → ⟪ (ℓ "二乬") ⟫ʷ ≈ ⟪ (ℓ "乬五") ⟫ʷ
wp0582 c4 L = pw3 c4 L (ℓ "二乬") (ℓ "乬五") tt tt Eq.refl

wp0583 : Base 4 → WsL → ⟪ (ℓ "乬井") ⟫ʷ ≈ ⟪ (ℓ "亍乬") ⟫ʷ
wp0583 c4 L = pw3 c4 L (ℓ "乬井") (ℓ "亍乬") tt tt Eq.refl

wp0584 : Base 4 → WsL → ⟪ (ℓ "五乬") ⟫ʷ ≈ ⟪ (ℓ "乬二") ⟫ʷ
wp0584 c4 L = pw3 c4 L (ℓ "五乬") (ℓ "乬二") tt tt Eq.refl

wp0585 : Base 4 → WsL → ⟪ (ℓ "乬于") ⟫ʷ ≈ ⟪ (ℓ "亖乬") ⟫ʷ
wp0585 c4 L = pw3 c4 L (ℓ "乬于") (ℓ "亖乬") tt tt Eq.refl

wp0586 : Base 4 → WsL → ⟪ (ℓ "亡並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亡") ⟫ʷ
wp0586 c4 L = pw1 c4 L (ℓ "亡並亊並") (ℓ "並亊並亡") tt tt Eq.refl

wp0587 : Base 4 → WsL → ⟪ (ℓ "二亝") ⟫ʷ ≈ ⟪ (ℓ "亝二亨") ⟫ʷ
wp0587 c4 L = pw3 c4 L (ℓ "二亝") (ℓ "亝二亨") tt tt Eq.refl

wp0588 : Base 4 → WsL → ⟪ (ℓ "乶亝") ⟫ʷ ≈ ⟪ (ℓ "亝乶亡") ⟫ʷ
wp0588 c4 L = pw1 c4 L (ℓ "乶亝") (ℓ "亝乶亡") tt tt Eq.refl

wp0589 : Base 4 → WsL → ⟪ (ℓ "亐亡京") ⟫ʷ ≈ ⟪ (ℓ "亡亐") ⟫ʷ
wp0589 c4 L = pw2 c4 L (ℓ "亐亡京") (ℓ "亡亐") tt tt Eq.refl

wp0590 : Base 4 → WsL → ⟪ (ℓ "乕亝") ⟫ʷ ≈ ⟪ (ℓ "亝乕") ⟫ʷ
wp0590 c4 L = pw3 c4 L (ℓ "乕亝") (ℓ "亝乕") tt tt Eq.refl

wp0591 : Base 4 → WsL → ⟪ (ℓ "亝亡") ⟫ʷ ≈ ⟪ (ℓ "亡亝") ⟫ʷ
wp0591 c4 L = pw1 c4 L (ℓ "亝亡") (ℓ "亡亝") tt tt Eq.refl

wp0592 : Base 4 → WsL → ⟪ (ℓ "乶亡亡") ⟫ʷ ≈ ⟪ (ℓ "乶") ⟫ʷ
wp0592 c4 L = pw1 c4 L (ℓ "乶亡亡") (ℓ "乶") tt tt Eq.refl

wp0593 : Base 4 → WsL → ⟪ (ℓ "亐京") ⟫ʷ ≈ ⟪ (ℓ "京亐") ⟫ʷ
wp0593 c4 L = pw2 c4 L (ℓ "亐京") (ℓ "京亐") tt tt Eq.refl

wp0594 : Base 4 → WsL → ⟪ (ℓ "亠乥") ⟫ʷ ≈ ⟪ (ℓ "乥亜") ⟫ʷ
wp0594 c4 L = pw1 c4 L (ℓ "亠乥") (ℓ "乥亜") tt tt Eq.refl

wp0595 : Base 4 → WsL → ⟪ (ℓ "乥亝") ⟫ʷ ≈ ⟪ (ℓ "亡乥") ⟫ʷ
wp0595 c4 L = pw1 c4 L (ℓ "乥亝") (ℓ "亡乥") tt tt Eq.refl

wp0596 : Base 4 → WsL → ⟪ (ℓ "亜乥") ⟫ʷ ≈ ⟪ (ℓ "乥亠") ⟫ʷ
wp0596 c4 L = pw1 c4 L (ℓ "亜乥") (ℓ "乥亠") tt tt Eq.refl

wp0597 : Base 4 → WsL → ⟪ (ℓ "乥亣") ⟫ʷ ≈ ⟪ (ℓ "亟乥") ⟫ʷ
wp0597 c4 L = pw1 c4 L (ℓ "乥亣") (ℓ "亟乥") tt tt Eq.refl

wp0598 : Base 4 → WsL → ⟪ (ℓ "亜亞乤亞亜乤") ⟫ʷ ≈ ⟪ (ℓ "亠") ⟫ʷ
wp0598 c4 L = pw1 c4 L (ℓ "亜亞乤亞亜乤") (ℓ "亠") tt tt Eq.refl

wp0599 : Base 4 → WsL → ⟪ (ℓ "亮丶亮丷一丣") ⟫ʷ ≈ ⟪ (ℓ "一丣亮丶亮丷") ⟫ʷ
wp0599 c4 L = pw2 c4 L (ℓ "亮丶亮丷一丣") (ℓ "一丣亮丶亮丷") tt tt Eq.refl

wp0600 : Base 4 → WsL → ⟪ (ℓ "亦丂丣") ⟫ʷ ≈ ⟪ (ℓ "丂丣亦") ⟫ʷ
wp0600 c4 L = pw0 c4 L (ℓ "亦丂丣") (ℓ "丂丣亦") tt tt Eq.refl

wp0601 : Base 4 → WsL → ⟪ (ℓ "亜一丣") ⟫ʷ ≈ ⟪ (ℓ "一丣亜") ⟫ʷ
wp0601 c4 L = pw1 c4 L (ℓ "亜一丣") (ℓ "一丣亜") tt tt Eq.refl

wp0602 : Base 4 → WsL → ⟪ (ℓ "上举並") ⟫ʷ ≈ ⟪ (ℓ "並丽") ⟫ʷ
wp0602 c4 L = pw1 c4 L (ℓ "上举並") (ℓ "並丽") tt tt Eq.refl

wp0603 : Base 4 → WsL → ⟪ (ℓ "丽並") ⟫ʷ ≈ ⟪ (ℓ "並上举") ⟫ʷ
wp0603 c4 L = pw1 c4 L (ℓ "丽並") (ℓ "並上举") tt tt Eq.refl

wp0604 : Base 4 → WsL → ⟪ (ℓ "丐乖亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丐乖") ⟫ʷ
wp0604 c4 L = pw2 c4 L (ℓ "丐乖亮丶亮丷") (ℓ "亮丶亮丷丐乖") tt tt Eq.refl

wp0605 : Base 4 → WsL → ⟪ (ℓ "亜丐乖") ⟫ʷ ≈ ⟪ (ℓ "丐乖亜") ⟫ʷ
wp0605 c4 L = pw3 c4 L (ℓ "亜丐乖") (ℓ "丐乖亜") tt tt Eq.refl

wp0606 : Base 4 → WsL → ⟪ (ℓ "丷世乪") ⟫ʷ ≈ ⟪ (ℓ "世乪丷") ⟫ʷ
wp0606 c4 L = pw1 c4 L (ℓ "丷世乪") (ℓ "世乪丷") tt tt Eq.refl

wp0607 : Base 4 → WsL → ⟪ (ℓ "丶世乪") ⟫ʷ ≈ ⟪ (ℓ "世乪丶") ⟫ʷ
wp0607 c4 L = pw1 c4 L (ℓ "丶世乪") (ℓ "世乪丶") tt tt Eq.refl

wp0608 : Base 4 → WsL → ⟪ (ℓ "东乺亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷东乺") ⟫ʷ
wp0608 c4 L = pw2 c4 L (ℓ "东乺亮丶亮丷") (ℓ "亮丶亮丷东乺") tt tt Eq.refl

wp0609 : Base 4 → WsL → ⟪ (ℓ "亜东乺") ⟫ʷ ≈ ⟪ (ℓ "东乺亜") ⟫ʷ
wp0609 c4 L = pw1 c4 L (ℓ "亜东乺") (ℓ "东乺亜") tt tt Eq.refl

wp0610 : Base 4 → WsL → ⟪ (ℓ "丌亁丢並") ⟫ʷ ≈ ⟪ (ℓ "並亁") ⟫ʷ
wp0610 c4 L = pw1 c4 L (ℓ "丌亁丢並") (ℓ "並亁") tt tt Eq.refl

wp0611 : Base 4 → WsL → ⟪ (ℓ "丌亁丢亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丌亁丢") ⟫ʷ
wp0611 c4 L = pw2 c4 L (ℓ "丌亁丢亮丶亮丷") (ℓ "亮丶亮丷丌亁丢") tt tt Eq.refl

wp0612 : Base 4 → WsL → ⟪ (ℓ "亜丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亁丢亜") ⟫ʷ
wp0612 c4 L = pw1 c4 L (ℓ "亜丌亁丢") (ℓ "丌亁丢亜") tt tt Eq.refl

wp0613 : Base 4 → WsL → ⟪ (ℓ "亁並") ⟫ʷ ≈ ⟪ (ℓ "並丌亁丢") ⟫ʷ
wp0613 c4 L = pw1 c4 L (ℓ "亁並") (ℓ "並丌亁丢") tt tt Eq.refl

wp0614 : Base 4 → WsL → ⟪ (ℓ "丒亄丢亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丒亄丢") ⟫ʷ
wp0614 c4 L = pw2 c4 L (ℓ "丒亄丢亮丶亮丷") (ℓ "亮丶亮丷丒亄丢") tt tt Eq.refl

wp0615 : Base 4 → WsL → ⟪ (ℓ "丷丘亇丢") ⟫ʷ ≈ ⟪ (ℓ "丘亇丢丷") ⟫ʷ
wp0615 c4 L = pw1 c4 L (ℓ "丷丘亇丢") (ℓ "丘亇丢丷") tt tt Eq.refl

wp0616 : Base 4 → WsL → ⟪ (ℓ "丶丘亇丢") ⟫ʷ ≈ ⟪ (ℓ "丘亇丢丶") ⟫ʷ
wp0616 c4 L = pw1 c4 L (ℓ "丶丘亇丢") (ℓ "丘亇丢丶") tt tt Eq.refl

wp0617 : Base 4 → WsL → ⟪ (ℓ "亜丢") ⟫ʷ ≈ ⟪ (ℓ "丢亜") ⟫ʷ
wp0617 c4 L = pw1 c4 L (ℓ "亜丢") (ℓ "丢亜") tt tt Eq.refl

wp0618 : Base 4 → WsL → ⟪ (ℓ "丞亊丢亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丞亊丢") ⟫ʷ
wp0618 c4 L = pw2 c4 L (ℓ "丞亊丢亮丶亮丷") (ℓ "亮丶亮丷丞亊丢") tt tt Eq.refl

wp0619 : Base 4 → WsL → ⟪ (ℓ "亲乎亲乏丂丣") ⟫ʷ ≈ ⟪ (ℓ "丂丣亲乎亲乏") ⟫ʷ
wp0619 c4 L = pw0 c4 L (ℓ "亲乎亲乏丂丣") (ℓ "丂丣亲乎亲乏") tt tt Eq.refl

wp0620 : Base 4 → WsL → ⟪ (ℓ "亙一丣") ⟫ʷ ≈ ⟪ (ℓ "一丣亙") ⟫ʷ
wp0620 c4 L = pw1 c4 L (ℓ "亙一丣") (ℓ "一丣亙") tt tt Eq.refl

wp0621 : Base 4 → WsL → ⟪ (ℓ "五一丣") ⟫ʷ ≈ ⟪ (ℓ "一丣五") ⟫ʷ
wp0621 c4 L = pw2 c4 L (ℓ "五一丣") (ℓ "一丣五") tt tt Eq.refl

wp0622 : Base 4 → WsL → ⟪ (ℓ "乏上举") ⟫ʷ ≈ ⟪ (ℓ "上举乏") ⟫ʷ
wp0622 c4 L = pw2 c4 L (ℓ "乏上举") (ℓ "上举乏") tt tt Eq.refl

wp0623 : Base 4 → WsL → ⟪ (ℓ "上举亲") ⟫ʷ ≈ ⟪ (ℓ "亲上举") ⟫ʷ
wp0623 c4 L = pw1 c4 L (ℓ "上举亲") (ℓ "亲上举") tt tt Eq.refl

wp0624 : Base 4 → WsL → ⟪ (ℓ "乎上举") ⟫ʷ ≈ ⟪ (ℓ "上举乎") ⟫ʷ
wp0624 c4 L = pw2 c4 L (ℓ "乎上举") (ℓ "上举乎") tt tt Eq.refl

wp0625 : Base 4 → WsL → ⟪ (ℓ "世乪亙") ⟫ʷ ≈ ⟪ (ℓ "亙世乪") ⟫ʷ
wp0625 c4 L = pw1 c4 L (ℓ "世乪亙") (ℓ "亙世乪") tt tt Eq.refl

wp0626 : Base 4 → WsL → ⟪ (ℓ "五世乪") ⟫ʷ ≈ ⟪ (ℓ "世乪五") ⟫ʷ
wp0626 c4 L = pw3 c4 L (ℓ "五世乪") (ℓ "世乪五") tt tt Eq.refl

wp0627 : Base 4 → WsL → ⟪ (ℓ "东乺亙") ⟫ʷ ≈ ⟪ (ℓ "亙东乺") ⟫ʷ
wp0627 c4 L = pw1 c4 L (ℓ "东乺亙") (ℓ "亙东乺") tt tt Eq.refl

wp0628 : Base 4 → WsL → ⟪ (ℓ "五东乺") ⟫ʷ ≈ ⟪ (ℓ "东乺五") ⟫ʷ
wp0628 c4 L = pw2 c4 L (ℓ "五东乺") (ℓ "东乺五") tt tt Eq.refl

wp0629 : Base 4 → WsL → ⟪ (ℓ "乏丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亁丢乏") ⟫ʷ
wp0629 c4 L = pw2 c4 L (ℓ "乏丌亁丢") (ℓ "丌亁丢乏") tt tt Eq.refl

wp0630 : Base 4 → WsL → ⟪ (ℓ "丌亁丢亲") ⟫ʷ ≈ ⟪ (ℓ "亲丌亁丢") ⟫ʷ
wp0630 c4 L = pw1 c4 L (ℓ "丌亁丢亲") (ℓ "亲丌亁丢") tt tt Eq.refl

wp0631 : Base 4 → WsL → ⟪ (ℓ "乎丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亁丢乎") ⟫ʷ
wp0631 c4 L = pw2 c4 L (ℓ "乎丌亁丢") (ℓ "丌亁丢乎") tt tt Eq.refl

wp0632 : Base 4 → WsL → ⟪ (ℓ "丢亙") ⟫ʷ ≈ ⟪ (ℓ "亙丢") ⟫ʷ
wp0632 c4 L = pw1 c4 L (ℓ "丢亙") (ℓ "亙丢") tt tt Eq.refl

wp0633 : Base 4 → WsL → ⟪ (ℓ "五丢") ⟫ʷ ≈ ⟪ (ℓ "丢五") ⟫ʷ
wp0633 c4 L = pw2 c4 L (ℓ "五丢") (ℓ "丢五") tt tt Eq.refl

wp0634 : Base 4 → WsL → ⟪ (ℓ "五丒亄丢") ⟫ʷ ≈ ⟪ (ℓ "丒亄丢五") ⟫ʷ
wp0634 c4 L = pw2 c4 L (ℓ "五丒亄丢") (ℓ "丒亄丢五") tt tt Eq.refl

wp0635 : Base 4 → WsL → ⟪ (ℓ "丘亇丢亝") ⟫ʷ ≈ ⟪ (ℓ "亝丘亇丢") ⟫ʷ
wp0635 c4 L = pw1 c4 L (ℓ "丘亇丢亝") (ℓ "亝丘亇丢") tt tt Eq.refl

wp0636 : Base 4 → WsL → ⟪ (ℓ "丞亊丢亡") ⟫ʷ ≈ ⟪ (ℓ "亡丞亊丢") ⟫ʷ
wp0636 c4 L = pw1 c4 L (ℓ "丞亊丢亡") (ℓ "亡丞亊丢") tt tt Eq.refl

wp0637 : Base 4 → WsL → ⟪ (ℓ "亭乇亭么丂丣") ⟫ʷ ≈ ⟪ (ℓ "丂丣亭乇亭么") ⟫ʷ
wp0637 c4 L = pw0 c4 L (ℓ "亭乇亭么丂丣") (ℓ "丂丣亭乇亭么") tt tt Eq.refl

wp0638 : Base 4 → WsL → ⟪ (ℓ "云一丣") ⟫ʷ ≈ ⟪ (ℓ "一丣云") ⟫ʷ
wp0638 c4 L = pw2 c4 L (ℓ "云一丣") (ℓ "一丣云") tt tt Eq.refl

wp0639 : Base 4 → WsL → ⟪ (ℓ "么上举") ⟫ʷ ≈ ⟪ (ℓ "上举么") ⟫ʷ
wp0639 c4 L = pw3 c4 L (ℓ "么上举") (ℓ "上举么") tt tt Eq.refl

wp0640 : Base 4 → WsL → ⟪ (ℓ "上举亭") ⟫ʷ ≈ ⟪ (ℓ "亭上举") ⟫ʷ
wp0640 c4 L = pw2 c4 L (ℓ "上举亭") (ℓ "亭上举") tt tt Eq.refl

wp0641 : Base 4 → WsL → ⟪ (ℓ "乇上举") ⟫ʷ ≈ ⟪ (ℓ "上举乇") ⟫ʷ
wp0641 c4 L = pw3 c4 L (ℓ "乇上举") (ℓ "上举乇") tt tt Eq.refl

wp0642 : Base 4 → WsL → ⟪ (ℓ "丐乖云") ⟫ʷ ≈ ⟪ (ℓ "云丐乖") ⟫ʷ
wp0642 c4 L = pw2 c4 L (ℓ "丐乖云") (ℓ "云丐乖") tt tt Eq.refl

wp0643 : Base 4 → WsL → ⟪ (ℓ "东乺云") ⟫ʷ ≈ ⟪ (ℓ "云东乺") ⟫ʷ
wp0643 c4 L = pw2 c4 L (ℓ "东乺云") (ℓ "云东乺") tt tt Eq.refl

wp0644 : Base 4 → WsL → ⟪ (ℓ "么丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亁丢么") ⟫ʷ
wp0644 c4 L = pw3 c4 L (ℓ "么丌亁丢") (ℓ "丌亁丢么") tt tt Eq.refl

wp0645 : Base 4 → WsL → ⟪ (ℓ "丌亁丢亭") ⟫ʷ ≈ ⟪ (ℓ "亭丌亁丢") ⟫ʷ
wp0645 c4 L = pw2 c4 L (ℓ "丌亁丢亭") (ℓ "亭丌亁丢") tt tt Eq.refl

wp0646 : Base 4 → WsL → ⟪ (ℓ "乇丌亁丢") ⟫ʷ ≈ ⟪ (ℓ "丌亁丢乇") ⟫ʷ
wp0646 c4 L = pw3 c4 L (ℓ "乇丌亁丢") (ℓ "丌亁丢乇") tt tt Eq.refl

wp0647 : Base 4 → WsL → ⟪ (ℓ "丢云") ⟫ʷ ≈ ⟪ (ℓ "云丢") ⟫ʷ
wp0647 c4 L = pw2 c4 L (ℓ "丢云") (ℓ "云丢") tt tt Eq.refl

wp0648 : Base 4 → WsL → ⟪ (ℓ "丒亄丢井") ⟫ʷ ≈ ⟪ (ℓ "井丒亄丢") ⟫ʷ
wp0648 c4 L = pw2 c4 L (ℓ "丒亄丢井") (ℓ "井丒亄丢") tt tt Eq.refl

wp0649 : Base 4 → WsL → ⟪ (ℓ "亜丘亇丢") ⟫ʷ ≈ ⟪ (ℓ "丘亇丢亜") ⟫ʷ
wp0649 c4 L = pw1 c4 L (ℓ "亜丘亇丢") (ℓ "丘亇丢亜") tt tt Eq.refl

wp0650 : Base 4 → WsL → ⟪ (ℓ "亐五亮丶五亮丷並") ⟫ʷ ≈ ⟪ (ℓ "五亮丶五亮丷並亐") ⟫ʷ
wp0650 c4 L = pw2 c4 L (ℓ "亐五亮丶五亮丷並") (ℓ "五亮丶五亮丷並亐") tt tt Eq.refl

wp0651 : Base 4 → WsL → ⟪ (ℓ "五亮丶") ⟫ʷ ≈ ⟪ (ℓ "亮丶五") ⟫ʷ
wp0651 c4 L = pw2 c4 L (ℓ "五亮丶") (ℓ "亮丶五") tt tt Eq.refl

wp0652 : Base 4 → WsL → ⟪ (ℓ "乒亮亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷乒亮") ⟫ʷ
wp0652 c4 L = pw2 c4 L (ℓ "乒亮亮丶亮丷") (ℓ "亮丶亮丷乒亮") tt tt Eq.refl

wp0653 : Base 4 → WsL → ⟪ (ℓ "亜之") ⟫ʷ ≈ ⟪ (ℓ "之五亜") ⟫ʷ
wp0653 c4 L = pw3 c4 L (ℓ "亜之") (ℓ "之五亜") tt tt Eq.refl

wp0654 : Base 4 → WsL → ⟪ (ℓ "亜亪") ⟫ʷ ≈ ⟪ (ℓ "亪五亜") ⟫ʷ
wp0654 c4 L = pw3 c4 L (ℓ "亜亪") (ℓ "亪五亜") tt tt Eq.refl

wp0655 : Base 4 → WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "之五之") ⟫ʷ
wp0655 c4 L = pw3 c4 L (ℓ "五") (ℓ "之五之") tt tt Eq.refl

wp0656 : Base 4 → WsL → ⟪ (ℓ "五乒五亮") ⟫ʷ ≈ ⟪ (ℓ "乒亮") ⟫ʷ
wp0656 c4 L = pw2 c4 L (ℓ "五乒五亮") (ℓ "乒亮") tt tt Eq.refl

wp0657 : Base 4 → WsL → ⟪ (ℓ "丶並") ⟫ʷ ≈ ⟪ (ℓ "並丶") ⟫ʷ
wp0657 c4 L = pw1 c4 L (ℓ "丶並") (ℓ "並丶") tt tt Eq.refl

wp0658 : Base 4 → WsL → ⟪ (ℓ "丶亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丶") ⟫ʷ
wp0658 c4 L = pw2 c4 L (ℓ "丶亮丶亮丷") (ℓ "亮丶亮丷丶") tt tt Eq.refl

wp0659 : Base 4 → WsL → ⟪ (ℓ "丷並") ⟫ʷ ≈ ⟪ (ℓ "並丷") ⟫ʷ
wp0659 c4 L = pw1 c4 L (ℓ "丷並") (ℓ "並丷") tt tt Eq.refl

wp0660 : Base 4 → WsL → ⟪ (ℓ "丷亮丶亮丷") ⟫ʷ ≈ ⟪ (ℓ "亮丶亮丷丷") ⟫ʷ
wp0660 c4 L = pw2 c4 L (ℓ "丷亮丶亮丷") (ℓ "亮丶亮丷丷") tt tt Eq.refl

wp0661 : Base 4 → WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "亠亣乫亣亠乫") ⟫ʷ
wp0661 c4 L = pw1 c4 L (ℓ "亘") (ℓ "亠亣乫亣亠乫") tt tt Eq.refl

wp0662 : Base 4 → WsL → ⟪ (ℓ "乄亮") ⟫ʷ ≈ ⟪ (ℓ "亮乄") ⟫ʷ
wp0662 c4 L = pw2 c4 L (ℓ "乄亮") (ℓ "亮乄") tt tt Eq.refl

wp0663 : Base 4 → WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乄亨乄") ⟫ʷ
wp0663 c4 L = pw3 c4 L (ℓ "亨") (ℓ "乄亨乄") tt tt Eq.refl

wp0664 : Base 4 → WsL → ⟪ (ℓ "丬亮") ⟫ʷ ≈ ⟪ (ℓ "亮丬亢") ⟫ʷ
wp0664 c4 L = pw2 c4 L (ℓ "丬亮") (ℓ "亮丬亢") tt tt Eq.refl

wp0665 : Base 4 → WsL → ⟪ (ℓ "亘亢亜") ⟫ʷ ≈ ⟪ (ℓ "亢亘") ⟫ʷ
wp0665 c4 L = pw1 c4 L (ℓ "亘亢亜") (ℓ "亢亘") tt tt Eq.refl

wp0666 : Base 4 → WsL → ⟪ (ℓ "亀亮") ⟫ʷ ≈ ⟪ (ℓ "亮亀") ⟫ʷ
wp0666 c4 L = pw2 c4 L (ℓ "亀亮") (ℓ "亮亀") tt tt Eq.refl

wp0667 : Base 4 → WsL → ⟪ (ℓ "亢亮") ⟫ʷ ≈ ⟪ (ℓ "亮亢") ⟫ʷ
wp0667 c4 L = pw2 c4 L (ℓ "亢亮") (ℓ "亮亢") tt tt Eq.refl

wp0668 : Base 4 → WsL → ⟪ (ℓ "丬亢亢") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wp0668 c4 L = pw2 c4 L (ℓ "丬亢亢") (ℓ "丬") tt tt Eq.refl

wp0669 : Base 4 → WsL → ⟪ (ℓ "亘亜") ⟫ʷ ≈ ⟪ (ℓ "亜亘") ⟫ʷ
wp0669 c4 L = pw1 c4 L (ℓ "亘亜") (ℓ "亜亘") tt tt Eq.refl

wp0670 : Base 4 → WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丬亜丬") ⟫ʷ
wp0670 c4 L = pw3 c4 L (ℓ "亜") (ℓ "丬亜丬") tt tt Eq.refl

wp0671 : Base 4 → WsL → ⟪ (ℓ "亨丬") ⟫ʷ ≈ ⟪ (ℓ "丬亜亨") ⟫ʷ
wp0671 c4 L = pw3 c4 L (ℓ "亨丬") (ℓ "丬亜亨") tt tt Eq.refl

wp0672 : Base 4 → WsL → ⟪ (ℓ "亨乄") ⟫ʷ ≈ ⟪ (ℓ "乄亨") ⟫ʷ
wp0672 c4 L = pw3 c4 L (ℓ "亨乄") (ℓ "乄亨") tt tt Eq.refl

wp0673 : Base 4 → WsL → ⟪ (ℓ "亜乄") ⟫ʷ ≈ ⟪ (ℓ "乄亨亜") ⟫ʷ
wp0673 c4 L = pw3 c4 L (ℓ "亜乄") (ℓ "乄亨亜") tt tt Eq.refl

wp0674 : Base 4 → WsL → ⟪ (ℓ "亨亜亨亜亨") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wp0674 c4 L = pw3 c4 L (ℓ "亨亜亨亜亨") (ℓ "亨") tt tt Eq.refl
