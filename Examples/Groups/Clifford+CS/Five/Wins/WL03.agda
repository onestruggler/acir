------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL03 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl0505 : Base 4 → ⟪ (ℓ "交义") ⟫ʷ ≈ ⟪ (ℓ "产交产") ⟫ʷ
wl0505 c4 = lw4 c4 (ℓ "交义") (ℓ "产交产") tt tt Eq.refl

wl0506 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "义交义") ⟫ʷ
wl0506 c4 = lw4 c4 (ℓ "交") (ℓ "义交义") tt tt Eq.refl

wl0507 : Base 4 → ⟪ (ℓ "亰享交") ⟫ʷ ≈ ⟪ (ℓ "享亰") ⟫ʷ
wl0507 c4 = lw0 c4 (ℓ "亰享交") (ℓ "享亰") tt tt Eq.refl

wl0508 : Base 4 → ⟪ (ℓ "交亰") ⟫ʷ ≈ ⟪ (ℓ "亰交") ⟫ʷ
wl0508 c4 = lw0 c4 (ℓ "交亰") (ℓ "亰交") tt tt Eq.refl

wl0509 : Base 4 → ⟪ (ℓ "丳乜丳") ⟫ʷ ≈ ⟪ (ℓ "串") ⟫ʷ
wl0509 c4 = lw4 c4 (ℓ "丳乜丳") (ℓ "串") tt tt Eq.refl

wl0510 : Base 4 → ⟪ (ℓ "亐交亐交亐") ⟫ʷ ≈ ⟪ (ℓ "亐") ⟫ʷ
wl0510 c4 = lw4 c4 (ℓ "亐交亐交亐") (ℓ "亐") tt tt Eq.refl

wl0511 : Base 4 → ⟪ (ℓ "乽产") ⟫ʷ ≈ ⟪ (ℓ "产享乽") ⟫ʷ
wl0511 c4 = lw0 c4 (ℓ "乽产") (ℓ "产享乽") tt tt Eq.refl

wl0512 : Base 4 → ⟪ (ℓ "丸产") ⟫ʷ ≈ ⟪ (ℓ "产丸二") ⟫ʷ
wl0512 c4 = lw4 c4 (ℓ "丸产") (ℓ "产丸二") tt tt Eq.refl

wl0513 : Base 4 → ⟪ (ℓ "产享") ⟫ʷ ≈ ⟪ (ℓ "享产") ⟫ʷ
wl0513 c4 = lw0 c4 (ℓ "产享") (ℓ "享产") tt tt Eq.refl

wl0514 : Base 4 → ⟪ (ℓ "丞乢之乣之乎丟") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl0514 c4 = lw4 c4 (ℓ "丞乢之乣之乎丟") (ℓ "产") tt tt Eq.refl

wl0515 : Base 4 → ⟪ (ℓ "产亳") ⟫ʷ ≈ ⟪ (ℓ "亳产享") ⟫ʷ
wl0515 c4 = lw0 c4 (ℓ "产亳") (ℓ "亳产享") tt tt Eq.refl

wl0516 : Base 4 → ⟪ (ℓ "享亳") ⟫ʷ ≈ ⟪ (ℓ "亳享") ⟫ʷ
wl0516 c4 = lw0 c4 (ℓ "享亳") (ℓ "亳享") tt tt Eq.refl

wl0517 : Base 4 → ⟪ (ℓ "产享享") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl0517 c4 = lw0 c4 (ℓ "产享享") (ℓ "产") tt tt Eq.refl

wl0518 : Base 4 → ⟪ (ℓ "交亥乗亥交乗") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl0518 c4 = lw0 c4 (ℓ "交亥乗亥交乗") (ℓ "亰") tt tt Eq.refl

wl0519 : Base 4 → ⟪ (ℓ "亐亓") ⟫ʷ ≈ ⟪ (ℓ "亓亐个") ⟫ʷ
wl0519 c4 = lw4 c4 (ℓ "亐亓") (ℓ "亓亐个") tt tt Eq.refl

wl0520 : Base 4 → ⟪ (ℓ "亐个亓亐") ⟫ʷ ≈ ⟪ (ℓ "亓") ⟫ʷ
wl0520 c4 = lw4 c4 (ℓ "亐个亓亐") (ℓ "亓") tt tt Eq.refl

wl0521 : Base 4 → ⟪ (ℓ "丳亓") ⟫ʷ ≈ ⟪ (ℓ "亓丳") ⟫ʷ
wl0521 c4 = lw4 c4 (ℓ "丳亓") (ℓ "亓丳") tt tt Eq.refl

wl0522 : Base 4 → ⟪ (ℓ "乜亓") ⟫ʷ ≈ ⟪ (ℓ "亓乜产") ⟫ʷ
wl0522 c4 = lw4 c4 (ℓ "乜亓") (ℓ "亓乜产") tt tt Eq.refl

wl0523 : Base 4 → ⟪ (ℓ "亰产亨") ⟫ʷ ≈ ⟪ (ℓ "产亰") ⟫ʷ
wl0523 c4 = lw0 c4 (ℓ "亰产亨") (ℓ "产亰") tt tt Eq.refl

wl0524 : Base 4 → ⟪ (ℓ "之亓") ⟫ʷ ≈ ⟪ (ℓ "亓之") ⟫ʷ
wl0524 c4 = lw4 c4 (ℓ "之亓") (ℓ "亓之") tt tt Eq.refl

wl0525 : Base 4 → ⟪ (ℓ "亓产") ⟫ʷ ≈ ⟪ (ℓ "产亓") ⟫ʷ
wl0525 c4 = lw4 c4 (ℓ "亓产") (ℓ "产亓") tt tt Eq.refl

wl0526 : Base 4 → ⟪ (ℓ "乜产产") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
wl0526 c4 = lw4 c4 (ℓ "乜产产") (ℓ "乜") tt tt Eq.refl

wl0527 : Base 4 → ⟪ (ℓ "亨亰") ⟫ʷ ≈ ⟪ (ℓ "亰亨") ⟫ʷ
wl0527 c4 = lw0 c4 (ℓ "亨亰") (ℓ "亰亨") tt tt Eq.refl

wl0528 : Base 4 → ⟪ (ℓ "交串") ⟫ʷ ≈ ⟪ (ℓ "串亐") ⟫ʷ
wl0528 c4 = lw4 c4 (ℓ "交串") (ℓ "串亐") tt tt Eq.refl

wl0529 : Base 4 → ⟪ (ℓ "串亓") ⟫ʷ ≈ ⟪ (ℓ "产串") ⟫ʷ
wl0529 c4 = lw4 c4 (ℓ "串亓") (ℓ "产串") tt tt Eq.refl

wl0530 : Base 4 → ⟪ (ℓ "亐串") ⟫ʷ ≈ ⟪ (ℓ "串交") ⟫ʷ
wl0530 c4 = lw4 c4 (ℓ "亐串") (ℓ "串交") tt tt Eq.refl

wl0531 : Base 4 → ⟪ (ℓ "串亥") ⟫ʷ ≈ ⟪ (ℓ "互串") ⟫ʷ
wl0531 c4 = lw4 c4 (ℓ "串亥") (ℓ "互串") tt tt Eq.refl

wl0532 : Base 4 → ⟪ (ℓ "亨享义") ⟫ʷ ≈ ⟪ (ℓ "享亨") ⟫ʷ
wl0532 c4 = lw0 c4 (ℓ "亨享义") (ℓ "享亨") tt tt Eq.refl

wl0533 : Base 4 → ⟪ (ℓ "亨享") ⟫ʷ ≈ ⟪ (ℓ "享义亨") ⟫ʷ
wl0533 c4 = lw0 c4 (ℓ "亨享") (ℓ "享义亨") tt tt Eq.refl

wl0534 : Base 4 → ⟪ (ℓ "乜产") ⟫ʷ ≈ ⟪ (ℓ "产乜") ⟫ʷ
wl0534 c4 = lw4 c4 (ℓ "乜产") (ℓ "产乜") tt tt Eq.refl

wl0535 : Base 4 → ⟪ (ℓ "亰产") ⟫ʷ ≈ ⟪ (ℓ "产亰亨") ⟫ʷ
wl0535 c4 = lw0 c4 (ℓ "亰产") (ℓ "产亰亨") tt tt Eq.refl

wl0536 : Base 4 → ⟪ (ℓ "丳产") ⟫ʷ ≈ ⟪ (ℓ "产丳亓") ⟫ʷ
wl0536 c4 = lw4 c4 (ℓ "丳产") (ℓ "产丳亓") tt tt Eq.refl

wl0537 : Base 4 → ⟪ (ℓ "乄产") ⟫ʷ ≈ ⟪ (ℓ "产乄") ⟫ʷ
wl0537 c4 = lw4 c4 (ℓ "乄产") (ℓ "产乄") tt tt Eq.refl

wl0538 : Base 4 → ⟪ (ℓ "丳亓亓") ⟫ʷ ≈ ⟪ (ℓ "丳") ⟫ʷ
wl0538 c4 = lw4 c4 (ℓ "丳亓亓") (ℓ "丳") tt tt Eq.refl

wl0539 : Base 4 → ⟪ (ℓ "串产") ⟫ʷ ≈ ⟪ (ℓ "亓串") ⟫ʷ
wl0539 c4 = lw4 c4 (ℓ "串产") (ℓ "亓串") tt tt Eq.refl

wl0540 : Base 4 → ⟪ (ℓ "串互") ⟫ʷ ≈ ⟪ (ℓ "亥串") ⟫ʷ
wl0540 c4 = lw4 c4 (ℓ "串互") (ℓ "亥串") tt tt Eq.refl

wl0541 : Base 4 → ⟪ (ℓ "乽乽") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0541 c4 = lw0 c4 (ℓ "乽乽") [] tt tt Eq.refl

wl0542 : Base 4 → ⟪ (ℓ "乖亲") ⟫ʷ ≈ ⟪ (ℓ "亲乖") ⟫ʷ
wl0542 c4 = lw0 c4 (ℓ "乖亲") (ℓ "亲乖") tt tt Eq.refl

wl0543 : Base 4 → ⟪ (ℓ "乕亲") ⟫ʷ ≈ ⟪ (ℓ "亲乕") ⟫ʷ
wl0543 c4 = lw0 c4 (ℓ "乕亲") (ℓ "亲乕") tt tt Eq.refl

wl0544 : Base 4 → ⟪ (ℓ "争亲") ⟫ʷ ≈ ⟪ (ℓ "亲争") ⟫ʷ
wl0544 c4 = lw0 c4 (ℓ "争亲") (ℓ "亲争") tt tt Eq.refl

wl0545 : Base 4 → ⟪ (ℓ "争享") ⟫ʷ ≈ ⟪ (ℓ "享争产") ⟫ʷ
wl0545 c4 = lw0 c4 (ℓ "争享") (ℓ "享争产") tt tt Eq.refl

wl0546 : Base 4 → ⟪ (ℓ "争产享") ⟫ʷ ≈ ⟪ (ℓ "享争") ⟫ʷ
wl0546 c4 = lw0 c4 (ℓ "争产享") (ℓ "享争") tt tt Eq.refl

wl0547 : Base 4 → ⟪ (ℓ "乽争乽") ⟫ʷ ≈ ⟪ (ℓ "乼") ⟫ʷ
wl0547 c4 = lw0 c4 (ℓ "乽争乽") (ℓ "乼") tt tt Eq.refl

wl0548 : Base 4 → ⟪ (ℓ "乼享") ⟫ʷ ≈ ⟪ (ℓ "产乼") ⟫ʷ
wl0548 c4 = lw0 c4 (ℓ "乼享") (ℓ "产乼") tt tt Eq.refl

wl0549 : Base 4 → ⟪ (ℓ "丢並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並丢") ⟫ʷ
wl0549 c4 = lw0 c4 (ℓ "丢並丢並") (ℓ "並丢並丢") tt tt Eq.refl

wl0550 : Base 4 → ⟪ (ℓ "乕並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並乕") ⟫ʷ
wl0550 c4 = lw0 c4 (ℓ "乕並丢並") (ℓ "並丢並乕") tt tt Eq.refl

wl0551 : Base 4 → ⟪ (ℓ "乩並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並乩") ⟫ʷ
wl0551 c4 = lw0 c4 (ℓ "乩並丢並") (ℓ "並丢並乩") tt tt Eq.refl

wl0552 : Base 4 → ⟪ (ℓ "乹並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並乹") ⟫ʷ
wl0552 c4 = lw0 c4 (ℓ "乹並丢並") (ℓ "並丢並乹") tt tt Eq.refl

wl0553 : Base 4 → ⟪ (ℓ "亄並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亄") ⟫ʷ
wl0553 c4 = lw0 c4 (ℓ "亄並丢並") (ℓ "並丢並亄") tt tt Eq.refl

wl0554 : Base 4 → ⟪ (ℓ "亇並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亇") ⟫ʷ
wl0554 c4 = lw0 c4 (ℓ "亇並丢並") (ℓ "並丢並亇") tt tt Eq.refl

wl0555 : Base 4 → ⟪ (ℓ "亊並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亊") ⟫ʷ
wl0555 c4 = lw0 c4 (ℓ "亊並丢並") (ℓ "並丢並亊") tt tt Eq.refl

wl0556 : Base 4 → ⟪ (ℓ "亦並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亦") ⟫ʷ
wl0556 c4 = lw0 c4 (ℓ "亦並丢並") (ℓ "並丢並亦") tt tt Eq.refl

wl0557 : Base 4 → ⟪ (ℓ "並丢並") ⟫ʷ ≈ ⟪ (ℓ "一丣") ⟫ʷ
wl0557 c4 = lw1 c4 (ℓ "並丢並") (ℓ "一丣") tt tt Eq.refl

wl0558 : Base 4 → ⟪ (ℓ "亲乎亲乏並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亲乎亲乏") ⟫ʷ
wl0558 c4 = lw0 c4 (ℓ "亲乎亲乏並丢並") (ℓ "並丢並亲乎亲乏") tt tt Eq.refl

wl0559 : Base 4 → ⟪ (ℓ "亭乇亭么並丢並") ⟫ʷ ≈ ⟪ (ℓ "並丢並亭乇亭么") ⟫ʷ
wl0559 c4 = lw0 c4 (ℓ "亭乇亭么並丢並") (ℓ "並丢並亭乇亭么") tt tt Eq.refl

wl0560 : Base 4 → ⟪ (ℓ "亘丬") ⟫ʷ ≈ ⟪ (ℓ "丬亘") ⟫ʷ
wl0560 c4 = lw4 c4 (ℓ "亘丬") (ℓ "丬亘") tt tt Eq.refl

wl0561 : Base 4 → ⟪ (ℓ "亘上") ⟫ʷ ≈ ⟪ (ℓ "上亘") ⟫ʷ
wl0561 c4 = lw4 c4 (ℓ "亘上") (ℓ "上亘") tt tt Eq.refl

wl0562 : Base 4 → ⟪ (ℓ "亐上") ⟫ʷ ≈ ⟪ (ℓ "上亐") ⟫ʷ
wl0562 c4 = lw4 c4 (ℓ "亐上") (ℓ "上亐") tt tt Eq.refl

wl0563 : Base 4 → ⟪ (ℓ "丢並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並丢") ⟫ʷ
wl0563 c4 = lw0 c4 (ℓ "丢並乕並") (ℓ "並乕並丢") tt tt Eq.refl

wl0564 : Base 4 → ⟪ (ℓ "乕並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並乕") ⟫ʷ
wl0564 c4 = lw0 c4 (ℓ "乕並乕並") (ℓ "並乕並乕") tt tt Eq.refl

wl0565 : Base 4 → ⟪ (ℓ "乩並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並乩") ⟫ʷ
wl0565 c4 = lw0 c4 (ℓ "乩並乕並") (ℓ "並乕並乩") tt tt Eq.refl

wl0566 : Base 4 → ⟪ (ℓ "乹並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並乹") ⟫ʷ
wl0566 c4 = lw0 c4 (ℓ "乹並乕並") (ℓ "並乕並乹") tt tt Eq.refl

wl0567 : Base 4 → ⟪ (ℓ "亄並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亄") ⟫ʷ
wl0567 c4 = lw0 c4 (ℓ "亄並乕並") (ℓ "並乕並亄") tt tt Eq.refl

wl0568 : Base 4 → ⟪ (ℓ "亇並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亇") ⟫ʷ
wl0568 c4 = lw0 c4 (ℓ "亇並乕並") (ℓ "並乕並亇") tt tt Eq.refl

wl0569 : Base 4 → ⟪ (ℓ "亊並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亊") ⟫ʷ
wl0569 c4 = lw0 c4 (ℓ "亊並乕並") (ℓ "並乕並亊") tt tt Eq.refl

wl0570 : Base 4 → ⟪ (ℓ "亦並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亦") ⟫ʷ
wl0570 c4 = lw0 c4 (ℓ "亦並乕並") (ℓ "並乕並亦") tt tt Eq.refl

wl0571 : Base 4 → ⟪ (ℓ "丐乖") ⟫ʷ ≈ ⟪ (ℓ "並乕並") ⟫ʷ
wl0571 c4 = lw0 c4 (ℓ "丐乖") (ℓ "並乕並") tt tt Eq.refl

wl0572 : Base 4 → ⟪ (ℓ "丐亙") ⟫ʷ ≈ ⟪ (ℓ "亙丐") ⟫ʷ
wl0572 c4 = lw4 c4 (ℓ "丐亙") (ℓ "亙丐") tt tt Eq.refl

wl0573 : Base 4 → ⟪ (ℓ "丐乖亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏丐乖") ⟫ʷ
wl0573 c4 = lw0 c4 (ℓ "丐乖亲乎亲乏") (ℓ "亲乎亲乏丐乖") tt tt Eq.refl

wl0574 : Base 4 → ⟪ (ℓ "亭乇亭么並乕並") ⟫ʷ ≈ ⟪ (ℓ "並乕並亭乇亭么") ⟫ʷ
wl0574 c4 = lw0 c4 (ℓ "亭乇亭么並乕並") (ℓ "並乕並亭乇亭么") tt tt Eq.refl

wl0575 : Base 4 → ⟪ (ℓ "丢並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並丢") ⟫ʷ
wl0575 c4 = lw0 c4 (ℓ "丢並乩並") (ℓ "並乩並丢") tt tt Eq.refl

wl0576 : Base 4 → ⟪ (ℓ "乕並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並乕") ⟫ʷ
wl0576 c4 = lw0 c4 (ℓ "乕並乩並") (ℓ "並乩並乕") tt tt Eq.refl

wl0577 : Base 4 → ⟪ (ℓ "乩並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並乩") ⟫ʷ
wl0577 c4 = lw0 c4 (ℓ "乩並乩並") (ℓ "並乩並乩") tt tt Eq.refl

wl0578 : Base 4 → ⟪ (ℓ "乹並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並乹") ⟫ʷ
wl0578 c4 = lw0 c4 (ℓ "乹並乩並") (ℓ "並乩並乹") tt tt Eq.refl

wl0579 : Base 4 → ⟪ (ℓ "亄並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亄") ⟫ʷ
wl0579 c4 = lw0 c4 (ℓ "亄並乩並") (ℓ "並乩並亄") tt tt Eq.refl

wl0580 : Base 4 → ⟪ (ℓ "亇並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亇") ⟫ʷ
wl0580 c4 = lw0 c4 (ℓ "亇並乩並") (ℓ "並乩並亇") tt tt Eq.refl

wl0581 : Base 4 → ⟪ (ℓ "亊並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亊") ⟫ʷ
wl0581 c4 = lw0 c4 (ℓ "亊並乩並") (ℓ "並乩並亊") tt tt Eq.refl

wl0582 : Base 4 → ⟪ (ℓ "交世") ⟫ʷ ≈ ⟪ (ℓ "世交") ⟫ʷ
wl0582 c4 = lw4 c4 (ℓ "交世") (ℓ "世交") tt tt Eq.refl

wl0583 : Base 4 → ⟪ (ℓ "世乪") ⟫ʷ ≈ ⟪ (ℓ "並乩並") ⟫ʷ
wl0583 c4 = lw0 c4 (ℓ "世乪") (ℓ "並乩並") tt tt Eq.refl

wl0584 : Base 4 → ⟪ (ℓ "亮並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亮") ⟫ʷ
wl0584 c4 = lw0 c4 (ℓ "亮並乩並") (ℓ "並乩並亮") tt tt Eq.refl

wl0585 : Base 4 → ⟪ (ℓ "亲乎亲乏並乩並") ⟫ʷ ≈ ⟪ (ℓ "並乩並亲乎亲乏") ⟫ʷ
wl0585 c4 = lw0 c4 (ℓ "亲乎亲乏並乩並") (ℓ "並乩並亲乎亲乏") tt tt Eq.refl

wl0586 : Base 4 → ⟪ (ℓ "世云") ⟫ʷ ≈ ⟪ (ℓ "云世") ⟫ʷ
wl0586 c4 = lw4 c4 (ℓ "世云") (ℓ "云世") tt tt Eq.refl

wl0587 : Base 4 → ⟪ (ℓ "世乪亭乇亭么") ⟫ʷ ≈ ⟪ (ℓ "亭乇亭么世乪") ⟫ʷ
wl0587 c4 = lw0 c4 (ℓ "世乪亭乇亭么") (ℓ "亭乇亭么世乪") tt tt Eq.refl

wl0588 : Base 4 → ⟪ (ℓ "丢並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並丢") ⟫ʷ
wl0588 c4 = lw0 c4 (ℓ "丢並乹並") (ℓ "並乹並丢") tt tt Eq.refl

wl0589 : Base 4 → ⟪ (ℓ "乕並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並乕") ⟫ʷ
wl0589 c4 = lw0 c4 (ℓ "乕並乹並") (ℓ "並乹並乕") tt tt Eq.refl

wl0590 : Base 4 → ⟪ (ℓ "乩並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並乩") ⟫ʷ
wl0590 c4 = lw0 c4 (ℓ "乩並乹並") (ℓ "並乹並乩") tt tt Eq.refl

wl0591 : Base 4 → ⟪ (ℓ "乹並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並乹") ⟫ʷ
wl0591 c4 = lw0 c4 (ℓ "乹並乹並") (ℓ "並乹並乹") tt tt Eq.refl

wl0592 : Base 4 → ⟪ (ℓ "亄並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亄") ⟫ʷ
wl0592 c4 = lw0 c4 (ℓ "亄並乹並") (ℓ "並乹並亄") tt tt Eq.refl

wl0593 : Base 4 → ⟪ (ℓ "亇並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亇") ⟫ʷ
wl0593 c4 = lw0 c4 (ℓ "亇並乹並") (ℓ "並乹並亇") tt tt Eq.refl

wl0594 : Base 4 → ⟪ (ℓ "亊並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亊") ⟫ʷ
wl0594 c4 = lw0 c4 (ℓ "亊並乹並") (ℓ "並乹並亊") tt tt Eq.refl

wl0595 : Base 4 → ⟪ (ℓ "亦並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亦") ⟫ʷ
wl0595 c4 = lw0 c4 (ℓ "亦並乹並") (ℓ "並乹並亦") tt tt Eq.refl

wl0596 : Base 4 → ⟪ (ℓ "东乺") ⟫ʷ ≈ ⟪ (ℓ "並乹並") ⟫ʷ
wl0596 c4 = lw0 c4 (ℓ "东乺") (ℓ "並乹並") tt tt Eq.refl

wl0597 : Base 4 → ⟪ (ℓ "亲乎亲乏並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亲乎亲乏") ⟫ʷ
wl0597 c4 = lw0 c4 (ℓ "亲乎亲乏並乹並") (ℓ "並乹並亲乎亲乏") tt tt Eq.refl

wl0598 : Base 4 → ⟪ (ℓ "亭乇亭么並乹並") ⟫ʷ ≈ ⟪ (ℓ "並乹並亭乇亭么") ⟫ʷ
wl0598 c4 = lw0 c4 (ℓ "亭乇亭么並乹並") (ℓ "並乹並亭乇亭么") tt tt Eq.refl

wl0599 : Base 4 → ⟪ (ℓ "丌亘") ⟫ʷ ≈ ⟪ (ℓ "亙丌") ⟫ʷ
wl0599 c4 = lw4 c4 (ℓ "丌亘") (ℓ "亙丌") tt tt Eq.refl

wl0600 : Base 4 → ⟪ (ℓ "不亘") ⟫ʷ ≈ ⟪ (ℓ "亙不") ⟫ʷ
wl0600 c4 = lw4 c4 (ℓ "不亘") (ℓ "亙不") tt tt Eq.refl

wl0601 : Base 4 → ⟪ (ℓ "丌亐") ⟫ʷ ≈ ⟪ (ℓ "云丌") ⟫ʷ
wl0601 c4 = lw4 c4 (ℓ "丌亐") (ℓ "云丌") tt tt Eq.refl

wl0602 : Base 4 → ⟪ (ℓ "不亐") ⟫ʷ ≈ ⟪ (ℓ "云不") ⟫ʷ
wl0602 c4 = lw4 c4 (ℓ "不亐") (ℓ "云不") tt tt Eq.refl

wl0603 : Base 4 → ⟪ (ℓ "丢並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並丢") ⟫ʷ
wl0603 c4 = lw0 c4 (ℓ "丢並亄並") (ℓ "並亄並丢") tt tt Eq.refl

wl0604 : Base 4 → ⟪ (ℓ "乕並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並乕") ⟫ʷ
wl0604 c4 = lw0 c4 (ℓ "乕並亄並") (ℓ "並亄並乕") tt tt Eq.refl

wl0605 : Base 4 → ⟪ (ℓ "乩並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並乩") ⟫ʷ
wl0605 c4 = lw0 c4 (ℓ "乩並亄並") (ℓ "並亄並乩") tt tt Eq.refl

wl0606 : Base 4 → ⟪ (ℓ "乹並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並乹") ⟫ʷ
wl0606 c4 = lw0 c4 (ℓ "乹並亄並") (ℓ "並亄並乹") tt tt Eq.refl

wl0607 : Base 4 → ⟪ (ℓ "亄並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亄") ⟫ʷ
wl0607 c4 = lw0 c4 (ℓ "亄並亄並") (ℓ "並亄並亄") tt tt Eq.refl

wl0608 : Base 4 → ⟪ (ℓ "亇並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亇") ⟫ʷ
wl0608 c4 = lw0 c4 (ℓ "亇並亄並") (ℓ "並亄並亇") tt tt Eq.refl

wl0609 : Base 4 → ⟪ (ℓ "亊並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亊") ⟫ʷ
wl0609 c4 = lw0 c4 (ℓ "亊並亄並") (ℓ "並亄並亊") tt tt Eq.refl

wl0610 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "亨享乻享亨乻") ⟫ʷ
wl0610 c4 = lw0 c4 (ℓ "交") (ℓ "亨享乻享亨乻") tt tt Eq.refl

wl0611 : Base 4 → ⟪ (ℓ "交丰") ⟫ʷ ≈ ⟪ (ℓ "丰交") ⟫ʷ
wl0611 c4 = lw4 c4 (ℓ "交丰") (ℓ "丰交") tt tt Eq.refl

wl0612 : Base 4 → ⟪ (ℓ "交丬亘") ⟫ʷ ≈ ⟪ (ℓ "丬交") ⟫ʷ
wl0612 c4 = lw4 c4 (ℓ "交丬亘") (ℓ "丬交") tt tt Eq.refl

wl0613 : Base 4 → ⟪ (ℓ "亘交") ⟫ʷ ≈ ⟪ (ℓ "交亘") ⟫ʷ
wl0613 c4 = lw4 c4 (ℓ "亘交") (ℓ "交亘") tt tt Eq.refl

wl0614 : Base 4 → ⟪ (ℓ "丬亘亘") ⟫ʷ ≈ ⟪ (ℓ "丬") ⟫ʷ
wl0614 c4 = lw4 c4 (ℓ "丬亘亘") (ℓ "丬") tt tt Eq.refl

wl0615 : Base 4 → ⟪ (ℓ "交亪京") ⟫ʷ ≈ ⟪ (ℓ "亪交") ⟫ʷ
wl0615 c4 = lw0 c4 (ℓ "交亪京") (ℓ "亪交") tt tt Eq.refl

wl0616 : Base 4 → ⟪ (ℓ "交乄") ⟫ʷ ≈ ⟪ (ℓ "乄交") ⟫ʷ
wl0616 c4 = lw4 c4 (ℓ "交乄") (ℓ "乄交") tt tt Eq.refl

wl0617 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乎亃乏亃乹") ⟫ʷ
wl0617 c4 = lw0 c4 (ℓ "京") (ℓ "乎亃乏亃乹") tt tt Eq.refl

wl0618 : Base 4 → ⟪ (ℓ "交京") ⟫ʷ ≈ ⟪ (ℓ "京交") ⟫ʷ
wl0618 c4 = lw0 c4 (ℓ "交京") (ℓ "京交") tt tt Eq.refl

wl0619 : Base 4 → ⟪ (ℓ "丬乄丬") ⟫ʷ ≈ ⟪ (ℓ "丫") ⟫ʷ
wl0619 c4 = lw4 c4 (ℓ "丬乄丬") (ℓ "丫") tt tt Eq.refl

wl0620 : Base 4 → ⟪ (ℓ "亘么") ⟫ʷ ≈ ⟪ (ℓ "么亘") ⟫ʷ
wl0620 c4 = lw4 c4 (ℓ "亘么") (ℓ "么亘") tt tt Eq.refl

wl0621 : Base 4 → ⟪ (ℓ "亘乇") ⟫ʷ ≈ ⟪ (ℓ "乇亘") ⟫ʷ
wl0621 c4 = lw4 c4 (ℓ "亘乇") (ℓ "乇亘") tt tt Eq.refl

wl0622 : Base 4 → ⟪ (ℓ "亨亪") ⟫ʷ ≈ ⟪ (ℓ "亪亨乗") ⟫ʷ
wl0622 c4 = lw0 c4 (ℓ "亨亪") (ℓ "亪亨乗") tt tt Eq.refl

wl0623 : Base 4 → ⟪ (ℓ "亨乗亪亨") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wl0623 c4 = lw0 c4 (ℓ "亨乗亪亨") (ℓ "亪") tt tt Eq.refl

wl0624 : Base 4 → ⟪ (ℓ "丘亨丙") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
wl0624 c4 = lw0 c4 (ℓ "丘亨丙") (ℓ "亪") tt tt Eq.refl

wl0625 : Base 4 → ⟪ (ℓ "丘亘丙") ⟫ʷ ≈ ⟪ (ℓ "亚") ⟫ʷ
wl0625 c4 = lw4 c4 (ℓ "丘亘丙") (ℓ "亚") tt tt Eq.refl

wl0626 : Base 4 → ⟪ (ℓ "亘丸亚") ⟫ʷ ≈ ⟪ (ℓ "亚亘") ⟫ʷ
wl0626 c4 = lw4 c4 (ℓ "亘丸亚") (ℓ "亚亘") tt tt Eq.refl

wl0627 : Base 4 → ⟪ (ℓ "亘丸") ⟫ʷ ≈ ⟪ (ℓ "亚亘亚") ⟫ʷ
wl0627 c4 = lw4 c4 (ℓ "亘丸") (ℓ "亚亘亚") tt tt Eq.refl

wl0628 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丸亘丸") ⟫ʷ
wl0628 c4 = lw4 c4 (ℓ "亘") (ℓ "丸亘丸") tt tt Eq.refl

wl0629 : Base 4 → ⟪ (ℓ "乖世亪丗") ⟫ʷ ≈ ⟪ (ℓ "亪亨") ⟫ʷ
wl0629 c4 = lw0 c4 (ℓ "乖世亪丗") (ℓ "亪亨") tt tt Eq.refl

wl0630 : Base 4 → ⟪ (ℓ "丷世亚丗") ⟫ʷ ≈ ⟪ (ℓ "亚亘") ⟫ʷ
wl0630 c4 = lw4 c4 (ℓ "丷世亚丗") (ℓ "亚亘") tt tt Eq.refl

wl0631 : Base 4 → ⟪ (ℓ "丷丗") ⟫ʷ ≈ ⟪ (ℓ "丗丷") ⟫ʷ
wl0631 c4 = lw4 c4 (ℓ "丷丗") (ℓ "丗丷") tt tt Eq.refl

wl0632 : Base 4 → ⟪ (ℓ "丷世") ⟫ʷ ≈ ⟪ (ℓ "世丷") ⟫ʷ
wl0632 c4 = lw4 c4 (ℓ "丷世") (ℓ "世丷") tt tt Eq.refl

wl0633 : Base 4 → ⟪ (ℓ "乖世") ⟫ʷ ≈ ⟪ (ℓ "世乖") ⟫ʷ
wl0633 c4 = lw0 c4 (ℓ "乖世") (ℓ "世乖") tt tt Eq.refl

wl0634 : Base 4 → ⟪ (ℓ "乖丗") ⟫ʷ ≈ ⟪ (ℓ "丗乖") ⟫ʷ
wl0634 c4 = lw0 c4 (ℓ "乖丗") (ℓ "丗乖") tt tt Eq.refl

wl0635 : Base 4 → ⟪ (ℓ "亚亚") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0635 c4 = lw4 c4 (ℓ "亚亚") [] tt tt Eq.refl

wl0636 : Base 4 → ⟪ (ℓ "亪亪") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0636 c4 = lw0 c4 (ℓ "亪亪") [] tt tt Eq.refl

wl0637 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "乢为乣为丯") ⟫ʷ
wl0637 c4 = lw4 c4 (ℓ "亘") (ℓ "乢为乣为丯") tt tt Eq.refl

wl0638 : Base 4 → ⟪ (ℓ "亨乣") ⟫ʷ ≈ ⟪ (ℓ "乣亨") ⟫ʷ
wl0638 c4 = lw0 c4 (ℓ "亨乣") (ℓ "乣亨") tt tt Eq.refl

wl0639 : Base 4 → ⟪ (ℓ "亨乢") ⟫ʷ ≈ ⟪ (ℓ "乢亨") ⟫ʷ
wl0639 c4 = lw0 c4 (ℓ "亨乢") (ℓ "乢亨") tt tt Eq.refl

wl0640 : Base 4 → ⟪ (ℓ "亘亚") ⟫ʷ ≈ ⟪ (ℓ "亚亘丸") ⟫ʷ
wl0640 c4 = lw4 c4 (ℓ "亘亚") (ℓ "亚亘丸") tt tt Eq.refl

wl0641 : Base 4 → ⟪ (ℓ "亘丸亚亘") ⟫ʷ ≈ ⟪ (ℓ "亚") ⟫ʷ
wl0641 c4 = lw4 c4 (ℓ "亘丸亚亘") (ℓ "亚") tt tt Eq.refl

wl0642 : Base 4 → ⟪ (ℓ "亪並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亪") ⟫ʷ
wl0642 c4 = lw0 c4 (ℓ "亪並亄並") (ℓ "並亄並亪") tt tt Eq.refl

wl0643 : Base 4 → ⟪ (ℓ "亲乎亲乏並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亲乎亲乏") ⟫ʷ
wl0643 c4 = lw0 c4 (ℓ "亲乎亲乏並亄並") (ℓ "並亄並亲乎亲乏") tt tt Eq.refl

wl0644 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乕乭乖乭乇") ⟫ʷ
wl0644 c4 = lw0 c4 (ℓ "亨") (ℓ "乕乭乖乭乇") tt tt Eq.refl

wl0645 : Base 4 → ⟪ (ℓ "亐乇") ⟫ʷ ≈ ⟪ (ℓ "乇亐") ⟫ʷ
wl0645 c4 = lw4 c4 (ℓ "亐乇") (ℓ "乇亐") tt tt Eq.refl

wl0646 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "争亨争") ⟫ʷ
wl0646 c4 = lw0 c4 (ℓ "亨") (ℓ "争亨争") tt tt Eq.refl

wl0647 : Base 4 → ⟪ (ℓ "亐亙交") ⟫ʷ ≈ ⟪ (ℓ "亙亐") ⟫ʷ
wl0647 c4 = lw4 c4 (ℓ "亐亙交") (ℓ "亙亐") tt tt Eq.refl

wl0648 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乽交乽") ⟫ʷ
wl0648 c4 = lw0 c4 (ℓ "交") (ℓ "乽交乽") tt tt Eq.refl

wl0649 : Base 4 → ⟪ (ℓ "争乽争") ⟫ʷ ≈ ⟪ (ℓ "乼") ⟫ʷ
wl0649 c4 = lw0 c4 (ℓ "争乽争") (ℓ "乼") tt tt Eq.refl

wl0650 : Base 4 → ⟪ (ℓ "亨乽") ⟫ʷ ≈ ⟪ (ℓ "乽交亨") ⟫ʷ
wl0650 c4 = lw0 c4 (ℓ "亨乽") (ℓ "乽交亨") tt tt Eq.refl

wl0651 : Base 4 → ⟪ (ℓ "亨争") ⟫ʷ ≈ ⟪ (ℓ "争亨") ⟫ʷ
wl0651 c4 = lw0 c4 (ℓ "亨争") (ℓ "争亨") tt tt Eq.refl

wl0652 : Base 4 → ⟪ (ℓ "交争") ⟫ʷ ≈ ⟪ (ℓ "争亨交") ⟫ʷ
wl0652 c4 = lw0 c4 (ℓ "交争") (ℓ "争亨交") tt tt Eq.refl

wl0653 : Base 4 → ⟪ (ℓ "亨交亨交亨") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wl0653 c4 = lw0 c4 (ℓ "亨交亨交亨") (ℓ "亨") tt tt Eq.refl

wl0654 : Base 4 → ⟪ (ℓ "亭乇亭么並亄並") ⟫ʷ ≈ ⟪ (ℓ "並亄並亭乇亭么") ⟫ʷ
wl0654 c4 = lw0 c4 (ℓ "亭乇亭么並亄並") (ℓ "並亄並亭乇亭么") tt tt Eq.refl

wl0655 : Base 4 → ⟪ (ℓ "丢並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並丢") ⟫ʷ
wl0655 c4 = lw0 c4 (ℓ "丢並亇並") (ℓ "並亇並丢") tt tt Eq.refl

wl0656 : Base 4 → ⟪ (ℓ "乕並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並乕") ⟫ʷ
wl0656 c4 = lw0 c4 (ℓ "乕並亇並") (ℓ "並亇並乕") tt tt Eq.refl

wl0657 : Base 4 → ⟪ (ℓ "乩並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並乩") ⟫ʷ
wl0657 c4 = lw0 c4 (ℓ "乩並亇並") (ℓ "並亇並乩") tt tt Eq.refl

wl0658 : Base 4 → ⟪ (ℓ "乹並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並乹") ⟫ʷ
wl0658 c4 = lw0 c4 (ℓ "乹並亇並") (ℓ "並亇並乹") tt tt Eq.refl

wl0659 : Base 4 → ⟪ (ℓ "亄並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亄") ⟫ʷ
wl0659 c4 = lw0 c4 (ℓ "亄並亇並") (ℓ "並亇並亄") tt tt Eq.refl

wl0660 : Base 4 → ⟪ (ℓ "亇並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亇") ⟫ʷ
wl0660 c4 = lw0 c4 (ℓ "亇並亇並") (ℓ "並亇並亇") tt tt Eq.refl

wl0661 : Base 4 → ⟪ (ℓ "亊並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亊") ⟫ʷ
wl0661 c4 = lw0 c4 (ℓ "亊並亇並") (ℓ "並亇並亊") tt tt Eq.refl

wl0662 : Base 4 → ⟪ (ℓ "丘交") ⟫ʷ ≈ ⟪ (ℓ "亦丘") ⟫ʷ
wl0662 c4 = lw4 c4 (ℓ "丘交") (ℓ "亦丘") tt tt Eq.refl

wl0663 : Base 4 → ⟪ (ℓ "丙交") ⟫ʷ ≈ ⟪ (ℓ "亦丙") ⟫ʷ
wl0663 c4 = lw4 c4 (ℓ "丙交") (ℓ "亦丙") tt tt Eq.refl

wl0664 : Base 4 → ⟪ (ℓ "予") ⟫ʷ ≈ ⟪ (ℓ "乩丙乩丘乩") ⟫ʷ
wl0664 c4 = lw0 c4 (ℓ "予") (ℓ "乩丙乩丘乩") tt tt Eq.refl

wl0665 : Base 4 → ⟪ (ℓ "丘予") ⟫ʷ ≈ ⟪ (ℓ "並亇並") ⟫ʷ
wl0665 c4 = lw0 c4 (ℓ "丘予") (ℓ "並亇並") tt tt Eq.refl

wl0666 : Base 4 → ⟪ (ℓ "亮並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亮") ⟫ʷ
wl0666 c4 = lw0 c4 (ℓ "亮並亇並") (ℓ "並亇並亮") tt tt Eq.refl

wl0667 : Base 4 → ⟪ (ℓ "亘丩") ⟫ʷ ≈ ⟪ (ℓ "丩亘") ⟫ʷ
wl0667 c4 = lw4 c4 (ℓ "亘丩") (ℓ "丩亘") tt tt Eq.refl

wl0668 : Base 4 → ⟪ (ℓ "亘之亐") ⟫ʷ ≈ ⟪ (ℓ "之亘") ⟫ʷ
wl0668 c4 = lw4 c4 (ℓ "亘之亐") (ℓ "之亘") tt tt Eq.refl

wl0669 : Base 4 → ⟪ (ℓ "亘乏") ⟫ʷ ≈ ⟪ (ℓ "乏亘") ⟫ʷ
wl0669 c4 = lw4 c4 (ℓ "亘乏") (ℓ "乏亘") tt tt Eq.refl

wl0670 : Base 4 → ⟪ (ℓ "亘乎") ⟫ʷ ≈ ⟪ (ℓ "乎亘") ⟫ʷ
wl0670 c4 = lw4 c4 (ℓ "亘乎") (ℓ "乎亘") tt tt Eq.refl

wl0671 : Base 4 → ⟪ (ℓ "亐亘") ⟫ʷ ≈ ⟪ (ℓ "亘亐") ⟫ʷ
wl0671 c4 = lw4 c4 (ℓ "亐亘") (ℓ "亘亐") tt tt Eq.refl

wl0672 : Base 4 → ⟪ (ℓ "之亐亐") ⟫ʷ ≈ ⟪ (ℓ "之") ⟫ʷ
wl0672 c4 = lw4 c4 (ℓ "之亐亐") (ℓ "之") tt tt Eq.refl

wl0673 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "之京之") ⟫ʷ
wl0673 c4 = lw0 c4 (ℓ "京") (ℓ "之京之") tt tt Eq.refl

wl0674 : Base 4 → ⟪ (ℓ "亘也") ⟫ʷ ≈ ⟪ (ℓ "也亘") ⟫ʷ
wl0674 c4 = lw4 c4 (ℓ "亘也") (ℓ "也亘") tt tt Eq.refl

wl0675 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乢了乣了乹") ⟫ʷ
wl0675 c4 = lw0 c4 (ℓ "亰") (ℓ "乢了乣了乹") tt tt Eq.refl

wl0676 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "也亰也") ⟫ʷ
wl0676 c4 = lw0 c4 (ℓ "亰") (ℓ "也亰也") tt tt Eq.refl

wl0677 : Base 4 → ⟪ (ℓ "之也之") ⟫ʷ ≈ ⟪ (ℓ "乊") ⟫ʷ
wl0677 c4 = lw4 c4 (ℓ "之也之") (ℓ "乊") tt tt Eq.refl

wl0678 : Base 4 → ⟪ (ℓ "京也") ⟫ʷ ≈ ⟪ (ℓ "也亰京") ⟫ʷ
wl0678 c4 = lw0 c4 (ℓ "京也") (ℓ "也亰京") tt tt Eq.refl

wl0679 : Base 4 → ⟪ (ℓ "京之") ⟫ʷ ≈ ⟪ (ℓ "之京") ⟫ʷ
wl0679 c4 = lw0 c4 (ℓ "京之") (ℓ "之京") tt tt Eq.refl

wl0680 : Base 4 → ⟪ (ℓ "亰之") ⟫ʷ ≈ ⟪ (ℓ "之京亰") ⟫ʷ
wl0680 c4 = lw0 c4 (ℓ "亰之") (ℓ "之京亰") tt tt Eq.refl

wl0681 : Base 4 → ⟪ (ℓ "京亰京亰京") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wl0681 c4 = lw0 c4 (ℓ "京亰京亰京") (ℓ "京") tt tt Eq.refl

wl0682 : Base 4 → ⟪ (ℓ "亐乐云") ⟫ʷ ≈ ⟪ (ℓ "云亐") ⟫ʷ
wl0682 c4 = lw4 c4 (ℓ "亐乐云") (ℓ "云亐") tt tt Eq.refl

wl0683 : Base 4 → ⟪ (ℓ "亐乐") ⟫ʷ ≈ ⟪ (ℓ "云亐云") ⟫ʷ
wl0683 c4 = lw4 c4 (ℓ "亐乐") (ℓ "云亐云") tt tt Eq.refl

wl0684 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乐亐乐") ⟫ʷ
wl0684 c4 = lw4 c4 (ℓ "亐") (ℓ "乐亐乐") tt tt Eq.refl

wl0685 : Base 4 → ⟪ (ℓ "亲乎亲乏並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亲乎亲乏") ⟫ʷ
wl0685 c4 = lw0 c4 (ℓ "亲乎亲乏並亇並") (ℓ "並亇並亲乎亲乏") tt tt Eq.refl

wl0686 : Base 4 → ⟪ (ℓ "亭乇亭么並亇並") ⟫ʷ ≈ ⟪ (ℓ "並亇並亭乇亭么") ⟫ʷ
wl0686 c4 = lw0 c4 (ℓ "亭乇亭么並亇並") (ℓ "並亇並亭乇亭么") tt tt Eq.refl

wl0687 : Base 4 → ⟪ (ℓ "丢並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並丢") ⟫ʷ
wl0687 c4 = lw0 c4 (ℓ "丢並亊並") (ℓ "並亊並丢") tt tt Eq.refl

wl0688 : Base 4 → ⟪ (ℓ "乕並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並乕") ⟫ʷ
wl0688 c4 = lw0 c4 (ℓ "乕並亊並") (ℓ "並亊並乕") tt tt Eq.refl

wl0689 : Base 4 → ⟪ (ℓ "乩並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並乩") ⟫ʷ
wl0689 c4 = lw0 c4 (ℓ "乩並亊並") (ℓ "並亊並乩") tt tt Eq.refl

wl0690 : Base 4 → ⟪ (ℓ "乹並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並乹") ⟫ʷ
wl0690 c4 = lw0 c4 (ℓ "乹並亊並") (ℓ "並亊並乹") tt tt Eq.refl

wl0691 : Base 4 → ⟪ (ℓ "亄並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亄") ⟫ʷ
wl0691 c4 = lw0 c4 (ℓ "亄並亊並") (ℓ "並亊並亄") tt tt Eq.refl

wl0692 : Base 4 → ⟪ (ℓ "亇並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亇") ⟫ʷ
wl0692 c4 = lw0 c4 (ℓ "亇並亊並") (ℓ "並亊並亇") tt tt Eq.refl

wl0693 : Base 4 → ⟪ (ℓ "亊並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亊") ⟫ʷ
wl0693 c4 = lw0 c4 (ℓ "亊並亊並") (ℓ "並亊並亊") tt tt Eq.refl

wl0694 : Base 4 → ⟪ (ℓ "交亃亰") ⟫ʷ ≈ ⟪ (ℓ "亃交") ⟫ʷ
wl0694 c4 = lw0 c4 (ℓ "交亃亰") (ℓ "亃交") tt tt Eq.refl

wl0695 : Base 4 → ⟪ (ℓ "亃亰亰") ⟫ʷ ≈ ⟪ (ℓ "亃") ⟫ʷ
wl0695 c4 = lw0 c4 (ℓ "亃亰亰") (ℓ "亃") tt tt Eq.refl

wl0696 : Base 4 → ⟪ (ℓ "交亏亐") ⟫ʷ ≈ ⟪ (ℓ "亏交") ⟫ʷ
wl0696 c4 = lw4 c4 (ℓ "交亏亐") (ℓ "亏交") tt tt Eq.refl

wl0697 : Base 4 → ⟪ (ℓ "亱並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亱") ⟫ʷ
wl0697 c4 = lw0 c4 (ℓ "亱並亊並") (ℓ "並亊並亱") tt tt Eq.refl

wl0698 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乹乙乺乙乎") ⟫ʷ
wl0698 c4 = lw0 c4 (ℓ "京") (ℓ "乹乙乺乙乎") tt tt Eq.refl

wl0699 : Base 4 → ⟪ (ℓ "亘亍交") ⟫ʷ ≈ ⟪ (ℓ "亍亘") ⟫ʷ
wl0699 c4 = lw4 c4 (ℓ "亘亍交") (ℓ "亍亘") tt tt Eq.refl

wl0700 : Base 4 → ⟪ (ℓ "亲乎亲乏並亊並") ⟫ʷ ≈ ⟪ (ℓ "並亊並亲乎亲乏") ⟫ʷ
wl0700 c4 = lw0 c4 (ℓ "亲乎亲乏並亊並") (ℓ "並亊並亲乎亲乏") tt tt Eq.refl
