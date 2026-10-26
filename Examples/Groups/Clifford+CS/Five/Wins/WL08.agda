------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL08 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl1524 : Base 4 → ⟪ (ℓ "二书二些") ⟫ʷ ≈ ⟪ (ℓ "书些") ⟫ʷ
wl1524 c4 = lw4 c4 (ℓ "二书二些") (ℓ "书些") tt tt Eq.refl

wl1525 : Base 4 → ⟪ (ℓ "些与") ⟫ʷ ≈ ⟪ (ℓ "与书些") ⟫ʷ
wl1525 c4 = lw4 c4 (ℓ "些与") (ℓ "与书些") tt tt Eq.refl

wl1526 : Base 4 → ⟪ (ℓ "乎与") ⟫ʷ ≈ ⟪ (ℓ "与乎") ⟫ʷ
wl1526 c4 = lw4 c4 (ℓ "乎与") (ℓ "与乎") tt tt Eq.refl

wl1527 : Base 4 → ⟪ (ℓ "乎些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏乎") ⟫ʷ
wl1527 c4 = lw4 c4 (ℓ "乎些乎些乏") (ℓ "些乎些乏乎") tt tt Eq.refl

wl1528 : Base 4 → ⟪ (ℓ "乏与") ⟫ʷ ≈ ⟪ (ℓ "与乏") ⟫ʷ
wl1528 c4 = lw4 c4 (ℓ "乏与") (ℓ "与乏") tt tt Eq.refl

wl1529 : Base 4 → ⟪ (ℓ "乏些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏乏") ⟫ʷ
wl1529 c4 = lw4 c4 (ℓ "乏些乎些乏") (ℓ "些乎些乏乏") tt tt Eq.refl

wl1530 : Base 4 → ⟪ (ℓ "些乎些乏与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与些乎些乏") ⟫ʷ
wl1530 c4 = lw4 c4 (ℓ "些乎些乏与临与") (ℓ "与临与些乎些乏") tt tt Eq.refl

wl1531 : Base 4 → ⟪ (ℓ "临与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与临") ⟫ʷ
wl1531 c4 = lw4 c4 (ℓ "临与临与") (ℓ "与临与临") tt tt Eq.refl

wl1532 : Base 4 → ⟪ (ℓ "临与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与临") ⟫ʷ
wl1532 c4 = lw4 c4 (ℓ "临与上与") (ℓ "与上与临") tt tt Eq.refl

wl1533 : Base 4 → ⟪ (ℓ "亳与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与亳") ⟫ʷ
wl1533 c4 = lw1 c4 (ℓ "亳与上与") (ℓ "与上与亳") tt tt Eq.refl

wl1534 : Base 4 → ⟪ (ℓ "些乎些乏与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与些乎些乏") ⟫ʷ
wl1534 c4 = lw4 c4 (ℓ "些乎些乏与上与") (ℓ "与上与些乎些乏") tt tt Eq.refl

wl1535 : Base 4 → ⟪ (ℓ "互乇互么与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与互乇互么") ⟫ʷ
wl1535 c4 = lw4 c4 (ℓ "互乇互么与上与") (ℓ "与上与互乇互么") tt tt Eq.refl

wl1536 : Base 4 → ⟪ (ℓ "互乇互么一下") ⟫ʷ ≈ ⟪ (ℓ "一下互乇互么") ⟫ʷ
wl1536 c4 = lw4 c4 (ℓ "互乇互么一下") (ℓ "一下互乇互么") tt tt Eq.refl

wl1537 : Base 4 → ⟪ (ℓ "丘临上互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么丘临上") ⟫ʷ
wl1537 c4 = lw4 c4 (ℓ "丘临上互乇互么") (ℓ "互乇互么丘临上") tt tt Eq.refl

wl1538 : Base 4 → ⟪ (ℓ "丘亯") ⟫ʷ ≈ ⟪ (ℓ "亯丘") ⟫ʷ
wl1538 c4 = lw0 c4 (ℓ "丘亯") (ℓ "亯丘") tt tt Eq.refl

wl1539 : Base 4 → ⟪ (ℓ "交互亘乇互亘么与") ⟫ʷ ≈ ⟪ (ℓ "互亘乇互亘么与交") ⟫ʷ
wl1539 c4 = lw4 c4 (ℓ "交互亘乇互亘么与") (ℓ "互亘乇互亘么与交") tt tt Eq.refl

wl1540 : Base 4 → ⟪ (ℓ "亘乇互") ⟫ʷ ≈ ⟪ (ℓ "乇互亘") ⟫ʷ
wl1540 c4 = lw4 c4 (ℓ "亘乇互") (ℓ "乇互亘") tt tt Eq.refl

wl1541 : Base 4 → ⟪ (ℓ "书些互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么书些") ⟫ʷ
wl1541 c4 = lw4 c4 (ℓ "书些互乇互么") (ℓ "互乇互么书些") tt tt Eq.refl

wl1542 : Base 4 → ⟪ (ℓ "乎互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么乎") ⟫ʷ
wl1542 c4 = lw4 c4 (ℓ "乎互乇互么") (ℓ "互乇互么乎") tt tt Eq.refl

wl1543 : Base 4 → ⟪ (ℓ "乏互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么乏") ⟫ʷ
wl1543 c4 = lw4 c4 (ℓ "乏互乇互么") (ℓ "互乇互么乏") tt tt Eq.refl

wl1544 : Base 4 → ⟪ (ℓ "么亯") ⟫ʷ ≈ ⟪ (ℓ "亯么") ⟫ʷ
wl1544 c4 = lw0 c4 (ℓ "么亯") (ℓ "亯么") tt tt Eq.refl

wl1545 : Base 4 → ⟪ (ℓ "丒丶乒丷乒丨专") ⟫ʷ ≈ ⟪ (ℓ "互") ⟫ʷ
wl1545 c4 = lw4 c4 (ℓ "丒丶乒丷乒丨专") (ℓ "互") tt tt Eq.refl

wl1546 : Base 4 → ⟪ (ℓ "乢亯") ⟫ʷ ≈ ⟪ (ℓ "亯乢") ⟫ʷ
wl1546 c4 = lw0 c4 (ℓ "乢亯") (ℓ "亯乢") tt tt Eq.refl

wl1547 : Base 4 → ⟪ (ℓ "乇亯") ⟫ʷ ≈ ⟪ (ℓ "亯乇") ⟫ʷ
wl1547 c4 = lw0 c4 (ℓ "乇亯") (ℓ "亯乇") tt tt Eq.refl

wl1548 : Base 4 → ⟪ (ℓ "亘互乇亘互么与交") ⟫ʷ ≈ ⟪ (ℓ "交亘互乇亘互么与") ⟫ʷ
wl1548 c4 = lw4 c4 (ℓ "亘互乇亘互么与交") (ℓ "交亘互乇亘互么与") tt tt Eq.refl

wl1549 : Base 4 → ⟪ (ℓ "亘互乇") ⟫ʷ ≈ ⟪ (ℓ "互乇亘") ⟫ʷ
wl1549 c4 = lw4 c4 (ℓ "亘互乇") (ℓ "互乇亘") tt tt Eq.refl

wl1550 : Base 4 → ⟪ (ℓ "乳互互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么乳互") ⟫ʷ
wl1550 c4 = lw4 c4 (ℓ "乳互互乇互么") (ℓ "互乇互么乳互") tt tt Eq.refl

wl1551 : Base 4 → ⟪ (ℓ "乽乳亯") ⟫ʷ ≈ ⟪ (ℓ "亯乳") ⟫ʷ
wl1551 c4 = lw0 c4 (ℓ "乽乳亯") (ℓ "亯乳") tt tt Eq.refl

wl1552 : Base 4 → ⟪ (ℓ "乽亯") ⟫ʷ ≈ ⟪ (ℓ "亯乽") ⟫ʷ
wl1552 c4 = lw0 c4 (ℓ "乽亯") (ℓ "亯乽") tt tt Eq.refl

wl1553 : Base 4 → ⟪ (ℓ "亘乳亘互") ⟫ʷ ≈ ⟪ (ℓ "乳互") ⟫ʷ
wl1553 c4 = lw4 c4 (ℓ "亘乳亘互") (ℓ "乳互") tt tt Eq.refl

wl1554 : Base 4 → ⟪ (ℓ "乇互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么乇") ⟫ʷ
wl1554 c4 = lw4 c4 (ℓ "乇互乇互么") (ℓ "互乇互么乇") tt tt Eq.refl

wl1555 : Base 4 → ⟪ (ℓ "么互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么么") ⟫ʷ
wl1555 c4 = lw4 c4 (ℓ "么互乇互么") (ℓ "互乇互么么") tt tt Eq.refl

wl1556 : Base 4 → ⟪ (ℓ "上与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与上") ⟫ʷ
wl1556 c4 = lw4 c4 (ℓ "上与临与") (ℓ "与临与上") tt tt Eq.refl

wl1557 : Base 4 → ⟪ (ℓ "些乎些乏一下") ⟫ʷ ≈ ⟪ (ℓ "一下些乎些乏") ⟫ʷ
wl1557 c4 = lw4 c4 (ℓ "些乎些乏一下") (ℓ "一下些乎些乏") tt tt Eq.refl

wl1558 : Base 4 → ⟪ (ℓ "亳一下") ⟫ʷ ≈ ⟪ (ℓ "一下亳") ⟫ʷ
wl1558 c4 = lw1 c4 (ℓ "亳一下") (ℓ "一下亳") tt tt Eq.refl

wl1559 : Base 4 → ⟪ (ℓ "上与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与上") ⟫ʷ
wl1559 c4 = lw4 c4 (ℓ "上与主与") (ℓ "与主与上") tt tt Eq.refl

wl1560 : Base 4 → ⟪ (ℓ "临与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与临") ⟫ʷ
wl1560 c4 = lw4 c4 (ℓ "临与主与") (ℓ "与主与临") tt tt Eq.refl

wl1561 : Base 4 → ⟪ (ℓ "些乎些乏与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与些乎些乏") ⟫ʷ
wl1561 c4 = lw4 c4 (ℓ "些乎些乏与主与") (ℓ "与主与些乎些乏") tt tt Eq.refl

wl1562 : Base 4 → ⟪ (ℓ "京书亨") ⟫ʷ ≈ ⟪ (ℓ "书京") ⟫ʷ
wl1562 c4 = lw0 c4 (ℓ "京书亨") (ℓ "书京") tt tt Eq.refl

wl1563 : Base 4 → ⟪ (ℓ "书亨亨") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
wl1563 c4 = lw0 c4 (ℓ "书亨亨") (ℓ "书") tt tt Eq.refl

wl1564 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "书二书") ⟫ʷ
wl1564 c4 = lw4 c4 (ℓ "二") (ℓ "书二书") tt tt Eq.refl

wl1565 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乶亐乶") ⟫ʷ
wl1565 c4 = lw4 c4 (ℓ "亐") (ℓ "乶亐乶") tt tt Eq.refl

wl1566 : Base 4 → ⟪ (ℓ "二乶") ⟫ʷ ≈ ⟪ (ℓ "乶亐二") ⟫ʷ
wl1566 c4 = lw4 c4 (ℓ "二乶") (ℓ "乶亐二") tt tt Eq.refl

wl1567 : Base 4 → ⟪ (ℓ "亐书") ⟫ʷ ≈ ⟪ (ℓ "书二亐") ⟫ʷ
wl1567 c4 = lw4 c4 (ℓ "亐书") (ℓ "书二亐") tt tt Eq.refl

wl1568 : Base 4 → ⟪ (ℓ "二亐二亐二") ⟫ʷ ≈ ⟪ (ℓ "二") ⟫ʷ
wl1568 c4 = lw4 c4 (ℓ "二亐二亐二") (ℓ "二") tt tt Eq.refl

wl1569 : Base 4 → ⟪ (ℓ "亨义享") ⟫ʷ ≈ ⟪ (ℓ "享亨") ⟫ʷ
wl1569 c4 = lw0 c4 (ℓ "亨义享") (ℓ "享亨") tt tt Eq.refl

wl1570 : Base 4 → ⟪ (ℓ "亨义") ⟫ʷ ≈ ⟪ (ℓ "享亨享") ⟫ʷ
wl1570 c4 = lw0 c4 (ℓ "亨义") (ℓ "享亨享") tt tt Eq.refl

wl1571 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "义亨义") ⟫ʷ
wl1571 c4 = lw0 c4 (ℓ "亨") (ℓ "义亨义") tt tt Eq.refl

wl1572 : Base 4 → ⟪ (ℓ "互乇互么与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与互乇互么") ⟫ʷ
wl1572 c4 = lw4 c4 (ℓ "互乇互么与主与") (ℓ "与主与互乇互么") tt tt Eq.refl

wl1573 : Base 4 → ⟪ (ℓ "中与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与中") ⟫ʷ
wl1573 c4 = lw4 c4 (ℓ "中与主与") (ℓ "与主与中") tt tt Eq.refl

wl1574 : Base 4 → ⟪ (ℓ "丞主上与") ⟫ʷ ≈ ⟪ (ℓ "与主") ⟫ʷ
wl1574 c4 = lw4 c4 (ℓ "丞主上与") (ℓ "与主") tt tt Eq.refl

wl1575 : Base 4 → ⟪ (ℓ "丞主上互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么丞主上") ⟫ʷ
wl1575 c4 = lw4 c4 (ℓ "丞主上互乇互么") (ℓ "互乇互么丞主上") tt tt Eq.refl

wl1576 : Base 4 → ⟪ (ℓ "亨丞") ⟫ʷ ≈ ⟪ (ℓ "丞亨") ⟫ʷ
wl1576 c4 = lw0 c4 (ℓ "亨丞") (ℓ "丞亨") tt tt Eq.refl

wl1577 : Base 4 → ⟪ (ℓ "主与") ⟫ʷ ≈ ⟪ (ℓ "与丞主上") ⟫ʷ
wl1577 c4 = lw4 c4 (ℓ "主与") (ℓ "与丞主上") tt tt Eq.refl

wl1578 : Base 4 → ⟪ (ℓ "主与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与主") ⟫ʷ
wl1578 c4 = lw4 c4 (ℓ "主与主与") (ℓ "与主与主") tt tt Eq.refl

wl1579 : Base 4 → ⟪ (ℓ "主与上与") ⟫ʷ ≈ ⟪ (ℓ "与上与主") ⟫ʷ
wl1579 c4 = lw4 c4 (ℓ "主与上与") (ℓ "与上与主") tt tt Eq.refl

wl1580 : Base 4 → ⟪ (ℓ "主与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与主") ⟫ʷ
wl1580 c4 = lw4 c4 (ℓ "主与临与") (ℓ "与临与主") tt tt Eq.refl

wl1581 : Base 4 → ⟪ (ℓ "丞主上些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏丞主上") ⟫ʷ
wl1581 c4 = lw4 c4 (ℓ "丞主上些乎些乏") (ℓ "些乎些乏丞主上") tt tt Eq.refl

wl1582 : Base 4 → ⟪ (ℓ "主与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与主") ⟫ʷ
wl1582 c4 = lw4 c4 (ℓ "主与中与") (ℓ "与中与主") tt tt Eq.refl

wl1583 : Base 4 → ⟪ (ℓ "互乇互么与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与互乇互么") ⟫ʷ
wl1583 c4 = lw4 c4 (ℓ "互乇互么与中与") (ℓ "与中与互乇互么") tt tt Eq.refl

wl1584 : Base 4 → ⟪ (ℓ "临与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与临") ⟫ʷ
wl1584 c4 = lw4 c4 (ℓ "临与中与") (ℓ "与中与临") tt tt Eq.refl

wl1585 : Base 4 → ⟪ (ℓ "些乎些乏与中与") ⟫ʷ ≈ ⟪ (ℓ "与中与些乎些乏") ⟫ʷ
wl1585 c4 = lw4 c4 (ℓ "些乎些乏与中与") (ℓ "与中与些乎些乏") tt tt Eq.refl

wl1586 : Base 4 → ⟪ (ℓ "乶亯") ⟫ʷ ≈ ⟪ (ℓ "亯乶") ⟫ʷ
wl1586 c4 = lw0 c4 (ℓ "乶亯") (ℓ "亯乶") tt tt Eq.refl

wl1587 : Base 4 → ⟪ (ℓ "书亯") ⟫ʷ ≈ ⟪ (ℓ "亯书享") ⟫ʷ
wl1587 c4 = lw0 c4 (ℓ "书亯") (ℓ "亯书享") tt tt Eq.refl

wl1588 : Base 4 → ⟪ (ℓ "之亯") ⟫ʷ ≈ ⟪ (ℓ "亯之") ⟫ʷ
wl1588 c4 = lw0 c4 (ℓ "之亯") (ℓ "亯之") tt tt Eq.refl

wl1589 : Base 4 → ⟪ (ℓ "享亯") ⟫ʷ ≈ ⟪ (ℓ "亯享") ⟫ʷ
wl1589 c4 = lw0 c4 (ℓ "享亯") (ℓ "亯享") tt tt Eq.refl

wl1590 : Base 4 → ⟪ (ℓ "书享享") ⟫ʷ ≈ ⟪ (ℓ "书") ⟫ʷ
wl1590 c4 = lw0 c4 (ℓ "书享享") (ℓ "书") tt tt Eq.refl

wl1591 : Base 4 → ⟪ (ℓ "亐二亐二亐") ⟫ʷ ≈ ⟪ (ℓ "亐") ⟫ʷ
wl1591 c4 = lw4 c4 (ℓ "亐二亐二亐") (ℓ "亐") tt tt Eq.refl

wl1592 : Base 4 → ⟪ (ℓ "亨乥") ⟫ʷ ≈ ⟪ (ℓ "乥京") ⟫ʷ
wl1592 c4 = lw0 c4 (ℓ "亨乥") (ℓ "乥京") tt tt Eq.refl

wl1593 : Base 4 → ⟪ (ℓ "乥亯") ⟫ʷ ≈ ⟪ (ℓ "享乥") ⟫ʷ
wl1593 c4 = lw0 c4 (ℓ "乥亯") (ℓ "享乥") tt tt Eq.refl

wl1594 : Base 4 → ⟪ (ℓ "京乥") ⟫ʷ ≈ ⟪ (ℓ "乥亨") ⟫ʷ
wl1594 c4 = lw0 c4 (ℓ "京乥") (ℓ "乥亨") tt tt Eq.refl

wl1595 : Base 4 → ⟪ (ℓ "乥亩") ⟫ʷ ≈ ⟪ (ℓ "亭乥") ⟫ʷ
wl1595 c4 = lw0 c4 (ℓ "乥亩") (ℓ "亭乥") tt tt Eq.refl

wl1596 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "京亮乤亮京乤") ⟫ʷ
wl1596 c4 = lw0 c4 (ℓ "亨") (ℓ "京亮乤亮京乤") tt tt Eq.refl

wl1597 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丬亘丬") ⟫ʷ
wl1597 c4 = lw4 c4 (ℓ "亘") (ℓ "丬亘丬") tt tt Eq.refl

wl1598 : Base 4 → ⟪ (ℓ "亨亯交") ⟫ʷ ≈ ⟪ (ℓ "亯亨") ⟫ʷ
wl1598 c4 = lw0 c4 (ℓ "亨亯交") (ℓ "亯亨") tt tt Eq.refl

wl1599 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乄交乄") ⟫ʷ
wl1599 c4 = lw4 c4 (ℓ "交") (ℓ "乄交乄") tt tt Eq.refl

wl1600 : Base 4 → ⟪ (ℓ "亘乄") ⟫ʷ ≈ ⟪ (ℓ "乄交亘") ⟫ʷ
wl1600 c4 = lw4 c4 (ℓ "亘乄") (ℓ "乄交亘") tt tt Eq.refl

wl1601 : Base 4 → ⟪ (ℓ "交丬") ⟫ʷ ≈ ⟪ (ℓ "丬亘交") ⟫ʷ
wl1601 c4 = lw4 c4 (ℓ "交丬") (ℓ "丬亘交") tt tt Eq.refl

wl1602 : Base 4 → ⟪ (ℓ "亘交亘交亘") ⟫ʷ ≈ ⟪ (ℓ "亘") ⟫ʷ
wl1602 c4 = lw4 c4 (ℓ "亘交亘交亘") (ℓ "亘") tt tt Eq.refl

wl1603 : Base 4 → ⟪ (ℓ "亨亯") ⟫ʷ ≈ ⟪ (ℓ "亯亨交") ⟫ʷ
wl1603 c4 = lw0 c4 (ℓ "亨亯") (ℓ "亯亨交") tt tt Eq.refl

wl1604 : Base 4 → ⟪ (ℓ "交亘交亘交") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl1604 c4 = lw4 c4 (ℓ "交亘交亘交") (ℓ "交") tt tt Eq.refl

wl1605 : Base 4 → ⟪ (ℓ "两乎亃乏亃乹严") ⟫ʷ ≈ ⟪ (ℓ "亯") ⟫ʷ
wl1605 c4 = lw0 c4 (ℓ "两乎亃乏亃乹严") (ℓ "亯") tt tt Eq.refl

wl1606 : Base 4 → ⟪ (ℓ "乏亚") ⟫ʷ ≈ ⟪ (ℓ "亚乏") ⟫ʷ
wl1606 c4 = lw4 c4 (ℓ "乏亚") (ℓ "亚乏") tt tt Eq.refl

wl1607 : Base 4 → ⟪ (ℓ "乎亚") ⟫ʷ ≈ ⟪ (ℓ "亚乎") ⟫ʷ
wl1607 c4 = lw4 c4 (ℓ "乎亚") (ℓ "亚乎") tt tt Eq.refl

wl1608 : Base 4 → ⟪ (ℓ "亯交交") ⟫ʷ ≈ ⟪ (ℓ "亯") ⟫ʷ
wl1608 c4 = lw0 c4 (ℓ "亯交交") (ℓ "亯") tt tt Eq.refl

wl1609 : Base 4 → ⟪ (ℓ "书享") ⟫ʷ ≈ ⟪ (ℓ "享书") ⟫ʷ
wl1609 c4 = lw0 c4 (ℓ "书享") (ℓ "享书") tt tt Eq.refl

wl1610 : Base 4 → ⟪ (ℓ "乶享") ⟫ʷ ≈ ⟪ (ℓ "享乶亯") ⟫ʷ
wl1610 c4 = lw0 c4 (ℓ "乶享") (ℓ "享乶亯") tt tt Eq.refl

wl1611 : Base 4 → ⟪ (ℓ "乒享") ⟫ʷ ≈ ⟪ (ℓ "享乒") ⟫ʷ
wl1611 c4 = lw0 c4 (ℓ "乒享") (ℓ "享乒") tt tt Eq.refl

wl1612 : Base 4 → ⟪ (ℓ "乶亯亯") ⟫ʷ ≈ ⟪ (ℓ "乶") ⟫ʷ
wl1612 c4 = lw0 c4 (ℓ "乶亯亯") (ℓ "乶") tt tt Eq.refl

wl1613 : Base 4 → ⟪ (ℓ "乥享") ⟫ʷ ≈ ⟪ (ℓ "亯乥") ⟫ʷ
wl1613 c4 = lw0 c4 (ℓ "乥享") (ℓ "亯乥") tt tt Eq.refl

wl1614 : Base 4 → ⟪ (ℓ "乥亭") ⟫ʷ ≈ ⟪ (ℓ "亩乥") ⟫ʷ
wl1614 c4 = lw0 c4 (ℓ "乥亭") (ℓ "亩乥") tt tt Eq.refl

wl1615 : Base 4 → ⟪ (ℓ "乹亯") ⟫ʷ ≈ ⟪ (ℓ "亯乹乎京") ⟫ʷ
wl1615 c4 = lw0 c4 (ℓ "乹亯") (ℓ "亯乹乎京") tt tt Eq.refl

wl1616 : Base 4 → ⟪ (ℓ "京亯") ⟫ʷ ≈ ⟪ (ℓ "亯乐京") ⟫ʷ
wl1616 c4 = lw0 c4 (ℓ "京亯") (ℓ "亯乐京") tt tt Eq.refl

wl1617 : Base 4 → ⟪ (ℓ "乹乎京乎乐京") ⟫ʷ ≈ ⟪ (ℓ "乹") ⟫ʷ
wl1617 c4 = lw0 c4 (ℓ "乹乎京乎乐京") (ℓ "乹") tt tt Eq.refl

wl1618 : Base 4 → ⟪ (ℓ "乺亯") ⟫ʷ ≈ ⟪ (ℓ "亯乺乏京") ⟫ʷ
wl1618 c4 = lw0 c4 (ℓ "乺亯") (ℓ "亯乺乏京") tt tt Eq.refl

wl1619 : Base 4 → ⟪ (ℓ "乺乏京乏乐京") ⟫ʷ ≈ ⟪ (ℓ "乺") ⟫ʷ
wl1619 c4 = lw0 c4 (ℓ "乺乏京乏乐京") (ℓ "乺") tt tt Eq.refl

wl1620 : Base 4 → ⟪ (ℓ "互亦") ⟫ʷ ≈ ⟪ (ℓ "亦互亚") ⟫ʷ
wl1620 c4 = lw4 c4 (ℓ "互亦") (ℓ "亦互亚") tt tt Eq.refl

wl1621 : Base 4 → ⟪ (ℓ "互亚亚") ⟫ʷ ≈ ⟪ (ℓ "互") ⟫ʷ
wl1621 c4 = lw4 c4 (ℓ "互亚亚") (ℓ "互") tt tt Eq.refl

wl1622 : Base 4 → ⟪ (ℓ "乐京亯") ⟫ʷ ≈ ⟪ (ℓ "亯京") ⟫ʷ
wl1622 c4 = lw0 c4 (ℓ "乐京亯") (ℓ "亯京") tt tt Eq.refl

wl1623 : Base 4 → ⟪ (ℓ "乒亓互乇互么") ⟫ʷ ≈ ⟪ (ℓ "互乇互么乒亓") ⟫ʷ
wl1623 c4 = lw4 c4 (ℓ "乒亓互乇互么") (ℓ "互乇互么乒亓") tt tt Eq.refl

wl1624 : Base 4 → ⟪ (ℓ "乙乒亯") ⟫ʷ ≈ ⟪ (ℓ "亯乒") ⟫ʷ
wl1624 c4 = lw0 c4 (ℓ "乙乒亯") (ℓ "亯乒") tt tt Eq.refl

wl1625 : Base 4 → ⟪ (ℓ "丞丶乒丷乒丨丟") ⟫ʷ ≈ ⟪ (ℓ "亓") ⟫ʷ
wl1625 c4 = lw4 c4 (ℓ "丞丶乒丷乒丨丟") (ℓ "亓") tt tt Eq.refl

wl1626 : Base 4 → ⟪ (ℓ "乙亯") ⟫ʷ ≈ ⟪ (ℓ "亯乙") ⟫ʷ
wl1626 c4 = lw0 c4 (ℓ "乙亯") (ℓ "亯乙") tt tt Eq.refl

wl1627 : Base 4 → ⟪ (ℓ "二乒二亓") ⟫ʷ ≈ ⟪ (ℓ "乒亓") ⟫ʷ
wl1627 c4 = lw4 c4 (ℓ "二乒二亓") (ℓ "乒亓") tt tt Eq.refl

wl1628 : Base 4 → ⟪ (ℓ "么乹") ⟫ʷ ≈ ⟪ (ℓ "乹么") ⟫ʷ
wl1628 c4 = lw0 c4 (ℓ "么乹") (ℓ "乹么") tt tt Eq.refl

wl1629 : Base 4 → ⟪ (ℓ "乇乹") ⟫ʷ ≈ ⟪ (ℓ "乹乇") ⟫ʷ
wl1629 c4 = lw0 c4 (ℓ "乇乹") (ℓ "乹乇") tt tt Eq.refl

wl1630 : Base 4 → ⟪ (ℓ "么乺") ⟫ʷ ≈ ⟪ (ℓ "乺么") ⟫ʷ
wl1630 c4 = lw0 c4 (ℓ "么乺") (ℓ "乺么") tt tt Eq.refl

wl1631 : Base 4 → ⟪ (ℓ "乇乺") ⟫ʷ ≈ ⟪ (ℓ "乺乇") ⟫ʷ
wl1631 c4 = lw0 c4 (ℓ "乇乺") (ℓ "乺乇") tt tt Eq.refl

wl1632 : Base 4 → ⟪ (ℓ "丵") ⟫ʷ ≈ ⟪ (ℓ "丯丙丯丘丯") ⟫ʷ
wl1632 c4 = lw4 c4 (ℓ "丵") (ℓ "丯丙丯丘丯") tt tt Eq.refl

wl1633 : Base 4 → ⟪ (ℓ "丘丵") ⟫ʷ ≈ ⟪ (ℓ "与临与") ⟫ʷ
wl1633 c4 = lw4 c4 (ℓ "丘丵") (ℓ "与临与") tt tt Eq.refl

wl1634 : Base 4 → ⟪ (ℓ "亓与临与") ⟫ʷ ≈ ⟪ (ℓ "与临与亓") ⟫ʷ
wl1634 c4 = lw4 c4 (ℓ "亓与临与") (ℓ "与临与亓") tt tt Eq.refl

wl1635 : Base 4 → ⟪ (ℓ "交亏") ⟫ʷ ≈ ⟪ (ℓ "亏亐交") ⟫ʷ
wl1635 c4 = lw4 c4 (ℓ "交亏") (ℓ "亏亐交") tt tt Eq.refl

wl1636 : Base 4 → ⟪ (ℓ "亐交亏") ⟫ʷ ≈ ⟪ (ℓ "亏交") ⟫ʷ
wl1636 c4 = lw4 c4 (ℓ "亐交亏") (ℓ "亏交") tt tt Eq.refl

wl1637 : Base 4 → ⟪ (ℓ "书亏") ⟫ʷ ≈ ⟪ (ℓ "亏亓书") ⟫ʷ
wl1637 c4 = lw4 c4 (ℓ "书亏") (ℓ "亏亓书") tt tt Eq.refl

wl1638 : Base 4 → ⟪ (ℓ "亰乫书") ⟫ʷ ≈ ⟪ (ℓ "书亰") ⟫ʷ
wl1638 c4 = lw0 c4 (ℓ "亰乫书") (ℓ "书亰") tt tt Eq.refl

wl1639 : Base 4 → ⟪ (ℓ "亰乫") ⟫ʷ ≈ ⟪ (ℓ "书亰书") ⟫ʷ
wl1639 c4 = lw0 c4 (ℓ "亰乫") (ℓ "书亰书") tt tt Eq.refl

wl1640 : Base 4 → ⟪ (ℓ "丘乇丬么丬丯丙") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1640 c4 = lw4 c4 (ℓ "丘乇丬么丬丯丙") (ℓ "亏") tt tt Eq.refl

wl1641 : Base 4 → ⟪ (ℓ "亏产") ⟫ʷ ≈ ⟪ (ℓ "产亏亓") ⟫ʷ
wl1641 c4 = lw4 c4 (ℓ "亏产") (ℓ "产亏亓") tt tt Eq.refl

wl1642 : Base 4 → ⟪ (ℓ "亏亓亓") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1642 c4 = lw4 c4 (ℓ "亏亓亓") (ℓ "亏") tt tt Eq.refl

wl1643 : Base 4 → ⟪ (ℓ "乺亲") ⟫ʷ ≈ ⟪ (ℓ "亲乺乪亰") ⟫ʷ
wl1643 c4 = lw0 c4 (ℓ "乺亲") (ℓ "亲乺乪亰") tt tt Eq.refl

wl1644 : Base 4 → ⟪ (ℓ "乪亲") ⟫ʷ ≈ ⟪ (ℓ "亲乪") ⟫ʷ
wl1644 c4 = lw0 c4 (ℓ "乪亲") (ℓ "亲乪") tt tt Eq.refl

wl1645 : Base 4 → ⟪ (ℓ "乺乪亰乪乫亰") ⟫ʷ ≈ ⟪ (ℓ "乺") ⟫ʷ
wl1645 c4 = lw0 c4 (ℓ "乺乪亰乪乫亰") (ℓ "乺") tt tt Eq.refl

wl1646 : Base 4 → ⟪ (ℓ "书亓") ⟫ʷ ≈ ⟪ (ℓ "亓书") ⟫ʷ
wl1646 c4 = lw4 c4 (ℓ "书亓") (ℓ "亓书") tt tt Eq.refl

wl1647 : Base 4 → ⟪ (ℓ "乹乩亰书") ⟫ʷ ≈ ⟪ (ℓ "书乹") ⟫ʷ
wl1647 c4 = lw0 c4 (ℓ "乹乩亰书") (ℓ "书乹") tt tt Eq.refl

wl1648 : Base 4 → ⟪ (ℓ "乺乪亰书") ⟫ʷ ≈ ⟪ (ℓ "书乺") ⟫ʷ
wl1648 c4 = lw0 c4 (ℓ "乺乪亰书") (ℓ "书乺") tt tt Eq.refl

wl1649 : Base 4 → ⟪ (ℓ "亰乩") ⟫ʷ ≈ ⟪ (ℓ "乩亰") ⟫ʷ
wl1649 c4 = lw0 c4 (ℓ "亰乩") (ℓ "乩亰") tt tt Eq.refl

wl1650 : Base 4 → ⟪ (ℓ "乩乺乪") ⟫ʷ ≈ ⟪ (ℓ "乺") ⟫ʷ
wl1650 c4 = lw0 c4 (ℓ "乩乺乪") (ℓ "乺") tt tt Eq.refl

wl1651 : Base 4 → ⟪ (ℓ "亰乺") ⟫ʷ ≈ ⟪ (ℓ "乺亰") ⟫ʷ
wl1651 c4 = lw0 c4 (ℓ "亰乺") (ℓ "乺亰") tt tt Eq.refl

wl1652 : Base 4 → ⟪ (ℓ "乹亲") ⟫ʷ ≈ ⟪ (ℓ "亲乹乩亰") ⟫ʷ
wl1652 c4 = lw0 c4 (ℓ "乹亲") (ℓ "亲乹乩亰") tt tt Eq.refl

wl1653 : Base 4 → ⟪ (ℓ "乩亲") ⟫ʷ ≈ ⟪ (ℓ "亲乩") ⟫ʷ
wl1653 c4 = lw0 c4 (ℓ "乩亲") (ℓ "亲乩") tt tt Eq.refl

wl1654 : Base 4 → ⟪ (ℓ "乹乩亰乩乫亰") ⟫ʷ ≈ ⟪ (ℓ "乹") ⟫ʷ
wl1654 c4 = lw0 c4 (ℓ "乹乩亰乩乫亰") (ℓ "乹") tt tt Eq.refl

wl1655 : Base 4 → ⟪ (ℓ "乶亓") ⟫ʷ ≈ ⟪ (ℓ "亓乶亏") ⟫ʷ
wl1655 c4 = lw4 c4 (ℓ "乶亓") (ℓ "亓乶亏") tt tt Eq.refl

wl1656 : Base 4 → ⟪ (ℓ "乹乶") ⟫ʷ ≈ ⟪ (ℓ "乶乹") ⟫ʷ
wl1656 c4 = lw0 c4 (ℓ "乹乶") (ℓ "乶乹") tt tt Eq.refl

wl1657 : Base 4 → ⟪ (ℓ "乶亏亓") ⟫ʷ ≈ ⟪ (ℓ "亓乶") ⟫ʷ
wl1657 c4 = lw4 c4 (ℓ "乶亏亓") (ℓ "亓乶") tt tt Eq.refl

wl1658 : Base 4 → ⟪ (ℓ "乺乶") ⟫ʷ ≈ ⟪ (ℓ "乶乺") ⟫ʷ
wl1658 c4 = lw0 c4 (ℓ "乺乶") (ℓ "乶乺") tt tt Eq.refl

wl1659 : Base 4 → ⟪ (ℓ "京亯乫亯京乫乥") ⟫ʷ ≈ ⟪ (ℓ "乥亨享乻享亨乻") ⟫ʷ
wl1659 c4 = lw0 c4 (ℓ "京亯乫亯京乫乥") (ℓ "乥亨享乻享亨乻") tt tt Eq.refl

wl1660 : Base 4 → ⟪ (ℓ "乥亓") ⟫ʷ ≈ ⟪ (ℓ "亏乥") ⟫ʷ
wl1660 c4 = lw4 c4 (ℓ "乥亓") (ℓ "亏乥") tt tt Eq.refl

wl1661 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "乳亘乳") ⟫ʷ
wl1661 c4 = lw4 c4 (ℓ "亘") (ℓ "乳亘乳") tt tt Eq.refl

wl1662 : Base 4 → ⟪ (ℓ "乒亳") ⟫ʷ ≈ ⟪ (ℓ "亳乒享") ⟫ʷ
wl1662 c4 = lw0 c4 (ℓ "乒亳") (ℓ "亳乒享") tt tt Eq.refl

wl1663 : Base 4 → ⟪ (ℓ "也亳") ⟫ʷ ≈ ⟪ (ℓ "亳也") ⟫ʷ
wl1663 c4 = lw0 c4 (ℓ "也亳") (ℓ "亳也") tt tt Eq.refl

wl1664 : Base 4 → ⟪ (ℓ "乒享享") ⟫ʷ ≈ ⟪ (ℓ "乒") ⟫ʷ
wl1664 c4 = lw0 c4 (ℓ "乒享享") (ℓ "乒") tt tt Eq.refl

wl1665 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "乒二乒") ⟫ʷ
wl1665 c4 = lw4 c4 (ℓ "二") (ℓ "乒二乒") tt tt Eq.refl

wl1666 : Base 4 → ⟪ (ℓ "亘乒") ⟫ʷ ≈ ⟪ (ℓ "乒二亘") ⟫ʷ
wl1666 c4 = lw4 c4 (ℓ "亘乒") (ℓ "乒二亘") tt tt Eq.refl

wl1667 : Base 4 → ⟪ (ℓ "二乳") ⟫ʷ ≈ ⟪ (ℓ "乳亘二") ⟫ʷ
wl1667 c4 = lw4 c4 (ℓ "二乳") (ℓ "乳亘二") tt tt Eq.refl

wl1668 : Base 4 → ⟪ (ℓ "亘二亘二亘") ⟫ʷ ≈ ⟪ (ℓ "亘") ⟫ʷ
wl1668 c4 = lw4 c4 (ℓ "亘二亘二亘") (ℓ "亘") tt tt Eq.refl

wl1669 : Base 4 → ⟪ (ℓ "亨乑") ⟫ʷ ≈ ⟪ (ℓ "乑亰") ⟫ʷ
wl1669 c4 = lw0 c4 (ℓ "亨乑") (ℓ "乑亰") tt tt Eq.refl

wl1670 : Base 4 → ⟪ (ℓ "乑亳") ⟫ʷ ≈ ⟪ (ℓ "享乑") ⟫ʷ
wl1670 c4 = lw0 c4 (ℓ "乑亳") (ℓ "享乑") tt tt Eq.refl

wl1671 : Base 4 → ⟪ (ℓ "亰乑") ⟫ʷ ≈ ⟪ (ℓ "乑亨") ⟫ʷ
wl1671 c4 = lw0 c4 (ℓ "亰乑") (ℓ "乑亨") tt tt Eq.refl

wl1672 : Base 4 → ⟪ (ℓ "乑亪") ⟫ʷ ≈ ⟪ (ℓ "亱乑") ⟫ʷ
wl1672 c4 = lw0 c4 (ℓ "乑亪") (ℓ "亱乑") tt tt Eq.refl

wl1673 : Base 4 → ⟪ (ℓ "京享交") ⟫ʷ ≈ ⟪ (ℓ "享京") ⟫ʷ
wl1673 c4 = lw0 c4 (ℓ "京享交") (ℓ "享京") tt tt Eq.refl

wl1674 : Base 4 → ⟪ (ℓ "两乇亃么亃乩严") ⟫ʷ ≈ ⟪ (ℓ "享") ⟫ʷ
wl1674 c4 = lw0 c4 (ℓ "两乇亃么亃乩严") (ℓ "享") tt tt Eq.refl

wl1675 : Base 4 → ⟪ (ℓ "么些") ⟫ʷ ≈ ⟪ (ℓ "些么") ⟫ʷ
wl1675 c4 = lw4 c4 (ℓ "么些") (ℓ "些么") tt tt Eq.refl

wl1676 : Base 4 → ⟪ (ℓ "享交交") ⟫ʷ ≈ ⟪ (ℓ "享") ⟫ʷ
wl1676 c4 = lw0 c4 (ℓ "享交交") (ℓ "享") tt tt Eq.refl

wl1677 : Base 4 → ⟪ (ℓ "乳享") ⟫ʷ ≈ ⟪ (ℓ "享乳亳") ⟫ʷ
wl1677 c4 = lw0 c4 (ℓ "乳享") (ℓ "享乳亳") tt tt Eq.refl

wl1678 : Base 4 → ⟪ (ℓ "乳亳亳") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wl1678 c4 = lw0 c4 (ℓ "乳亳亳") (ℓ "乳") tt tt Eq.refl

wl1679 : Base 4 → ⟪ (ℓ "二亘二亘二") ⟫ʷ ≈ ⟪ (ℓ "二") ⟫ʷ
wl1679 c4 = lw4 c4 (ℓ "二亘二亘二") (ℓ "二") tt tt Eq.refl

wl1680 : Base 4 → ⟪ (ℓ "乑享") ⟫ʷ ≈ ⟪ (ℓ "亳乑") ⟫ʷ
wl1680 c4 = lw0 c4 (ℓ "乑享") (ℓ "亳乑") tt tt Eq.refl

wl1681 : Base 4 → ⟪ (ℓ "乑亱") ⟫ʷ ≈ ⟪ (ℓ "亪乑") ⟫ʷ
wl1681 c4 = lw0 c4 (ℓ "乑亱") (ℓ "亪乑") tt tt Eq.refl

wl1682 : Base 4 → ⟪ (ℓ "乩亳") ⟫ʷ ≈ ⟪ (ℓ "亳乩乢亰") ⟫ʷ
wl1682 c4 = lw0 c4 (ℓ "乩亳") (ℓ "亳乩乢亰") tt tt Eq.refl

wl1683 : Base 4 → ⟪ (ℓ "亰亳") ⟫ʷ ≈ ⟪ (ℓ "亳乤亰") ⟫ʷ
wl1683 c4 = lw0 c4 (ℓ "亰亳") (ℓ "亳乤亰") tt tt Eq.refl

wl1684 : Base 4 → ⟪ (ℓ "乢亳") ⟫ʷ ≈ ⟪ (ℓ "亳乢") ⟫ʷ
wl1684 c4 = lw0 c4 (ℓ "乢亳") (ℓ "亳乢") tt tt Eq.refl

wl1685 : Base 4 → ⟪ (ℓ "乩乢亰乢乤亰") ⟫ʷ ≈ ⟪ (ℓ "乩") ⟫ʷ
wl1685 c4 = lw0 c4 (ℓ "乩乢亰乢乤亰") (ℓ "乩") tt tt Eq.refl

wl1686 : Base 4 → ⟪ (ℓ "乪亳") ⟫ʷ ≈ ⟪ (ℓ "亳乪乣亰") ⟫ʷ
wl1686 c4 = lw0 c4 (ℓ "乪亳") (ℓ "亳乪乣亰") tt tt Eq.refl

wl1687 : Base 4 → ⟪ (ℓ "乣亳") ⟫ʷ ≈ ⟪ (ℓ "亳乣") ⟫ʷ
wl1687 c4 = lw0 c4 (ℓ "乣亳") (ℓ "亳乣") tt tt Eq.refl

wl1688 : Base 4 → ⟪ (ℓ "乪乣亰乣乤亰") ⟫ʷ ≈ ⟪ (ℓ "乪") ⟫ʷ
wl1688 c4 = lw0 c4 (ℓ "乪乣亰乣乤亰") (ℓ "乪") tt tt Eq.refl

wl1689 : Base 4 → ⟪ (ℓ "乻产") ⟫ʷ ≈ ⟪ (ℓ "产乻亨") ⟫ʷ
wl1689 c4 = lw0 c4 (ℓ "乻产") (ℓ "产乻亨") tt tt Eq.refl

wl1690 : Base 4 → ⟪ (ℓ "与乻乻") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
wl1690 c4 = lw1 c4 (ℓ "与乻乻") (ℓ "与") tt tt Eq.refl

wl1691 : Base 4 → ⟪ (ℓ "亨亳") ⟫ʷ ≈ ⟪ (ℓ "亳亨交") ⟫ʷ
wl1691 c4 = lw0 c4 (ℓ "亨亳") (ℓ "亳亨交") tt tt Eq.refl

wl1692 : Base 4 → ⟪ (ℓ "亨交亳") ⟫ʷ ≈ ⟪ (ℓ "亳亨") ⟫ʷ
wl1692 c4 = lw0 c4 (ℓ "亨交亳") (ℓ "亳亨") tt tt Eq.refl

wl1693 : Base 4 → ⟪ (ℓ "之亏与") ⟫ʷ ≈ ⟪ (ℓ "与亏") ⟫ʷ
wl1693 c4 = lw4 c4 (ℓ "之亏与") (ℓ "与亏") tt tt Eq.refl

wl1694 : Base 4 → ⟪ (ℓ "之亏些乎些乏") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏之亏") ⟫ʷ
wl1694 c4 = lw4 c4 (ℓ "之亏些乎些乏") (ℓ "些乎些乏之亏") tt tt Eq.refl

wl1695 : Base 4 → ⟪ (ℓ "丘丯之丰之丨丙") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1695 c4 = lw4 c4 (ℓ "丘丯之丰之丨丙") (ℓ "亏") tt tt Eq.refl

wl1696 : Base 4 → ⟪ (ℓ "亏与") ⟫ʷ ≈ ⟪ (ℓ "与之亏") ⟫ʷ
wl1696 c4 = lw4 c4 (ℓ "亏与") (ℓ "与之亏") tt tt Eq.refl

wl1697 : Base 4 → ⟪ (ℓ "乩与") ⟫ʷ ≈ ⟪ (ℓ "与乩") ⟫ʷ
wl1697 c4 = lw1 c4 (ℓ "乩与") (ℓ "与乩") tt tt Eq.refl

wl1698 : Base 4 → ⟪ (ℓ "乏乩") ⟫ʷ ≈ ⟪ (ℓ "乩乏") ⟫ʷ
wl1698 c4 = lw0 c4 (ℓ "乏乩") (ℓ "乩乏") tt tt Eq.refl

wl1699 : Base 4 → ⟪ (ℓ "乎乩") ⟫ʷ ≈ ⟪ (ℓ "乩乎") ⟫ʷ
wl1699 c4 = lw0 c4 (ℓ "乎乩") (ℓ "乩乎") tt tt Eq.refl

wl1700 : Base 4 → ⟪ (ℓ "乪与") ⟫ʷ ≈ ⟪ (ℓ "与乪") ⟫ʷ
wl1700 c4 = lw1 c4 (ℓ "乪与") (ℓ "与乪") tt tt Eq.refl

wl1701 : Base 4 → ⟪ (ℓ "乎乪") ⟫ʷ ≈ ⟪ (ℓ "乪乎") ⟫ʷ
wl1701 c4 = lw0 c4 (ℓ "乎乪") (ℓ "乪乎") tt tt Eq.refl

wl1702 : Base 4 → ⟪ (ℓ "亚与主与") ⟫ʷ ≈ ⟪ (ℓ "与主与亚") ⟫ʷ
wl1702 c4 = lw4 c4 (ℓ "亚与主与") (ℓ "与主与亚") tt tt Eq.refl

wl1703 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "些乎些乏些乎些乏") ⟫ʷ
wl1703 c4 = lw4 c4 (ℓ "二") (ℓ "些乎些乏些乎些乏") tt tt Eq.refl

wl1704 : Base 4 → ⟪ (ℓ "临二临上") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl1704 c4 = lw4 c4 (ℓ "临二临上") (ℓ "亏") tt tt Eq.refl

wl1705 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "互乇互么互乇互么") ⟫ʷ
wl1705 c4 = lw4 c4 (ℓ "亘") (ℓ "互乇互么互乇互么") tt tt Eq.refl

wl1706 : Base 4 → ⟪ (ℓ "主亘主上") ⟫ʷ ≈ ⟪ (ℓ "些") ⟫ʷ
wl1706 c4 = lw4 c4 (ℓ "主亘主上") (ℓ "些") tt tt Eq.refl

wl1707 : Base 4 → ⟪ (ℓ "临亘临上") ⟫ʷ ≈ ⟪ (ℓ "亚") ⟫ʷ
wl1707 c4 = lw4 c4 (ℓ "临亘临上") (ℓ "亚") tt tt Eq.refl

wl1708 : Base 4 → ⟪ (ℓ "丘丶书丷书丯丙") ⟫ʷ ≈ ⟪ (ℓ "亚") ⟫ʷ
wl1708 c4 = lw4 c4 (ℓ "丘丶书丷书丯丙") (ℓ "亚") tt tt Eq.refl

wl1709 : Base 4 → ⟪ (ℓ "丙亯") ⟫ʷ ≈ ⟪ (ℓ "亯丙") ⟫ʷ
wl1709 c4 = lw0 c4 (ℓ "丙亯") (ℓ "亯丙") tt tt Eq.refl

wl1710 : Base 4 → ⟪ (ℓ "丘丶乜丷乜乢丙") ⟫ʷ ≈ ⟪ (ℓ "亚") ⟫ʷ
wl1710 c4 = lw4 c4 (ℓ "丘丶乜丷乜乢丙") (ℓ "亚") tt tt Eq.refl

wl1711 : Base 4 → ⟪ (ℓ "亐亘亘亘互乇亘亘互么亏") ⟫ʷ ≈ ⟪ (ℓ "亘亘亘互乇亘亘互么亏亐") ⟫ʷ
wl1711 c4 = lw4 c4 (ℓ "亐亘亘亘互乇亘亘互么亏") (ℓ "亘亘亘互乇亘亘互么亏亐") tt tt Eq.refl
