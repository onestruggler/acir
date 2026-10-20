{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2a.P1 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1203 as C1203
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1204 as C1204
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1205 as C1205
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1206 as C1206
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1207 as C1207
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1234 as C1234
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1235 as C1235
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1236 as C1236
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1237 as C1237
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1245 as C1245
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1246 as C1246
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1247 as C1247
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1256 as C1256
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1257 as C1257
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1267 as C1267
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1302 as C1302
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1304 as C1304
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1305 as C1305
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1306 as C1306
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1307 as C1307
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1324 as C1324
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1325 as C1325
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1326 as C1326
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1327 as C1327
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1345 as C1345
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1346 as C1346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1347 as C1347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1356 as C1356
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1357 as C1357
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1367 as C1367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1402 as C1402
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1403 as C1403
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1405 as C1405
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1406 as C1406
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1407 as C1407
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1423 as C1423
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1425 as C1425
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1426 as C1426
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1427 as C1427
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1435 as C1435
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1436 as C1436
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1437 as C1437
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1456 as C1456
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1457 as C1457
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1467 as C1467
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1502 as C1502
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1503 as C1503
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1504 as C1504
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1506 as C1506
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1507 as C1507
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1523 as C1523
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1524 as C1524
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1526 as C1526
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1527 as C1527
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1534 as C1534
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1536 as C1536
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1537 as C1537
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1546 as C1546
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1547 as C1547
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1567 as C1567
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1602 as C1602
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1603 as C1603
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1604 as C1604
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1605 as C1605
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1607 as C1607
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1623 as C1623
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1624 as C1624
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1625 as C1625
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1627 as C1627
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1634 as C1634
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1635 as C1635
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1637 as C1637
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1645 as C1645
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1647 as C1647
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1657 as C1657
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1702 as C1702
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1703 as C1703
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1704 as C1704
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1705 as C1705
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1706 as C1706
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1723 as C1723
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1724 as C1724
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1725 as C1725
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1726 as C1726
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1734 as C1734
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1735 as C1735
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1736 as C1736
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1745 as C1745
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1746 as C1746
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1756 as C1756

private
  a : Fin 8
  a = (suc (zero))

translate : (b c d : Fin 8) →
  .(p0 : a < b) →
  .(p1 : c < d) →
  (ne0 : a Eq.≢ c) →
  (ne1 : a Eq.≢ d) →
  (ne2 : b Eq.≢ c) →
  (ne3 : b Eq.≢ d) →
  (dX a b) • (dX c d) ≈ (dX c d) • (dX a b)
translate (zero) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (zero))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (zero))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1203.proved
translate (suc (suc (zero))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1204.proved
translate (suc (suc (zero))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1205.proved
translate (suc (suc (zero))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1206.proved
translate (suc (suc (zero))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1207.proved
translate (suc (suc (zero))) (suc (zero)) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (zero))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1234.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1235.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1236.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1237.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1245.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1246.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1247.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1256.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1257.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1267.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (zero)))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (zero)))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C1302.proved
translate (suc (suc (suc (zero)))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (zero)))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1304.proved
translate (suc (suc (suc (zero)))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1305.proved
translate (suc (suc (suc (zero)))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1306.proved
translate (suc (suc (suc (zero)))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1307.proved
translate (suc (suc (suc (zero)))) (suc (zero)) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1324.proved
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1325.proved
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1326.proved
translate (suc (suc (suc (zero)))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1327.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1345.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1356.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1357.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1367.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (zero))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C1402.proved
translate (suc (suc (suc (suc (zero))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1403.proved
translate (suc (suc (suc (suc (zero))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1405.proved
translate (suc (suc (suc (suc (zero))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1406.proved
translate (suc (suc (suc (suc (zero))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1407.proved
translate (suc (suc (suc (suc (zero))))) (suc (zero)) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1423.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1425.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1426.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1427.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1435.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1436.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1437.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1456.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1457.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1467.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C1502.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1503.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1504.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1506.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1507.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1523.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1524.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1526.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1527.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1534.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1536.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1537.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1546.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1547.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C1602.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1603.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1604.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1605.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1607.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1623.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1624.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1625.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1627.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1634.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1635.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1637.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1645.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1647.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C1657.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C1702.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1703.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1704.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1705.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1706.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C1723.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1724.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1725.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1726.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C1734.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1735.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1736.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C1745.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1746.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C1756.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
