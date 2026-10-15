{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r6a where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0123 as P0123
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0124 as P0124
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0125 as P0125
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0126 as P0126
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0127 as P0127
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0134 as P0134
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0135 as P0135
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0136 as P0136
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0137 as P0137
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0145 as P0145
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0146 as P0146
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0147 as P0147
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0156 as P0156
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0157 as P0157
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0167 as P0167
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0234 as P0234
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0235 as P0235
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0236 as P0236
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0237 as P0237
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0245 as P0245
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0246 as P0246
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0247 as P0247
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0256 as P0256
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0257 as P0257
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0267 as P0267
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0345 as P0345
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0346 as P0346
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0347 as P0347
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0356 as P0356
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0357 as P0357
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0367 as P0367
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0456 as P0456
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0457 as P0457
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0467 as P0467
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0567 as P0567
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1234 as P1234
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1235 as P1235
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1236 as P1236
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1237 as P1237
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1245 as P1245
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1246 as P1246
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1247 as P1247
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1256 as P1256
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1257 as P1257
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1267 as P1267
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1345 as P1345
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1346 as P1346
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1347 as P1347
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1356 as P1356
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1357 as P1357
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1367 as P1367
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1456 as P1456
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1457 as P1457
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1467 as P1467
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P1567 as P1567
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2345 as P2345
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2346 as P2346
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2347 as P2347
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2356 as P2356
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2357 as P2357
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2367 as P2367
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2456 as P2456
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2457 as P2457
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2467 as P2467
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P2567 as P2567
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P3456 as P3456
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P3457 as P3457
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P3467 as P3467
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P3567 as P3567
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P4567 as P4567

translate : (a b c d e f g h : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : d < e) →
  .(p4 : e < f) →
  .(p5 : f < g) →
  .(p6 : g < h) →
  .(p7 : a < e) →
  (dM a) • (dM e) • (dX a e) • (dK e f g h) • (dK a b c d) • (dX d e) • (dK a b c d) • (dK e f g h) • (dX a e) • (dM a) • (dM e) ≈ (dK e f g h) • (dK a b c d) • (dX d e) • (dK a b c d) • (dK e f g h)
translate (zero) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (zero)) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (zero)) (suc (suc (zero))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0123.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0124.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0125.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0126.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0127.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0134.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0135.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0136.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0137.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0145.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0146.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0147.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0156.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0157.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0167.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (zero) (suc (suc (zero))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (zero))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (zero))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0234.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0235.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0236.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0237.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0245.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0246.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0247.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0256.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0257.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0267.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (zero) (suc (suc (suc (zero)))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (zero)))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0345.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0346.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0347.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0356.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0357.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0367.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0456.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0457.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0467.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P0567.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (zero)) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (zero))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1234.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1235.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1236.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1237.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1245.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1246.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1247.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1256.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1257.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1267.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1345.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1346.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1347.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1356.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1357.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1367.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1456.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1457.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1467.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P1567.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (zero))) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2345.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2346.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2347.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2356.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2357.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2367.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2456.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2457.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2467.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P2567.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (zero)))) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P3456.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P3457.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P3467.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P3567.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (zero))))) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = P4567.translate e f g h p0 p1 p2 p3 p4 p5 p6 p7
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
