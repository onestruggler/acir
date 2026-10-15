{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P01 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01234 as C01234
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01235 as C01235
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01236 as C01236
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01237 as C01237
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01245 as C01245
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01246 as C01246
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01247 as C01247
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01256 as C01256
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01257 as C01257
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01267 as C01267
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01345 as C01345
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01346 as C01346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01347 as C01347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01356 as C01356
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01357 as C01357
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01367 as C01367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01456 as C01456
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01457 as C01457
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01467 as C01467
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij01567 as C01567

private
  a b : Fin 8
  a = (zero)
  b = (suc (zero))

translate : (c d t : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : d < t) →
  .(p4 : c < t) →
  (dX d t) • (dK a b c d) ≈ (dK a b c t) • (dX d t)
translate (zero) d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = C01234.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = C01235.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C01236.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01237.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = C01245.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C01246.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01247.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C01256.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01257.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01267.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p3)
translate (suc (suc (suc (zero)))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = C01345.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C01346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C01356.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01357.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01367.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p3)
translate (suc (suc (suc (suc (zero))))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C01456.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01457.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01467.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C01567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
