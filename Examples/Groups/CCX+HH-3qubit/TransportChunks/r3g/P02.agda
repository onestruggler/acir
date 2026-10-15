{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P02 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02345 as C02345
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02346 as C02346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02347 as C02347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02356 as C02356
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02357 as C02357
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02367 as C02367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02456 as C02456
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02457 as C02457
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02467 as C02467
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3g_ij02567 as C02567

private
  a b : Fin 8
  a = (zero)
  b = (suc (suc (zero)))

translate : (c d t : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : d < t) →
  .(p4 : c < t) →
  (dX d t) • (dK a b c d) ≈ (dK a b c t) • (dX d t)
translate (zero) d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (zero) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (zero)) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = C02345.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C02346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C02347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C02356.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C02357.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C02367.proved
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
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = C02456.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C02457.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C02467.proved
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
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 = C02567.proved
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
