{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r3e where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P01 as P01
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P02 as P02
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P03 as P03
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P04 as P04
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P05 as P05
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P06 as P06
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P07 as P07
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P12 as P12
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P13 as P13
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P14 as P14
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P15 as P15
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P16 as P16
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P17 as P17
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P23 as P23
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P24 as P24
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P25 as P25
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P26 as P26
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P27 as P27
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P34 as P34
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P35 as P35
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P36 as P36
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P37 as P37
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P45 as P45
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P46 as P46
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P47 as P47
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P56 as P56
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P57 as P57
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3e.P67 as P67

translate : (a b y c d : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < y) →
  .(p2 : y < c) →
  .(p3 : c < d) →
  .(p4 : b < c) →
  .(p5 : a < y) →
  (dX b y) • (dK a b c d) ≈ (dK a y c d) • (dX b y)
translate (zero) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = P01.translate y c d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = P02.translate y c d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = P03.translate y c d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = P04.translate y c d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = P05.translate y c d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = P06.translate y c d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P07.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = P12.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = P13.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = P14.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = P15.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = P16.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P17.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = P23.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = P24.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = P25.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = P26.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P27.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = P34.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = P35.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = P36.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P37.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (zero))))) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = P45.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = P46.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P47.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (zero)))))) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = P56.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P57.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = P67.translate y c d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) y c d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
