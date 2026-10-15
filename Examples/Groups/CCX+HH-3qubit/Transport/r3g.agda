{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r3g where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P01 as P01
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P02 as P02
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P03 as P03
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P04 as P04
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P05 as P05
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P06 as P06
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P07 as P07
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P12 as P12
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P13 as P13
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P14 as P14
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P15 as P15
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P16 as P16
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P17 as P17
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P23 as P23
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P24 as P24
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P25 as P25
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P26 as P26
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P27 as P27
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P34 as P34
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P35 as P35
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P36 as P36
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P37 as P37
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P45 as P45
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P46 as P46
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P47 as P47
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P56 as P56
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P57 as P57
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3g.P67 as P67

translate : (a b c d t : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : d < t) →
  .(p4 : c < t) →
  (dX d t) • (dK a b c d) ≈ (dK a b c t) • (dX d t)
translate (zero) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) c d t p0 p1 p2 p3 p4 = P01.translate c d t p0 p1 p2 p3 p4
translate (zero) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = P02.translate c d t p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = P03.translate c d t p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = P04.translate c d t p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = P05.translate c d t p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = P06.translate c d t p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P07.translate c d t p0 p1 p2 p3 p4
translate (suc (zero)) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = P12.translate c d t p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = P13.translate c d t p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = P14.translate c d t p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = P15.translate c d t p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = P16.translate c d t p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P17.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (zero))) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = P23.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = P24.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = P25.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = P26.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P27.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = P34.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = P35.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = P36.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P37.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (zero))))) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = P45.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = P46.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P47.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (zero)))))) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = P56.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P57.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = P67.translate c d t p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d t p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
