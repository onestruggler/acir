{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r3f where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P01 as P01
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P02 as P02
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P03 as P03
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P04 as P04
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P05 as P05
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P06 as P06
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P07 as P07
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P12 as P12
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P13 as P13
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P14 as P14
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P15 as P15
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P16 as P16
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P17 as P17
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P23 as P23
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P24 as P24
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P25 as P25
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P26 as P26
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P27 as P27
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P34 as P34
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P35 as P35
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P36 as P36
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P37 as P37
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P45 as P45
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P46 as P46
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P47 as P47
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P56 as P56
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P57 as P57
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3f.P67 as P67

translate : (a b c z d : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < z) →
  .(p3 : z < d) →
  .(p4 : c < d) →
  .(p5 : b < z) →
  (dX c z) • (dK a b c d) ≈ (dK a b z d) • (dX c z)
translate (zero) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = P01.translate c z d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = P02.translate c z d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = P03.translate c z d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = P04.translate c z d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = P05.translate c z d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = P06.translate c z d p0 p1 p2 p3 p4 p5
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P07.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = P12.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = P13.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = P14.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = P15.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = P16.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P17.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = P23.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = P24.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = P25.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = P26.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P27.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = P34.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = P35.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = P36.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P37.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (zero))))) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = P45.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = P46.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P47.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (zero)))))) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = P56.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P57.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = P67.translate c z d p0 p1 p2 p3 p4 p5
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c z d p0 p1 p2 p3 p4 p5 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
