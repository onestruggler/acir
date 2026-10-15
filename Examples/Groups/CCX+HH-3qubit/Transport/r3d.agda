{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r3d where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P01 as P01
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P02 as P02
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P03 as P03
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P04 as P04
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P05 as P05
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P06 as P06
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P07 as P07
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P12 as P12
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P13 as P13
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P14 as P14
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P15 as P15
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P16 as P16
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P17 as P17
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P23 as P23
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P24 as P24
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P25 as P25
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P26 as P26
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P27 as P27
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P34 as P34
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P35 as P35
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P36 as P36
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P37 as P37
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P45 as P45
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P46 as P46
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P47 as P47
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P56 as P56
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P57 as P57
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r3d.P67 as P67

translate : (a x b c d : Fin 8) →
  .(p0 : a < x) →
  .(p1 : x < b) →
  .(p2 : b < c) →
  .(p3 : c < d) →
  .(p4 : a < b) →
  (dX a x) • (dK a b c d) ≈ (dK x b c d) • (dX a x)
translate (zero) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) b c d p0 p1 p2 p3 p4 = P01.translate b c d p0 p1 p2 p3 p4
translate (zero) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = P02.translate b c d p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = P03.translate b c d p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = P04.translate b c d p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = P05.translate b c d p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = P06.translate b c d p0 p1 p2 p3 p4
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P07.translate b c d p0 p1 p2 p3 p4
translate (suc (zero)) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = P12.translate b c d p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = P13.translate b c d p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = P14.translate b c d p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = P15.translate b c d p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = P16.translate b c d p0 p1 p2 p3 p4
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P17.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (zero))) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = P23.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = P24.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = P25.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = P26.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P27.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = P34.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = P35.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = P36.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P37.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (zero))))) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = P45.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = P46.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P47.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (zero)))))) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = P56.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P57.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = P67.translate b c d p0 p1 p2 p3 p4
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 p4 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
