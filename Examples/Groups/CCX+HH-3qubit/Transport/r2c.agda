{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r2c where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P01 as P01
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P02 as P02
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P03 as P03
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P04 as P04
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P05 as P05
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P06 as P06
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P07 as P07
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P12 as P12
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P13 as P13
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P14 as P14
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P15 as P15
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P16 as P16
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P17 as P17
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P23 as P23
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P24 as P24
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P25 as P25
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P26 as P26
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P27 as P27
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P34 as P34
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P35 as P35
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P36 as P36
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P37 as P37
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P45 as P45
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P46 as P46
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P47 as P47
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P56 as P56
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P57 as P57
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2c.P67 as P67

translate : (a b c d e f : Fin 8) →
  .(p0 : a < b) →
  .(p1 : c < d) →
  .(p2 : d < e) →
  .(p3 : e < f) →
  (ne0 : a Eq.≢ c) →
  (ne1 : a Eq.≢ d) →
  (ne2 : a Eq.≢ e) →
  (ne3 : a Eq.≢ f) →
  (ne4 : b Eq.≢ c) →
  (ne5 : b Eq.≢ d) →
  (ne6 : b Eq.≢ e) →
  (ne7 : b Eq.≢ f) →
  (dX a b) • (dK c d e f) ≈ (dK c d e f) • (dX a b)
translate (zero) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P01.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (zero) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P02.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (zero) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P03.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (zero) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P04.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (zero) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P05.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P06.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P07.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (zero)) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P12.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (zero)) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P13.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (zero)) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P14.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P15.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P16.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P17.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (zero))) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P23.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P24.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P25.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P26.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P27.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (zero)))) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P34.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P35.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P36.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P37.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (zero))))) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P45.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P46.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P47.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (suc (zero)))))) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P56.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P57.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = P67.translate c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
