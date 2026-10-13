{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r1a where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij01 as C01
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij02 as C02
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij03 as C03
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij04 as C04
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij05 as C05
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij06 as C06
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij07 as C07
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij12 as C12
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij13 as C13
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij14 as C14
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij15 as C15
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij16 as C16
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij17 as C17
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij23 as C23
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij24 as C24
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij25 as C25
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij26 as C26
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij27 as C27
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij34 as C34
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij35 as C35
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij36 as C36
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij37 as C37
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij45 as C45
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij46 as C46
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij47 as C47
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij56 as C56
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij57 as C57
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij67 as C67

translate : (a b : Fin 8) →
  .(p0 : a < b) →
  (dX a b) • (dX a b) ≈ ε
translate (zero) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) p0 = C01.proved
translate (zero) (suc (suc (zero))) p0 = C02.proved
translate (zero) (suc (suc (suc (zero)))) p0 = C03.proved
translate (zero) (suc (suc (suc (suc (zero))))) p0 = C04.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) p0 = C05.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = C06.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C07.proved
translate (suc (zero)) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) p0 = C12.proved
translate (suc (zero)) (suc (suc (suc (zero)))) p0 = C13.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) p0 = C14.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 = C15.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = C16.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C17.proved
translate (suc (suc (zero))) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) p0 = C23.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 = C24.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 = C25.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = C26.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C27.proved
translate (suc (suc (suc (zero)))) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 = C34.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 = C35.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = C36.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C37.proved
translate (suc (suc (suc (suc (zero))))) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 = C45.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = C46.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C47.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = C56.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C57.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = C67.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
