{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2a.P6 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6701 as C6701
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6702 as C6702
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6703 as C6703
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6704 as C6704
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6705 as C6705
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6712 as C6712
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6713 as C6713
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6714 as C6714
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6715 as C6715
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6723 as C6723
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6724 as C6724
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6725 as C6725
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6734 as C6734
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6735 as C6735
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6745 as C6745

private
  a : Fin 8
  a = (suc (suc (suc (suc (suc (suc (zero)))))))

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
translate (suc (suc (zero))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = C6701.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C6702.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C6703.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C6704.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C6705.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C6712.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C6713.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C6714.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C6715.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C6723.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C6724.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C6725.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = C6734.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C6735.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C6745.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
