{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2a.P5 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B02 using (module r2a_ij5601 ; module r2a_ij5602 ; module r2a_ij5603 ; module r2a_ij5604 ; module r2a_ij5607 ; module r2a_ij5612 ; module r2a_ij5613 ; module r2a_ij5614 ; module r2a_ij5617 ; module r2a_ij5623 ; module r2a_ij5624 ; module r2a_ij5627 ; module r2a_ij5634 ; module r2a_ij5637 ; module r2a_ij5647)
open import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B03 using (module r2a_ij5701 ; module r2a_ij5702 ; module r2a_ij5703 ; module r2a_ij5704 ; module r2a_ij5706 ; module r2a_ij5712 ; module r2a_ij5713 ; module r2a_ij5714 ; module r2a_ij5716 ; module r2a_ij5723 ; module r2a_ij5724 ; module r2a_ij5726 ; module r2a_ij5734 ; module r2a_ij5736 ; module r2a_ij5746)

private
  a : Fin 8
  a = (suc (suc (suc (suc (suc (zero))))))

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
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5601.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5602.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5603.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5604.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5607.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5612.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5613.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5614.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5617.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5623.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5624.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5627.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5634.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5637.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5647.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5701.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5702.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5703.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5704.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5706.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5712.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5713.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5714.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5716.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5723.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5724.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5726.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5734.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5736.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij5746.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
