{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2f.P0356 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03561247 as C03561247

private
  a b c d : Fin 8
  a = (zero)
  b = (suc (suc (suc (zero))))
  c = (suc (suc (suc (suc (suc (zero))))))
  d = (suc (suc (suc (suc (suc (suc (zero)))))))

translate : (e f g h : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : e < f) →
  .(p4 : f < g) →
  .(p5 : g < h) →
  (ne0 : a Eq.≢ e) →
  (ne1 : a Eq.≢ f) →
  (ne2 : a Eq.≢ g) →
  (ne3 : a Eq.≢ h) →
  (ne4 : b Eq.≢ e) →
  (ne5 : b Eq.≢ f) →
  (ne6 : b Eq.≢ g) →
  (ne7 : b Eq.≢ h) →
  (ne8 : c Eq.≢ e) →
  (ne9 : c Eq.≢ f) →
  (ne10 : c Eq.≢ g) →
  (ne11 : c Eq.≢ h) →
  (ne12 : d Eq.≢ e) →
  (ne13 : d Eq.≢ f) →
  (ne14 : d Eq.≢ g) →
  (ne15 : d Eq.≢ h) →
  (dK a b c d) • (dK e f g h) ≈ (dK e f g h) • (dK a b c d)
translate (zero) f g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (zero) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (zero)) (suc (zero)) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (zero)) (suc (suc (zero))) (zero) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (zero)) (suc (suc (zero))) (suc (zero)) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne6 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne11 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne15 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = C03561247.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne10 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne14 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p5)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p5)
translate (suc (zero)) (suc (suc (suc (zero)))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne5 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p4)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p4)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne10 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne14 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p5)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p5)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne9 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne13 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p4)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p4)
translate (suc (suc (zero))) (zero) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (zero))) (suc (zero)) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) (suc (suc (zero))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne5 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne10 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne14 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p5)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne9 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne13 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p4)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p4)
translate (suc (suc (suc (zero)))) f g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne4 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (zero) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne9 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne13 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p4)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p4)
translate (suc (suc (suc (suc (suc (zero)))))) f g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne8 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) f g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim (ne12 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p3)
