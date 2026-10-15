{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P20 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20134 as C20134
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20135 as C20135
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20136 as C20136
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20137 as C20137
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20145 as C20145
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20146 as C20146
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20147 as C20147
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20156 as C20156
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20157 as C20157
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20167 as C20167
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20345 as C20345
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20346 as C20346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20347 as C20347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20356 as C20356
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20357 as C20357
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20367 as C20367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20456 as C20456
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20457 as C20457
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20467 as C20467
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20567 as C20567

private
  a b : Fin 8
  a = (suc (suc (zero)))
  b = (zero)

translate : (c d e : Fin 8) →
  .(p0 : b < c) →
  .(p1 : c < d) →
  .(p2 : d < e) →
  (ne0 : a Eq.≢ b) →
  (ne1 : a Eq.≢ c) →
  (ne2 : a Eq.≢ d) →
  (ne3 : a Eq.≢ e) →
  (dM a) • (dK b c d e) ≈ (dK b c d e) • (dM a)
translate (zero) d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (zero)) (suc (suc (suc (zero)))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20134.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20135.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20136.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20137.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20145.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20146.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20147.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20156.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20157.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20167.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (zero))) d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (zero)))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20345.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20356.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20357.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20367.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (zero))))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20456.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20457.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20467.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C20567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
