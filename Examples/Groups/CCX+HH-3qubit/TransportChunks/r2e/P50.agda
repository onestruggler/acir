{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P50 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50123 as C50123
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50124 as C50124
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50126 as C50126
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50127 as C50127
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50134 as C50134
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50136 as C50136
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50137 as C50137
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50146 as C50146
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50147 as C50147
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50167 as C50167
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50234 as C50234
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50236 as C50236
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50237 as C50237
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50246 as C50246
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50247 as C50247
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50267 as C50267
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50346 as C50346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50347 as C50347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50367 as C50367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50467 as C50467

private
  a b : Fin 8
  a = (suc (suc (suc (suc (suc (zero))))))
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
translate (suc (zero)) (suc (suc (zero))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (zero))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50123.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50124.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50126.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50127.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50134.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50136.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50137.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50146.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50147.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50167.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (zero))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50234.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50236.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50237.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50246.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50247.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50267.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (zero)))) (zero) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (zero)) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50367.proved
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
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = C50467.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
translate (suc (suc (suc (suc (suc (zero)))))) d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
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
