{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r2d where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_B00 using (module r2d_ij01 ; module r2d_ij02 ; module r2d_ij03 ; module r2d_ij04 ; module r2d_ij05 ; module r2d_ij06 ; module r2d_ij07 ; module r2d_ij10 ; module r2d_ij12 ; module r2d_ij13 ; module r2d_ij14 ; module r2d_ij15 ; module r2d_ij16 ; module r2d_ij17 ; module r2d_ij20 ; module r2d_ij21 ; module r2d_ij23 ; module r2d_ij24 ; module r2d_ij25 ; module r2d_ij26 ; module r2d_ij27 ; module r2d_ij30 ; module r2d_ij31 ; module r2d_ij32 ; module r2d_ij34 ; module r2d_ij35 ; module r2d_ij36 ; module r2d_ij37 ; module r2d_ij40 ; module r2d_ij41 ; module r2d_ij42 ; module r2d_ij43 ; module r2d_ij45 ; module r2d_ij46 ; module r2d_ij47 ; module r2d_ij50 ; module r2d_ij51 ; module r2d_ij52 ; module r2d_ij53 ; module r2d_ij54 ; module r2d_ij56 ; module r2d_ij57 ; module r2d_ij60 ; module r2d_ij61 ; module r2d_ij62 ; module r2d_ij63 ; module r2d_ij64 ; module r2d_ij65 ; module r2d_ij67 ; module r2d_ij70 ; module r2d_ij71 ; module r2d_ij72 ; module r2d_ij73 ; module r2d_ij74 ; module r2d_ij75 ; module r2d_ij76)

translate : (a b : Fin 8) →
  (ne0 : a Eq.≢ b) →
  (dM a) • (dM b) ≈ (dM b) • (dM a)
translate (zero) (zero) ne0 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (zero)) ne0 = r2d_ij01.proved
translate (zero) (suc (suc (zero))) ne0 = r2d_ij02.proved
translate (zero) (suc (suc (suc (zero)))) ne0 = r2d_ij03.proved
translate (zero) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij04.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij05.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij06.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij07.proved
translate (suc (zero)) (zero) ne0 = r2d_ij10.proved
translate (suc (zero)) (suc (zero)) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) ne0 = r2d_ij12.proved
translate (suc (zero)) (suc (suc (suc (zero)))) ne0 = r2d_ij13.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij14.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij15.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij16.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij17.proved
translate (suc (suc (zero))) (zero) ne0 = r2d_ij20.proved
translate (suc (suc (zero))) (suc (zero)) ne0 = r2d_ij21.proved
translate (suc (suc (zero))) (suc (suc (zero))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) ne0 = r2d_ij23.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij24.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij25.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij26.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij27.proved
translate (suc (suc (suc (zero)))) (zero) ne0 = r2d_ij30.proved
translate (suc (suc (suc (zero)))) (suc (zero)) ne0 = r2d_ij31.proved
translate (suc (suc (suc (zero)))) (suc (suc (zero))) ne0 = r2d_ij32.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij34.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij35.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij36.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij37.proved
translate (suc (suc (suc (suc (zero))))) (zero) ne0 = r2d_ij40.proved
translate (suc (suc (suc (suc (zero))))) (suc (zero)) ne0 = r2d_ij41.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) ne0 = r2d_ij42.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) ne0 = r2d_ij43.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij45.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij46.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij47.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) ne0 = r2d_ij50.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) ne0 = r2d_ij51.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) ne0 = r2d_ij52.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) ne0 = r2d_ij53.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij54.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij56.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij57.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) ne0 = r2d_ij60.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) ne0 = r2d_ij61.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) ne0 = r2d_ij62.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) ne0 = r2d_ij63.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij64.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij65.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = r2d_ij67.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) ne0 = r2d_ij70.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) ne0 = r2d_ij71.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) ne0 = r2d_ij72.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) ne0 = r2d_ij73.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) ne0 = r2d_ij74.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = r2d_ij75.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = r2d_ij76.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = ⊥-elim (ne0 Eq.refl)
