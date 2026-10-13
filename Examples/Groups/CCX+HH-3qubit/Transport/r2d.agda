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
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij01 as C01
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij02 as C02
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij03 as C03
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij04 as C04
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij05 as C05
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij06 as C06
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij07 as C07
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij10 as C10
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij12 as C12
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij13 as C13
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij14 as C14
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij15 as C15
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij16 as C16
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij17 as C17
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij20 as C20
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij21 as C21
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij23 as C23
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij24 as C24
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij25 as C25
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij26 as C26
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij27 as C27
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij30 as C30
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij31 as C31
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij32 as C32
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij34 as C34
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij35 as C35
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij36 as C36
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij37 as C37
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij40 as C40
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij41 as C41
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij42 as C42
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij43 as C43
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij45 as C45
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij46 as C46
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij47 as C47
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij50 as C50
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij51 as C51
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij52 as C52
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij53 as C53
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij54 as C54
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij56 as C56
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij57 as C57
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij60 as C60
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij61 as C61
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij62 as C62
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij63 as C63
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij64 as C64
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij65 as C65
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij67 as C67
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij70 as C70
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij71 as C71
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij72 as C72
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij73 as C73
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij74 as C74
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij75 as C75
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij76 as C76

translate : (a b : Fin 8) →
  (ne0 : a Eq.≢ b) →
  (dM a) • (dM b) ≈ (dM b) • (dM a)
translate (zero) (zero) ne0 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (zero)) ne0 = C01.proved
translate (zero) (suc (suc (zero))) ne0 = C02.proved
translate (zero) (suc (suc (suc (zero)))) ne0 = C03.proved
translate (zero) (suc (suc (suc (suc (zero))))) ne0 = C04.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) ne0 = C05.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C06.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C07.proved
translate (suc (zero)) (zero) ne0 = C10.proved
translate (suc (zero)) (suc (zero)) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) ne0 = C12.proved
translate (suc (zero)) (suc (suc (suc (zero)))) ne0 = C13.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) ne0 = C14.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) ne0 = C15.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C16.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C17.proved
translate (suc (suc (zero))) (zero) ne0 = C20.proved
translate (suc (suc (zero))) (suc (zero)) ne0 = C21.proved
translate (suc (suc (zero))) (suc (suc (zero))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) ne0 = C23.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) ne0 = C24.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) ne0 = C25.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C26.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C27.proved
translate (suc (suc (suc (zero)))) (zero) ne0 = C30.proved
translate (suc (suc (suc (zero)))) (suc (zero)) ne0 = C31.proved
translate (suc (suc (suc (zero)))) (suc (suc (zero))) ne0 = C32.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) ne0 = C34.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) ne0 = C35.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C36.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C37.proved
translate (suc (suc (suc (suc (zero))))) (zero) ne0 = C40.proved
translate (suc (suc (suc (suc (zero))))) (suc (zero)) ne0 = C41.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) ne0 = C42.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) ne0 = C43.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = C45.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C46.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C47.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) ne0 = C50.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) ne0 = C51.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) ne0 = C52.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) ne0 = C53.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) ne0 = C54.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C56.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C57.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) ne0 = C60.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) ne0 = C61.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) ne0 = C62.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) ne0 = C63.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) ne0 = C64.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = C65.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = C67.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) ne0 = C70.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) ne0 = C71.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) ne0 = C72.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) ne0 = C73.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) ne0 = C74.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) ne0 = C75.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) ne0 = C76.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) ne0 = ⊥-elim (ne0 Eq.refl)
