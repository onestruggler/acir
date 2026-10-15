{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r2e where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P01 as P01
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P02 as P02
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P03 as P03
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P04 as P04
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P05 as P05
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P06 as P06
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P07 as P07
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P10 as P10
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P12 as P12
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P13 as P13
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P14 as P14
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P15 as P15
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P16 as P16
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P17 as P17
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P20 as P20
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P21 as P21
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P23 as P23
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P24 as P24
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P25 as P25
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P26 as P26
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P27 as P27
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P30 as P30
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P31 as P31
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P32 as P32
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P34 as P34
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P35 as P35
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P36 as P36
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P37 as P37
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P40 as P40
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P41 as P41
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P42 as P42
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P43 as P43
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P45 as P45
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P46 as P46
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P47 as P47
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P50 as P50
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P51 as P51
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P52 as P52
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P53 as P53
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P54 as P54
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P56 as P56
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P57 as P57
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P60 as P60
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P61 as P61
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P62 as P62
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P63 as P63
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P64 as P64
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P65 as P65
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P67 as P67
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P70 as P70
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P71 as P71
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P72 as P72
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P73 as P73
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P74 as P74
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P75 as P75
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r2e.P76 as P76

translate : (a b c d e : Fin 8) →
  .(p0 : b < c) →
  .(p1 : c < d) →
  .(p2 : d < e) →
  (ne0 : a Eq.≢ b) →
  (ne1 : a Eq.≢ c) →
  (ne2 : a Eq.≢ d) →
  (ne3 : a Eq.≢ e) →
  (dM a) • (dK b c d e) ≈ (dK b c d e) • (dM a)
translate (zero) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P01.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (zero) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P02.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (zero) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P03.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (zero) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P04.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (zero) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P05.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P06.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P07.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P10.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P12.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P13.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P14.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P15.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P16.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P17.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P20.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P21.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P23.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P24.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P25.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P26.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P27.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P30.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P31.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P32.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P34.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P35.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P36.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P37.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P40.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P41.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P42.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P43.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P45.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P46.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P47.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P50.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P51.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P52.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P53.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P54.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P56.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P57.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P60.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P61.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P62.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P63.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P64.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P65.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P67.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P70.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P71.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P72.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P73.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P74.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P75.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = P76.translate c d e p0 p1 p2 ne0 ne1 ne2 ne3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d e p0 p1 p2 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
