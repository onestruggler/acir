{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r3a where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij012 as C012
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij013 as C013
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij014 as C014
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij015 as C015
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij016 as C016
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij017 as C017
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij023 as C023
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij024 as C024
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij025 as C025
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij026 as C026
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij027 as C027
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij034 as C034
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij035 as C035
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij036 as C036
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij037 as C037
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij045 as C045
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij046 as C046
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij047 as C047
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij056 as C056
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij057 as C057
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij067 as C067
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij123 as C123
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij124 as C124
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij125 as C125
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij126 as C126
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij127 as C127
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij134 as C134
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij135 as C135
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij136 as C136
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij137 as C137
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij145 as C145
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij146 as C146
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij147 as C147
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij156 as C156
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij157 as C157
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij167 as C167
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij234 as C234
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij235 as C235
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij236 as C236
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij237 as C237
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij245 as C245
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij246 as C246
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij247 as C247
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij256 as C256
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij257 as C257
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij267 as C267
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij345 as C345
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij346 as C346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij347 as C347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij356 as C356
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij357 as C357
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij367 as C367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij456 as C456
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij457 as C457
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij467 as C467
import Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij567 as C567

translate : (a x b : Fin 8) →
  .(p0 : a < x) →
  .(p1 : x < b) →
  .(p2 : a < b) →
  (dX a x) • (dX a b) ≈ (dX x b) • (dX a x)
translate (zero) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (zero)) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (zero)) (suc (suc (zero))) p0 p1 p2 = C012.proved
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 p2 = C013.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 p2 = C014.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C015.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C016.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C017.proved
translate (zero) (suc (suc (zero))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (zero))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (zero))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 p2 = C023.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = C024.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C025.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C026.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C027.proved
translate (zero) (suc (suc (suc (zero)))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = C034.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C035.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C036.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C037.proved
translate (zero) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C045.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C046.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C047.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C056.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C057.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C067.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (zero)) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (zero))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 p2 = C123.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = C124.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C125.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C126.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C127.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = C134.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C135.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C136.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C137.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C145.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C146.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C147.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C156.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C157.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C167.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (zero))) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = C234.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C235.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C236.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C237.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C245.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C246.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C247.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C256.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C257.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C267.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (zero)))) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = C345.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C356.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C357.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C367.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (zero))))) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = C456.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C457.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C467.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = C567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b p0 p1 p2 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
