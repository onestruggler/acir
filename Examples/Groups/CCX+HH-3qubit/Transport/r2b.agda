{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r2b where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij012 as C012
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij013 as C013
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij014 as C014
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij015 as C015
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij016 as C016
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij017 as C017
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij021 as C021
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij023 as C023
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij024 as C024
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij025 as C025
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij026 as C026
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij027 as C027
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij031 as C031
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij032 as C032
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij034 as C034
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij035 as C035
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij036 as C036
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij037 as C037
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij041 as C041
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij042 as C042
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij043 as C043
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij045 as C045
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij046 as C046
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij047 as C047
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij051 as C051
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij052 as C052
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij053 as C053
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij054 as C054
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij056 as C056
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij057 as C057
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij061 as C061
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij062 as C062
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij063 as C063
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij064 as C064
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij065 as C065
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij067 as C067
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij071 as C071
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij072 as C072
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij073 as C073
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij074 as C074
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij075 as C075
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij076 as C076
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij120 as C120
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij123 as C123
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij124 as C124
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij125 as C125
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij126 as C126
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij127 as C127
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij130 as C130
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij132 as C132
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij134 as C134
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij135 as C135
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij136 as C136
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij137 as C137
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij140 as C140
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij142 as C142
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij143 as C143
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij145 as C145
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij146 as C146
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij147 as C147
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij150 as C150
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij152 as C152
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij153 as C153
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij154 as C154
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij156 as C156
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij157 as C157
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij160 as C160
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij162 as C162
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij163 as C163
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij164 as C164
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij165 as C165
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij167 as C167
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij170 as C170
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij172 as C172
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij173 as C173
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij174 as C174
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij175 as C175
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij176 as C176
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij230 as C230
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij231 as C231
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij234 as C234
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij235 as C235
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij236 as C236
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij237 as C237
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij240 as C240
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij241 as C241
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij243 as C243
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij245 as C245
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij246 as C246
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij247 as C247
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij250 as C250
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij251 as C251
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij253 as C253
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij254 as C254
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij256 as C256
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij257 as C257
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij260 as C260
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij261 as C261
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij263 as C263
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij264 as C264
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij265 as C265
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij267 as C267
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij270 as C270
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij271 as C271
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij273 as C273
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij274 as C274
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij275 as C275
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij276 as C276
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij340 as C340
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij341 as C341
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij342 as C342
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij345 as C345
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij346 as C346
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij347 as C347
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij350 as C350
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij351 as C351
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij352 as C352
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij354 as C354
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij356 as C356
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij357 as C357
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij360 as C360
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij361 as C361
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij362 as C362
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij364 as C364
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij365 as C365
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij367 as C367
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij370 as C370
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij371 as C371
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij372 as C372
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij374 as C374
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij375 as C375
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij376 as C376
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij450 as C450
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij451 as C451
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij452 as C452
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij453 as C453
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij456 as C456
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij457 as C457
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij460 as C460
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij461 as C461
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij462 as C462
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij463 as C463
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij465 as C465
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij467 as C467
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij470 as C470
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij471 as C471
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij472 as C472
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij473 as C473
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij475 as C475
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij476 as C476
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij560 as C560
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij561 as C561
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij562 as C562
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij563 as C563
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij564 as C564
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij567 as C567
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij570 as C570
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij571 as C571
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij572 as C572
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij573 as C573
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij574 as C574
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij576 as C576
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij670 as C670
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij671 as C671
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij672 as C672
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij673 as C673
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij674 as C674
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij675 as C675

translate : (a b c : Fin 8) →
  .(p0 : a < b) →
  (ne0 : c Eq.≢ a) →
  (ne1 : c Eq.≢ b) →
  (dX a b) • (dM c) ≈ (dM c) • (dX a b)
translate (zero) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (zero) (suc (zero)) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (zero)) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (zero) (suc (zero)) (suc (suc (zero))) p0 ne0 ne1 = C012.proved
translate (zero) (suc (zero)) (suc (suc (suc (zero)))) p0 ne0 ne1 = C013.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C014.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C015.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C016.proved
translate (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C017.proved
translate (zero) (suc (suc (zero))) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (suc (zero))) (suc (zero)) p0 ne0 ne1 = C021.proved
translate (zero) (suc (suc (zero))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C023.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C024.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C025.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C026.proved
translate (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C027.proved
translate (zero) (suc (suc (suc (zero)))) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (suc (suc (zero)))) (suc (zero)) p0 ne0 ne1 = C031.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 ne0 ne1 = C032.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C034.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C035.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C036.proved
translate (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C037.proved
translate (zero) (suc (suc (suc (suc (zero))))) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 ne0 ne1 = C041.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 ne0 ne1 = C042.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C043.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C045.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C046.proved
translate (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C047.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 ne0 ne1 = C051.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 ne0 ne1 = C052.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C053.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C054.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C056.proved
translate (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C057.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 ne0 ne1 = C061.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 ne0 ne1 = C062.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C063.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C064.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C065.proved
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C067.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = C071.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = C072.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C073.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C074.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C075.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C076.proved
translate (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (zero)) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (zero)) (suc (suc (zero))) (zero) p0 ne0 ne1 = C120.proved
translate (suc (zero)) (suc (suc (zero))) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C123.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C124.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C125.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C126.proved
translate (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C127.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (zero) p0 ne0 ne1 = C130.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 ne0 ne1 = C132.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C134.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C135.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C136.proved
translate (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C137.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) p0 ne0 ne1 = C140.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 ne0 ne1 = C142.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C143.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C145.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C146.proved
translate (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C147.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 ne0 ne1 = C150.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 ne0 ne1 = C152.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C153.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C154.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C156.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C157.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 ne0 ne1 = C160.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 ne0 ne1 = C162.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C163.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C164.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C165.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C167.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = C170.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = C172.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C173.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C174.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C175.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C176.proved
translate (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (zero))) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (zero))) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) (suc (suc (zero))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 ne0 ne1 = C230.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 ne0 ne1 = C231.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C234.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C235.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C236.proved
translate (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C237.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 ne0 ne1 = C240.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 ne0 ne1 = C241.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C243.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C245.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C246.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C247.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 ne0 ne1 = C250.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 ne0 ne1 = C251.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C253.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C254.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C256.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C257.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 ne0 ne1 = C260.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 ne0 ne1 = C261.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C263.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C264.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C265.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C267.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = C270.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = C271.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C273.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C274.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C275.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C276.proved
translate (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (zero)))) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (zero)))) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (zero)))) (suc (suc (zero))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 ne0 ne1 = C340.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 ne0 ne1 = C341.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 ne0 ne1 = C342.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C345.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C346.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C347.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 ne0 ne1 = C350.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 ne0 ne1 = C351.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 ne0 ne1 = C352.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C354.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C356.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C357.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 ne0 ne1 = C360.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 ne0 ne1 = C361.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 ne0 ne1 = C362.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C364.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C365.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C367.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = C370.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = C371.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = C372.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C374.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C375.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C376.proved
translate (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (zero))))) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 ne0 ne1 = C450.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 ne0 ne1 = C451.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 ne0 ne1 = C452.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C453.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C456.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C457.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 ne0 ne1 = C460.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 ne0 ne1 = C461.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 ne0 ne1 = C462.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C463.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C465.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C467.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = C470.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = C471.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = C472.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C473.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C475.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C476.proved
translate (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 ne0 ne1 = C560.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 ne0 ne1 = C561.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 ne0 ne1 = C562.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C563.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C564.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = C567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = C570.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = C571.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = C572.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C573.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C574.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = C576.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 ne0 ne1 = C670.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 ne0 ne1 = C671.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 ne0 ne1 = C672.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 ne0 ne1 = C673.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 ne0 ne1 = C674.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 ne0 ne1 = C675.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 ne0 ne1 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 ne0 ne1 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c p0 ne0 ne1 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
