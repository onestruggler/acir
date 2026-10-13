{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.DecodingMatrices where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ ; matrix-• ; matrix-ε)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding using (decode)
import Examples.Groups.CCX+HH-3qubit.Repaired.EncodingMatrices as EM
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
module Dim = SS.Dim 4
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M0 as CM0
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M1 as CM1
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M2 as CM2
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M3 as CM3
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M4 as CM4
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M5 as CM5
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M6 as CM6
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M7 as CM7
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X01 as CX01
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X02 as CX02
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X03 as CX03
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X04 as CX04
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X05 as CX05
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X06 as CX06
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X07 as CX07
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X12 as CX12
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X13 as CX13
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X14 as CX14
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X15 as CX15
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X16 as CX16
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X17 as CX17
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X23 as CX23
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X24 as CX24
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X25 as CX25
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X26 as CX26
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X27 as CX27
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X34 as CX34
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X35 as CX35
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X36 as CX36
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X37 as CX37
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X45 as CX45
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X46 as CX46
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X47 as CX47
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X56 as CX56
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X57 as CX57
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X67 as CX67
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0123 as CK0123
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0124 as CK0124
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0125 as CK0125
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0126 as CK0126
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0127 as CK0127
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0134 as CK0134
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0135 as CK0135
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0136 as CK0136
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0137 as CK0137
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0145 as CK0145
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0146 as CK0146
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0147 as CK0147
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0156 as CK0156
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0157 as CK0157
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0167 as CK0167
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0234 as CK0234
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0235 as CK0235
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0236 as CK0236
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0237 as CK0237
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0245 as CK0245
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0246 as CK0246
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0247 as CK0247
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0256 as CK0256
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0257 as CK0257
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0267 as CK0267
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0345 as CK0345
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0346 as CK0346
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0347 as CK0347
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0356 as CK0356
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0357 as CK0357
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0367 as CK0367
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0456 as CK0456
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0457 as CK0457
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0467 as CK0467
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0567 as CK0567
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1234 as CK1234
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1235 as CK1235
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1236 as CK1236
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1237 as CK1237
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1245 as CK1245
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1246 as CK1246
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1247 as CK1247
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1256 as CK1256
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1257 as CK1257
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1267 as CK1267
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1345 as CK1345
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1346 as CK1346
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1347 as CK1347
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1356 as CK1356
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1357 as CK1357
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1367 as CK1367
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1456 as CK1456
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1457 as CK1457
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1467 as CK1467
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K1567 as CK1567
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2345 as CK2345
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2346 as CK2346
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2347 as CK2347
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2356 as CK2356
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2357 as CK2357
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2367 as CK2367
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2456 as CK2456
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2457 as CK2457
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2467 as CK2467
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K2567 as CK2567
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3456 as CK3456
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3457 as CK3457
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3467 as CK3467
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3567 as CK3567
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K4567 as CK4567

dyadic-letter : ∀ g → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ g ⌋) ⟧ᴹ
dyadic-letter (T.M-gen (zero)) = CM0.proved
dyadic-letter (T.M-gen (suc (zero))) = CM1.proved
dyadic-letter (T.M-gen (suc (suc (zero)))) = CM2.proved
dyadic-letter (T.M-gen (suc (suc (suc (zero))))) = CM3.proved
dyadic-letter (T.M-gen (suc (suc (suc (suc (zero)))))) = CM4.proved
dyadic-letter (T.M-gen (suc (suc (suc (suc (suc (zero))))))) = CM5.proved
dyadic-letter (T.M-gen (suc (suc (suc (suc (suc (suc (zero)))))))) = CM6.proved
dyadic-letter (T.M-gen (suc (suc (suc (suc (suc (suc (suc (zero))))))))) = CM7.proved
dyadic-letter (T.X-gen (zero) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (zero) (suc (zero)) p0) = CX01.proved
dyadic-letter (T.X-gen (zero) (suc (suc (zero))) p0) = CX02.proved
dyadic-letter (T.X-gen (zero) (suc (suc (suc (zero)))) p0) = CX03.proved
dyadic-letter (T.X-gen (zero) (suc (suc (suc (suc (zero))))) p0) = CX04.proved
dyadic-letter (T.X-gen (zero) (suc (suc (suc (suc (suc (zero)))))) p0) = CX05.proved
dyadic-letter (T.X-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = CX06.proved
dyadic-letter (T.X-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX07.proved
dyadic-letter (T.X-gen (suc (zero)) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (zero)) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (zero)) (suc (suc (zero))) p0) = CX12.proved
dyadic-letter (T.X-gen (suc (zero)) (suc (suc (suc (zero)))) p0) = CX13.proved
dyadic-letter (T.X-gen (suc (zero)) (suc (suc (suc (suc (zero))))) p0) = CX14.proved
dyadic-letter (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0) = CX15.proved
dyadic-letter (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = CX16.proved
dyadic-letter (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX17.proved
dyadic-letter (T.X-gen (suc (suc (zero))) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (suc (zero))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (suc (suc (zero)))) p0) = CX23.proved
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0) = CX24.proved
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0) = CX25.proved
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = CX26.proved
dyadic-letter (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX27.proved
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (suc (zero))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0) = CX34.proved
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0) = CX35.proved
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = CX36.proved
dyadic-letter (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX37.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0) = CX45.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = CX46.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX47.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = CX56.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX57.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = CX67.proved
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
dyadic-letter (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)
dyadic-letter (T.K-gen (zero) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (zero) (suc (zero)) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 p2) = CK0123.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = CK0124.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK0125.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0126.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0127.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = CK0134.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK0135.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0136.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0137.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK0145.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0146.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0147.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0156.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0157.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0167.proved
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = CK0234.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK0235.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0236.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0237.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK0245.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0246.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0247.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0256.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0257.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0267.proved
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK0345.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0346.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0347.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0356.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0357.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0367.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK0456.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0457.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0467.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK0567.proved
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (zero)) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (zero)) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = CK1234.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK1235.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK1236.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1237.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK1245.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK1246.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1247.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK1256.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1257.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1267.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK1345.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK1346.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1347.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK1356.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1357.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1367.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK1456.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1457.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1467.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK1567.proved
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (zero))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = CK2345.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK2346.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK2347.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK2356.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK2357.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK2367.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK2456.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK2457.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK2467.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK2567.proved
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (zero))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = CK3456.proved
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK3457.proved
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK3467.proved
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK3567.proved
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (zero))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = CK4567.proved
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ z≤n p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p0)
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) c d p0 p1 p2) = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p0)

letter-matrix : ∀ g → Dim.⟦ [ g ]ʷ ⟧ᴸ ≡ ⟦ decode g ⟧ᴹ
letter-matrix (L.⌊ g ⌋) = dyadic-letter g
letter-matrix L.IH = EM.gen-matrix H2-gen

-- Decoding every word preserves its matrix, including I ⊗ H.
decode-matrix : ∀ w → Dim.⟦ w ⟧ᴸ ≡ ⟦ (decode ʷ) w ⟧ᴹ
decode-matrix [ g ]ʷ = letter-matrix g
decode-matrix ε = Eq.sym matrix-ε
decode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ w v)
  (Eq.trans (Eq.cong₂ _·*·_ (decode-matrix w) (decode-matrix v))
    (Eq.sym (matrix-• ((decode ʷ) w) ((decode ʷ) v))))
