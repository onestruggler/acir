{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K0 where

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding using (decode)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
module Dim = SS.Dim 4
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

private
  a : Fin 8
  a = (zero)

letter : (b c d : Fin 8) → .(p0 : a < b) → .(p1 : b < c) → .(p2 : c < d) →
  Dim.⟦ [ L.⌊ T.K-gen a b c d p0 p1 p2 ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ T.K-gen a b c d p0 p1 p2 ⌋) ⟧ᴹ
letter (zero) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p0)
letter (suc (zero)) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (zero)) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (zero)) (suc (suc (zero))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (zero)) (suc (suc (zero))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 p2 = CK0123.proved
letter (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = CK0124.proved
letter (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK0125.proved
letter (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0126.proved
letter (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0127.proved
letter (suc (zero)) (suc (suc (suc (zero)))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = CK0134.proved
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK0135.proved
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0136.proved
letter (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0137.proved
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK0145.proved
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0146.proved
letter (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0147.proved
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0156.proved
letter (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0157.proved
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0167.proved
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
letter (suc (suc (zero))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (zero))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (zero))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = CK0234.proved
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK0235.proved
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0236.proved
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0237.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK0245.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0246.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0247.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0256.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0257.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0267.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
letter (suc (suc (suc (zero)))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (suc (zero)))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (suc (zero)))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK0345.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0346.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0347.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0356.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0357.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0367.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
letter (suc (suc (suc (suc (zero))))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (suc (suc (zero))))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (suc (suc (zero))))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK0456.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0457.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0467.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK0567.proved
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p2)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
letter (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
