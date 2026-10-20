{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K1 where

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

private
  a : Fin 8
  a = (suc (zero))

letter : (b c d : Fin 8) → .(p0 : a < b) → .(p1 : b < c) → .(p2 : c < d) →
  Dim.⟦ [ L.⌊ T.K-gen a b c d p0 p1 p2 ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ T.K-gen a b c d p0 p1 p2 ⌋) ⟧ᴹ
letter (zero) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p0)
letter (suc (zero)) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
letter (suc (suc (zero))) (zero) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p1)
letter (suc (suc (zero))) (suc (zero)) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p1)
letter (suc (suc (zero))) (suc (suc (zero))) d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = CK1234.proved
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK1235.proved
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK1236.proved
letter (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1237.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK1245.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK1246.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1247.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK1256.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1257.proved
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1267.proved
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
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = CK1345.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK1346.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1347.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK1356.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1357.proved
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1367.proved
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
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK1456.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1457.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1467.proved
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
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK1567.proved
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
