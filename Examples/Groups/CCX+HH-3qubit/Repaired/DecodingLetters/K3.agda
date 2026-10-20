{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K3 where

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
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3456 as CK3456
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3457 as CK3457
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3467 as CK3467
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K3567 as CK3567

private
  a : Fin 8
  a = (suc (suc (suc (zero))))

letter : (b c d : Fin 8) → .(p0 : a < b) → .(p1 : b < c) → .(p2 : c < d) →
  Dim.⟦ [ L.⌊ T.K-gen a b c d p0 p1 p2 ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ T.K-gen a b c d p0 p1 p2 ⌋) ⟧ᴹ
letter (zero) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p0)
letter (suc (zero)) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p0)
letter (suc (suc (zero))) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
letter (suc (suc (suc (zero)))) c d p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
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
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = CK3456.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK3457.proved
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ z≤n p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s z≤n) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s z≤n)) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 p2 = ⊥-elim (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p2)
letter (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK3467.proved
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
letter (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 p2 = CK3567.proved
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
