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
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
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
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K0 as K0
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K1 as K1
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K2 as K2
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K3 as K3
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K4 as K4
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K5 as K5
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K6 as K6
import Examples.Groups.CCX+HH-3qubit.Repaired.DecodingLetters.K7 as K7

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
dyadic-letter (T.K-gen (zero) b c d p0 p1 p2) = K0.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (zero)) b c d p0 p1 p2) = K1.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (suc (zero))) b c d p0 p1 p2) = K2.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (suc (suc (zero)))) b c d p0 p1 p2) = K3.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (suc (suc (suc (zero))))) b c d p0 p1 p2) = K4.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2) = K5.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2) = K6.letter b c d p0 p1 p2
dyadic-letter (T.K-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2) = K7.letter b c d p0 p1 p2

letter-matrix : ∀ g → Dim.⟦ [ g ]ʷ ⟧ᴸ ≡ ⟦ decode g ⟧ᴹ
letter-matrix (L.⌊ g ⌋) = dyadic-letter g
letter-matrix L.IH = EM.gen-matrix H2-gen

-- Decoding every word preserves its matrix, including I ⊗ H.
decode-matrix : ∀ w → Dim.⟦ w ⟧ᴸ ≡ ⟦ (decode ʷ) w ⟧ᴹ
decode-matrix [ g ]ʷ = letter-matrix g
decode-matrix ε = Eq.sym matrix-ε
decode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ w v)
  (Eq.trans (Eq.cong₂ (_·*·_ {{R.RingD}})
    (decode-matrix w) (decode-matrix v))
    (Eq.sym (matrix-• ((decode ʷ) w) ((decode ʷ) v))))
