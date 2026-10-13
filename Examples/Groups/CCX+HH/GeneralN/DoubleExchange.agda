------------------------------------------------------------------------
-- Presentations of groups
--
-- Physical realization of every even exchange pair.  The equality is
-- with the ordinary matrix interpretation of the two-level word and
-- includes shared endpoints and a repeated exchange.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.DoubleExchange (n : ℕ) where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Fin.Properties using (<⇒≢)
open import Data.Nat.Base using (_^_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (_•_)
import Examples.Groups.CCX+HH.GeneralN.BasisPermutations as BP
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (physical-column ; ket ; ket-cong)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits ; idx-bits)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis ; basis-col)
open import Examples.Groups.CCX+HH.GeneralN.BasisExchange using (exchange-basis)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (X)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH.Semantics as Q

module P = BP n
width = P.width

module Pair (a b c d : Fin (2 ^ width)) (ab : a < b) (cd : c < d) where
  witness = P.pair a b c d (<⇒≢ ab) (<⇒≢ cd)
  circuit = C.physical (P.word witness)
  auxiliary = X a b ab • X c d cd

  column : ∀ i → A.col (Q.interpret circuit) i ≡
    basis (P.swap a b (P.swap c d i))
  column i = trans (physical-column (P.word witness) i)
    (trans (ket-cong width (P.correct witness i))
      (cong basis (idx-bits width (P.swap a b (P.swap c d i)))))

  auxiliary-column : ∀ i → A.col A.⟦ auxiliary ⟧ᵐ i ≡
    basis (P.swap a b (P.swap c d i))
  auxiliary-column i = trans (A.col-actMʷ auxiliary A.𝕀 i)
    (trans (cong (A.actVʷ auxiliary) (sym (basis-col i)))
      (trans (cong (A.actVʷ (X a b ab)) (exchange-basis cd i))
        (exchange-basis ab (P.swap c d i))))

  correct : Q.interpret circuit ≡ A.⟦ auxiliary ⟧ᵐ
  correct = A.col-ext λ i → trans (column i) (sym (auxiliary-column i))
