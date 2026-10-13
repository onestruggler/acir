------------------------------------------------------------------------
-- Presentations of groups
--
-- Complete auxiliary proof certificates for the scaled encoding.
--
-- A certificate is a derivation in Tables 1 and 2 between the explicit
-- encodings of two circuits.  Thus certificates involve no oracle for
-- matrix equality.  Soundness and completeness are inherited from the
-- proved scaled two-level presentation.
--
-- This is an unbounded, nonlocal certificate calculus.  It is NOT a
-- finite local circuit presentation or a decoding of auxiliary gates.
-- The matrix denotation below is defined THROUGH the compiler; the
-- independent tensor-semantics bridge is not asserted here.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; suc ; _*_)
  renaming (_^_ to _^ℕ_)

module Examples.Groups.CCX+H.Certificates (m : ℕ) where

open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; subst)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.Syntactics
open import Examples.Groups.CCX+H.Encoding using (e)
open import Examples.Groups.CCX+H.Dimension using (half ; dimension)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Sem
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (D)

n k N : ℕ
n = suc m
k = half m
N = suc k * 2

private
  module A = PB (T._===ᴸ_ {N})
  module M = Sem.Dim (suc k)
  module C = Complete k

------------------------------------------------------------------------
-- Put the power-of-two encoding in the dimension of the scaled theorem

cast : T.Genᴸ (2 ^ℕ n) → T.Genᴸ N
cast = subst T.Genᴸ (dimension m)

code : Gen n → Word (T.Genᴸ N)
code g = wmap cast (e g)

E : Circuit n → Word (T.Genᴸ N)
E = code ʷ

-- Denotation by the explicit auxiliary encoding.
⟦_⟧ : Circuit n → Matrix N N D
⟦ w ⟧ = M.⟦ E w ⟧ᴸ

------------------------------------------------------------------------
-- The circuit relation carries a syntactic auxiliary proof

infix 4 _===_

data _===_ : WRel (Gen n) where
  certificate : ∀ {w v} → E w A.≈ E v → w === v

module P = PB _===_

-- Closing certificates under the monoid laws does not add matrix
-- equations: the encoding extends a map on generators to words.
encode-sound : ∀ {w v} → w P.≈ v → E w A.≈ E v
encode-sound P.refl = A.refl
encode-sound (P.sym h) = A.sym (encode-sound h)
encode-sound (P.trans h j) = A.trans (encode-sound h) (encode-sound j)
encode-sound (P.cong h j) = A.cong (encode-sound h) (encode-sound j)
encode-sound P.assoc = A.assoc
encode-sound P.left-unit = A.left-unit
encode-sound P.right-unit = A.right-unit
encode-sound (P.axiom (certificate h)) = h

sound : ∀ {w v} → w P.≈ v → ⟦ w ⟧ ≡ ⟦ v ⟧
sound h = Sem.soundness (suc k) (encode-sound h)

complete : ∀ {w v} → ⟦ w ⟧ ≡ ⟦ v ⟧ → w P.≈ v
complete {w} {v} h =
  P.axiom (certificate (C.completeness {u = E w} {v = E v} h))

-- When an independent circuit interpretation is supplied, one bridge
-- equality per circuit transfers both results to that interpretation.
-- No such bridge is assumed by the preceding certificate theorem.
module TensorSemantics
  (interpret : Circuit n → Matrix N N D)
  (bridge : ∀ w → ⟦ w ⟧ ≡ interpret w)
  where

  sound-tensor : ∀ {w v} → w P.≈ v → interpret w ≡ interpret v
  sound-tensor {w} {v} h =
    Eq.trans (Eq.sym (bridge w)) (Eq.trans (sound h) (bridge v))

  complete-tensor : ∀ {w v} → interpret w ≡ interpret v → w P.≈ v
  complete-tensor {w} {v} h =
    complete (Eq.trans (bridge w) (Eq.trans h (Eq.sym (bridge v))))
