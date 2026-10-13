------------------------------------------------------------------------
-- Presentations of groups
--
-- The index-four auxiliary subgroup of the scaled dyadic group.
--
-- This is the stabilizer of 00 in the four-state action.  Its complete
-- relations are the stateful translations of Tables 1 and 2, together
-- with Schreier-generator recovery equations.  The theorem identifies
-- the auxiliary subgroup exactly; circuit decoding is a separate step.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; suc ; _*_ ; z≤n ; s≤s)

module Examples.Groups.CCX+H.GeneralN.Presentation (k : ℕ) where

open import Data.Fin.Base using (zero ; suc)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Derived as UD
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Sem
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
import Examples.Groups.CCX+HH.Subgroup.Schreier as Schreier
open import Examples.Groups.CCX+H.GeneralN.Action

N : ℕ
N = suc k * 2

open At N public using (state ; state-relations ; state-cong)

source-grouplike : Grouplike (T._===ᴸ_ {N})
source-grouplike T.⌊ g ⌋ = [ T.⌊ g ⌋ ]ʷ , T.⌊⌋-cong (UD.gen-gen g)
source-grouplike T.IH = T.H , PB.axiom T.r7a

rep : Coset → Word (T.Genᴸ N)
rep c00 = ε
rep c10 = T.Mᴸ zero
rep c11 = T.Xᴸ zero (suc zero) (s≤s z≤n)
rep c01 = T.Mᴸ zero • T.Xᴸ zero (suc zero) (s≤s z≤n)

rep-state : ∀ c → state c00 (rep c) ≡ c
rep-state c00 = Eq.refl
rep-state c10 = Eq.refl
rep-state c11 = Eq.refl
rep-state c01 = Eq.refl

module Theory = Schreier (T._===ᴸ_ {N}) source-grouplike c00
  step state-relations rep PB.refl rep-state

open Theory public using
  (Edge ; e ; encode ; decode ; _===_ ; _≈_ ; roundtrip ; translated
  ; encode-injective ; encode-cong ; encode-closed ; edge-closed
  ; factor-word ; decode-loop ; grouplike)

private
  module M = Sem.Dim (suc k)
  module C = Complete k

completeness : ∀ {u v : Word Edge} →
  M.⟦ encode u ⟧ᴸ ≡ M.⟦ encode v ⟧ᴸ → u ≈ v
completeness {u} {v} eq = encode-injective
  (C.completeness {u = encode u} {v = encode v} eq)

soundness : ∀ {u v : Word Edge} → u ≈ v →
  M.⟦ encode u ⟧ᴸ ≡ M.⟦ encode v ⟧ᴸ
soundness eq = Sem.soundness (suc k) (encode-cong eq)

-- The state is determined by the matrix, independently of its word.
state-semantic : ∀ c {u v : Word (T.Genᴸ N)} →
  M.⟦ u ⟧ᴸ ≡ M.⟦ v ⟧ᴸ → state c u ≡ state c v
state-semantic c {u} {v} eq = state-cong c
  (C.completeness {u = u} {v = v} eq)

-- Conversely every word in the stabilizer is reconstructed by decoding.
stabilizer-generated : ∀ w → state c00 w ≡ c00 →
  M.⟦ encode (decode c00 w) ⟧ᴸ ≡ M.⟦ w ⟧ᴸ
stabilizer-generated w closed = Sem.soundness (suc k)
  (decode-loop {w} closed)
