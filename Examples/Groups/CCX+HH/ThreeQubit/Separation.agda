------------------------------------------------------------------------
-- Presentations of groups
--
-- The 135 representatives are distinct modulo signed permutations.
-- This is the uniqueness input of the finite Clément translation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Separation where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH.ThreeQubit.Cosets
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (Letter ; b ; b-signed)
open import Examples.Groups.CCX+HH.ThreeQubit.Signature using (signature-injective)
import Examples.Groups.CCX+HH.ThreeQubit.QuarticInvariant as Q

separate-signed : ∀ c c′ {u v} → Q.Signed u → Q.Signed v →
  PB._≈_ (T._===_ {8}) (u • E.encode (rep c)) (v • E.encode (rep c′)) → c ≡ c′
separate-signed c c′ u-signed v-signed eq = signature-injective
  (Eq.trans (Eq.sym (Q.prefix-invariant u-signed (E.encode (rep c))))
    (Eq.trans (Q.signature-cong eq) (Q.prefix-invariant v-signed (E.encode (rep c′)))))

base-signed : ∀ w → Q.Signed ((b ʷ) w)
base-signed [ g ]ʷ = b-signed g
base-signed ε = Q.empty
base-signed (u • v) = Q.product (base-signed u) (base-signed v)

separate : ∀ c c′ (u v : Word Letter) →
  PB._≈_ (T._===_ {8})
    ((b ʷ) u • E.encode (rep c)) ((b ʷ) v • E.encode (rep c′)) → c ≡ c′
separate c c′ u v = separate-signed c c′ (base-signed u) (base-signed v)
