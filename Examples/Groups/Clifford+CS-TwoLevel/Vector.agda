------------------------------------------------------------------------
-- Presentations of groups
--
-- Vectors indexed by Fin n: lookup, extensionality, and updating one
-- or two entries.
--
-- The updates are opaque.  The generators act on vectors by updates
-- (see Action), so over 𝔻[i] a transparent update exposes the ring
-- arithmetic of a whole word, and the conversion checker unfolds the
-- action of a long word whenever two such terms are not syntactically
-- equal.  Opaque, the comparison stops at the update and goes on with
-- its arguments.  The defining equations are the lemmas set₁-a, …;
-- proofs by computation on concrete vectors (Soundness) unfold the
-- updates explicitly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Vector where

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec ; lookup ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (does)
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Lookup and extensionality

infixl 10 _!_

_!_ : {B : Set} → Vec B n → Fin n → B
_!_ = lookup

vec-ext : {B : Set} {u v : Vec B n} → (∀ x → u ! x ≡ v ! x) → u ≡ v
vec-ext {u = u} {v} eq =
  trans (sym (VecP.tabulate∘lookup u))
        (trans (VecP.tabulate-cong eq) (VecP.tabulate∘lookup v))

!-tabulate : {B : Set} (f : Fin n → B) (x : Fin n) → tabulate f ! x ≡ f x
!-tabulate f x = VecP.lookup∘tabulate f x

------------------------------------------------------------------------
-- Updating a vector at one or two indices

opaque
  set₁ : {B : Set} → Fin n → B → Vec B n → Vec B n
  set₁ a α v = tabulate (λ x → if does (x FinP.≟ a) then α else v ! x)

  set₂ : {B : Set} → Fin n → Fin n → B → B → Vec B n → Vec B n
  set₂ a b α β v =
    tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x)

  set₁-a : {B : Set} (a : Fin n) (α : B) (v : Vec B n) → set₁ a α v ! a ≡ α
  set₁-a a α v with !-tabulate (λ x → if does (x FinP.≟ a) then α else v ! x) a
  ... | eq with a FinP.≟ a
  ...   | yes _   = eq
  ...   | no  a≢a = contradiction refl a≢a

  set₁-≢ : {B : Set} (a : Fin n) (α : B) (v : Vec B n) {x : Fin n} → x ≢ a → set₁ a α v ! x ≡ v ! x
  set₁-≢ a α v {x} x≢a with !-tabulate (λ x → if does (x FinP.≟ a) then α else v ! x) x
  ... | eq with x FinP.≟ a
  ...   | yes x≡a = contradiction x≡a x≢a
  ...   | no  _   = eq

  set₂-a : {B : Set} (a b : Fin n) (α β : B) (v : Vec B n) → set₂ a b α β v ! a ≡ α
  set₂-a a b α β v
    with !-tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x) a
  ... | eq with a FinP.≟ a
  ...   | yes _   = eq
  ...   | no  a≢a = contradiction refl a≢a

  set₂-b : {B : Set} (a b : Fin n) (α β : B) (v : Vec B n) → a ≢ b → set₂ a b α β v ! b ≡ β
  set₂-b a b α β v a≢b
    with !-tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x) b
  ... | eq with b FinP.≟ a | b FinP.≟ b
  ...   | yes b≡a | _       = contradiction (sym b≡a) a≢b
  ...   | no  _   | yes _   = eq
  ...   | no  _   | no  b≢b = contradiction refl b≢b

  set₂-≢ : {B : Set} (a b : Fin n) (α β : B) (v : Vec B n) {x : Fin n} → x ≢ a → x ≢ b →
           set₂ a b α β v ! x ≡ v ! x
  set₂-≢ a b α β v {x} x≢a x≢b
    with !-tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x) x
  ... | eq with x FinP.≟ a | x FinP.≟ b
  ...   | yes x≡a | _       = contradiction x≡a x≢a
  ...   | no  _   | yes x≡b = contradiction x≡b x≢b
  ...   | no  _   | no  _   = eq
