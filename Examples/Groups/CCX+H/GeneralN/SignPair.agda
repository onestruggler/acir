------------------------------------------------------------------------
-- Presentations of groups
--
-- Every pair of level signs is a physical CCX+HH circuit at width >=4.
-- An affine router transports the independently checked local pair.
-- Coincident levels cancel and compile to the empty circuit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+H.GeneralN.SignPair (n : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_ ; <⇒≢)
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (ε ; _•_)
import Presentation.Base as PB
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (M ; r1b)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.GeneralN.PairRouting as Routing
import Examples.Groups.CCX+HH.GeneralN.SignPairBase as Base
import Examples.Groups.CCX+H.GeneralN.PhysicalConjugation as Conjugate
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits ; idx-cong ; idx-bits)

width : ℕ
width = 4 + n
Level = Fin (2 ^ width)
private module B = Base n

record Realisation (a b : Level) : Set where
  field
    word : H.Circuit width
    correct : Q.interpret word ≡ A.⟦ M a • M b ⟧ᵐ

private
  different : ∀ {a b : Level} → a ≢ b → ¬ (bits width a C.≈s bits width b)
  different {a} {b} ne eq = ne (trans (sym (idx-bits width a))
    (trans (idx-cong width eq) (idx-bits width b)))

module Distinct (a b : Level) (ab : a ≢ b) where
  private
    witness = Routing.route (bits width B.a) (bits width B.b)
      (bits width a) (bits width b) (different (<⇒≢ B.ordered)) (different ab)
    module W = Conjugate (Routing.Route.word witness)
    first : W.forward B.a ≡ a
    first = trans (idx-cong width (Routing.Route.first witness)) (idx-bits width a)
    second : W.forward B.b ≡ b
    second = trans (idx-cong width (Routing.Route.second witness)) (idx-bits width b)

  circuit : H.Circuit width
  circuit = W.route B.circuit

  correct : Q.interpret circuit ≡ A.⟦ M a • M b ⟧ᵐ
  correct = trans (W.sign-pair B.circuit B.a B.b B.correct)
    (cong₂ (λ x y → A.⟦ M x • M y ⟧ᵐ) first second)

realise : ∀ a b → Realisation a b
realise a b = choose (a ≟ b)
  where
  choose : Dec (a ≡ b) → Realisation a b
  choose (yes refl) = record
    { word = ε
    ; correct = sym (Red.sound-act (PB.axiom r1b) A.𝕀)
    }
  choose (no ab) = record { word = Distinct.circuit a b ab ; correct = Distinct.correct a b ab }

circuit : ∀ a b → H.Circuit width
circuit a b = Realisation.word (realise a b)

correct : ∀ a b → Q.interpret (circuit a b) ≡ A.⟦ M a • M b ⟧ᵐ
correct a b = Realisation.correct (realise a b)
