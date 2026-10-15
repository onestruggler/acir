------------------------------------------------------------------------
-- Presentations of groups
--
-- The two low-width abelian characters are ordinary gate counts:
-- X and H on one wire, CX and H on two, CCX and H on three.
-- The counts are modulo two; equality is in the universal commutative
-- quotient, not an assertion of physical matrix equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.LowWidthCharacters where

open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.Encoding as E
import Examples.Groups.CCX+H.Abelianization as Abel
import Examples.Groups.CCX+H.LowWidthAbelianization as Low
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity

X-kind CX-kind CCX-kind : View → Bool
X-kind (at-X _) = true
X-kind (at-H _) = false
X-kind (at-CX _) = false
X-kind (at-CCX _) = false
CX-kind (at-X _) = false
CX-kind (at-H _) = false
CX-kind (at-CX _) = true
CX-kind (at-CCX _) = false
CCX-kind (at-X _) = false
CCX-kind (at-H _) = false
CCX-kind (at-CX _) = false
CCX-kind (at-CCX _) = true

count : (View → Bool) → ∀ {n} → Circuit n → Bool
count kind [ g ]ʷ = kind (view g)
count kind ε = false
count kind (u • v) = count kind u xor count kind v

counts : (View → Bool) → ∀ {n} → Circuit n → Bool × Bool
counts kind w = count kind w , Parity.parity w

private
  _⊕_ : Bool × Bool → Bool × Bool → Bool × Bool
  (a , b) ⊕ (c , d) = (a xor c) , (b xor d)

  module Transfer (n : ℕ) (kind : View → Bool) (character : Circuit n → Bool × Bool)
    (letter : ∀ g → character [ g ]ʷ ≡ counts kind [ g ]ʷ)
    (empty : character ε ≡ (false , false))
    (product : ∀ u v → character (u • v) ≡ (character u ⊕ character v))
    where

    correct : ∀ w → character w ≡ counts kind w
    correct [ g ]ʷ = letter g
    correct ε = empty
    correct (u • v) = Eq.trans (product u v) (Eq.cong₂ _⊕_ (correct u) (correct v))

module One where
  private
    letter : ∀ g → Low.One.character [ g ]ʷ ≡ counts X-kind [ g ]ʷ
    letter (gate₀ ())
    letter (gate₁ X-gate) = Eq.refl
    letter (gate₁ H-gate) = Eq.refl
    letter ((gate₀ ()) ↥)
    module F = Transfer 1 X-kind Low.One.character letter Eq.refl
      (λ u v → Low.One.B.character-product (E.encode u) (E.encode v))

  open F public using (correct)

  sound : ∀ {u v} → Abel.At._≈_ 1 u v → counts X-kind u ≡ counts X-kind v
  sound {u} {v} eq = Eq.trans (Eq.sym (correct u)) (Eq.trans (Low.One.sound eq) (correct v))

  complete : ∀ {u v} → counts X-kind u ≡ counts X-kind v → Abel.At._≈_ 1 u v
  complete {u} {v} eq = Low.One.complete (Eq.trans (correct u) (Eq.trans eq (Eq.sym (correct v))))

module Two where
  private
    letter : ∀ g → Low.Two.character [ g ]ʷ ≡ counts CX-kind [ g ]ʷ
    letter (gate₀ ())
    letter (gate₁ X-gate) = Eq.refl
    letter (gate₁ H-gate) = Eq.refl
    letter (gate₂ CX-gate) = Eq.refl
    letter ((gate₀ ()) ↥)
    letter (gate₁ X-gate ↥) = Eq.refl
    letter (gate₁ H-gate ↥) = Eq.refl
    letter (((gate₀ ()) ↥) ↥)
    module F = Transfer 2 CX-kind Low.Two.character letter Eq.refl
      (λ u v → Low.Two.B.character-product (E.encode u) (E.encode v))

  open F public using (correct)

  sound : ∀ {u v} → Abel.At._≈_ 2 u v → counts CX-kind u ≡ counts CX-kind v
  sound {u} {v} eq = Eq.trans (Eq.sym (correct u)) (Eq.trans (Low.Two.sound eq) (correct v))

  complete : ∀ {u v} → counts CX-kind u ≡ counts CX-kind v → Abel.At._≈_ 2 u v
  complete {u} {v} eq = Low.Two.complete (Eq.trans (correct u) (Eq.trans eq (Eq.sym (correct v))))

module Three where
  private
    letter : ∀ g → Low.Three.character [ g ]ʷ ≡ counts CCX-kind [ g ]ʷ
    letter (gate₀ ())
    letter (gate₁ X-gate) = Eq.refl
    letter (gate₁ H-gate) = Eq.refl
    letter (gate₂ CX-gate) = Eq.refl
    letter (gate₃ CCX-gate) = Eq.refl
    letter ((gate₀ ()) ↥)
    letter (gate₁ X-gate ↥) = Eq.refl
    letter (gate₁ H-gate ↥) = Eq.refl
    letter (gate₂ CX-gate ↥) = Eq.refl
    letter (((gate₀ ()) ↥) ↥)
    letter ((gate₁ X-gate ↥) ↥) = Eq.refl
    letter ((gate₁ H-gate ↥) ↥) = Eq.refl
    letter ((((gate₀ ()) ↥) ↥) ↥)
    module F = Transfer 3 CCX-kind Low.Three.character letter Eq.refl
      (λ u v → Low.Three.B.character-product (E.encode u) (E.encode v))

  open F public using (correct)

  sound : ∀ {u v} → Abel.At._≈_ 3 u v → counts CCX-kind u ≡ counts CCX-kind v
  sound {u} {v} eq = Eq.trans (Eq.sym (correct u)) (Eq.trans (Low.Three.sound eq) (correct v))

  complete : ∀ {u v} → counts CCX-kind u ≡ counts CCX-kind v → Abel.At._≈_ 3 u v
  complete {u} {v} eq = Low.Three.complete (Eq.trans (correct u) (Eq.trans eq (Eq.sym (correct v))))
