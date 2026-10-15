------------------------------------------------------------------------
-- Presentations of groups
--
-- The low-width physical HH abelianizations: trivial on zero wires,
-- C2 on one wire, C2 x C2 on two wires, and C2 on three wires.
-- Short commutator witnesses give the upper bounds.  The independently
-- proved dyadic charge distinguishes every remaining representative.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.LowWidthAbelianization where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Abelianization as Abel
import Examples.Groups.CCX+HH.LowWidth as Low
import Examples.Groups.CCX+HH.OneQubit as Q1
import Examples.Groups.CCX+HH.LowWidth.AbelianTools as Tools
import Examples.Groups.CCX+HH.LowWidth.CommutatorChecks as Checks
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00 ; c10 ; c11 ; c01)
open Tools public using (C₂ ; C₂×C₂ ; _⊕_ ; abelian-group)

private
  first-charge : Coset → Bool
  first-charge c00 = false
  first-charge c10 = true
  first-charge c11 = true
  first-charge c01 = false

module Zero where
  trivial : ∀ (w : Circuit 0) → Abel.At._≈_ 0 w ε
  trivial w = Abel.At.source-cong 0 (Low.Zero.normalize w)

module One where
  open Tools.At 1

  character = Q1.denote
  rep = Q1.normal

  normalize : ∀ w → w ≈ rep (character w)
  normalize w = source-cong (Q1.normalize w)

  private
    read-rep : ∀ c → first-charge (charge (rep c)) ≡ c
    read-rep false = Eq.refl
    read-rep true = Eq.refl
    module NF = NormalForm Bool character rep normalize first-charge read-rep

  open NF public using (sound ; complete)

  representatives : ∀ c → character (rep c) ≡ c
  representatives false = Eq.refl
  representatives true = Eq.refl

  isomorphism : GroupMorphisms.IsGroupIsomorphism
    (Group.rawGroup (abelian-group 1)) (Group.rawGroup C₂) character
  isomorphism = Tools.Bundle.build 1 C₂ character sound complete
    (λ u v → Eq.refl) Eq.refl rep representatives

module Two where
  open Tools.At 2

  Character = Bool × Bool

  letter : Gen 2 → Character
  letter (gate₀ ())
  letter X-gen = false , false
  letter CX-gen = true , false
  letter HH-gen = false , true
  letter ((gate₀ ()) ↥)
  letter (X-gen ↥) = false , false
  letter (((gate₀ ()) ↥) ↥)

  character : Circuit 2 → Character
  character [ g ]ʷ = letter g
  character ε = false , false
  character (u • v) = character u ⊕ character v

  rep : Character → Circuit 2
  rep = pair-power CX HH

  private
    cx-square : (CX • CX) ≈ ε
    cx-square = source-cong (proj₂ (P.grouplike 2 CX-gen))

    hh-square : (HH • HH) ≈ ε
    hh-square = source-cong (proj₂ (P.grouplike 2 HH-gen))

    generator : ∀ g → [ g ]ʷ ≈ rep (letter g)
    generator (gate₀ ())
    generator X-gen = trans (Checks.Two.removed Checks.Two.x₀) (sym left-unit)
    generator CX-gen = sym right-unit
    generator HH-gen = sym left-unit
    generator ((gate₀ ()) ↥)
    generator (X-gen ↥) = trans (Checks.Two.removed Checks.Two.x₁) (sym left-unit)
    generator (((gate₀ ()) ↥) ↥)

    rep-product : ∀ c d → (rep c • rep d) ≈ rep (c ⊕ d)
    rep-product (a , b) (c , d) = pair-product CX HH cx-square hh-square a b c d

  normalize : ∀ w → w ≈ rep (character w)
  normalize [ g ]ʷ = generator g
  normalize ε = sym left-unit
  normalize (u • v) = trans (cong (normalize u) (normalize v))
    (rep-product (character u) (character v))

  private
    read : Coset → Character
    read c00 = false , false
    read c11 = true , false
    read c01 = false , true
    read c10 = true , true

    read-rep : ∀ c → read (charge (rep c)) ≡ c
    read-rep (false , false) = Eq.refl
    read-rep (false , true) = Eq.refl
    read-rep (true , false) = Eq.refl
    read-rep (true , true) = Eq.refl

    module NF = NormalForm Character character rep normalize read read-rep

  open NF public using (sound ; complete)

  representatives : ∀ c → character (rep c) ≡ c
  representatives (false , false) = Eq.refl
  representatives (false , true) = Eq.refl
  representatives (true , false) = Eq.refl
  representatives (true , true) = Eq.refl

  isomorphism : GroupMorphisms.IsGroupIsomorphism
    (Group.rawGroup (abelian-group 2)) (Group.rawGroup C₂×C₂) character
  isomorphism = Tools.Bundle.build 2 C₂×C₂ character sound complete
    (λ u v → Eq.refl) Eq.refl rep representatives

module Three where
  open Tools.At 3

  letter : Gen 3 → Bool
  letter (gate₀ ())
  letter X-gen = false
  letter CX-gen = false
  letter CCX-gen = true
  letter HH-gen = false
  letter ((gate₀ ()) ↥)
  letter (X-gen ↥) = false
  letter (CX-gen ↥) = false
  letter (HH-gen ↥) = false
  letter (((gate₀ ()) ↥) ↥)
  letter ((X-gen ↥) ↥) = false
  letter ((((gate₀ ()) ↥) ↥) ↥)

  character : Circuit 3 → Bool
  character [ g ]ʷ = letter g
  character ε = false
  character (u • v) = character u xor character v

  rep : Bool → Circuit 3
  rep b = power b CCX

  private
    square : (CCX • CCX) ≈ ε
    square = source-cong (proj₂ (P.grouplike 3 CCX-gen))

    generator : ∀ g → [ g ]ʷ ≈ rep (letter g)
    generator (gate₀ ())
    generator X-gen = Checks.Three.removed Checks.Three.x₀
    generator CX-gen = Checks.Three.removed Checks.Three.cx₀
    generator CCX-gen = refl
    generator HH-gen = Checks.Three.removed Checks.Three.hh₀
    generator ((gate₀ ()) ↥)
    generator (X-gen ↥) = Checks.Three.removed Checks.Three.x₁
    generator (CX-gen ↥) = Checks.Three.removed Checks.Three.cx₁
    generator (HH-gen ↥) = Checks.Three.removed Checks.Three.hh₁
    generator (((gate₀ ()) ↥) ↥)
    generator ((X-gen ↥) ↥) = Checks.Three.removed Checks.Three.x₂
    generator ((((gate₀ ()) ↥) ↥) ↥)

  normalize : ∀ w → w ≈ rep (character w)
  normalize [ g ]ʷ = generator g
  normalize ε = refl
  normalize (u • v) = trans (cong (normalize u) (normalize v))
    (power-product CCX square (character u) (character v))

  private
    read-rep : ∀ c → first-charge (charge (rep c)) ≡ c
    read-rep false = Eq.refl
    read-rep true = Eq.refl
    module NF = NormalForm Bool character rep normalize first-charge read-rep

  open NF public using (sound ; complete)

  representatives : ∀ c → character (rep c) ≡ c
  representatives false = Eq.refl
  representatives true = Eq.refl

  isomorphism : GroupMorphisms.IsGroupIsomorphism
    (Group.rawGroup (abelian-group 3)) (Group.rawGroup C₂) character
  isomorphism = Tools.Bundle.build 3 C₂ character sound complete
    (λ u v → Eq.refl) Eq.refl rep representatives
