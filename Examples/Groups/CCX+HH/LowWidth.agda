------------------------------------------------------------------------
-- Presentations of groups
--
-- Widths zero, one, and two against the common ordinary physical
-- matrix semantics.  These are the existing empty, involution, and
-- three-coset Clément theories, with their semantic bridges proved.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.LowWidth where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Product.Base using (_,_)
open import Data.Fin.Base using (zero)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.OneQubit as O
import Examples.Groups.CCX+HH.TwoQubit.Presentation as T
import Examples.Groups.CCX+HH.TwoQubit.Semantics as TS
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH.GeneralN.GateInvolutions using (matrix-involutive)

module Zero where
  data _===_ : WRel (Gen 0) where
  private module P = PB _===_
  open P public using (_≈_)

  normalize : ∀ w → w ≈ ε
  normalize [ gate₀ () ]ʷ
  normalize ε = P.refl
  normalize (u • v) = P.trans (P.cong (normalize u) (normalize v)) P.left-unit

  semantics : ∀ (w : Circuit 0) → C.interpret w ≡ C.interpret {0} ε
  semantics [ gate₀ () ]ʷ
  semantics ε = Eq.refl
  semantics (u • v) = Eq.trans (Eq.cong₂ _·*·_ (semantics u) (semantics v)) (A.·*·-identityˡ A.𝕀)

  soundness : ∀ {u v} → u ≈ v → C.interpret u ≡ C.interpret v
  soundness {u} {v} _ = Eq.trans (semantics u) (Eq.sym (semantics v))
  completeness : ∀ {u v : Circuit 0} → C.interpret u ≡ C.interpret v → u ≈ v
  completeness {u} {v} _ = P.trans (normalize u) (P.sym (normalize v))
  grouplike : Grouplike _===_
  grouplike (gate₀ ())

module One where
  open O public using (_===_ ; _≈_ ; grouplike)
  private module P = PB _===_

  soundness : ∀ {u v} → u ≈ v → C.interpret u ≡ C.interpret v
  soundness P.refl = Eq.refl
  soundness (P.sym p) = Eq.sym (soundness p)
  soundness (P.trans p q) = Eq.trans (soundness p) (soundness q)
  soundness (P.cong p q) = Eq.cong₂ _·*·_ (soundness p) (soundness q)
  soundness (P.assoc {u} {v} {w}) = A.·*·-assoc (C.interpret u) (C.interpret v) (C.interpret w)
  soundness (P.left-unit {w}) = A.·*·-identityˡ (C.interpret w)
  soundness (P.right-unit {w}) = A.·*·-identityʳ (C.interpret w)
  soundness (P.axiom O.involution) = matrix-involutive {1} X-gen

  private
    identity≢X : C.interpret (ε {X = Gen 1}) ≢ C.interpret {1} X
    identity≢X eq with Eq.cong (λ M → A.ent M zero zero) eq
    ... | ()

    normal-injective : ∀ (a b : Bool) → C.interpret (O.normal a) ≡ C.interpret (O.normal b) → a ≡ b
    normal-injective false false eq = Eq.refl
    normal-injective false true eq with identity≢X eq
    ... | ()
    normal-injective true false eq with identity≢X (Eq.sym eq)
    ... | ()
    normal-injective true true eq = Eq.refl

  completeness : ∀ {u v : Circuit 1} → C.interpret u ≡ C.interpret v → u ≈ v
  completeness {u} {v} eq = O.completeness
    (normal-injective (O.denote u) (O.denote v)
      (Eq.trans (Eq.sym (soundness (O.normalize u)))
        (Eq.trans eq (soundness (O.normalize v)))))

module Two where
  open T public using (_===_ ; _≈_)

  opaque
    unfolding A.actV A.set₁ A.set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

    gate-semantics : ∀ g → C.gate-matrix g ≡ TS.gate-matrix g
    gate-semantics (gate₀ ())
    gate-semantics X-gen = Eq.refl
    gate-semantics CX-gen = Eq.refl
    gate-semantics HH-gen = Eq.refl
    gate-semantics ((gate₀ ()) ↥)
    gate-semantics (X-gen ↥) = Eq.refl
    gate-semantics (((gate₀ ()) ↥) ↥)

  semantics : ∀ w → C.interpret w ≡ TS.⟦ w ⟧
  semantics [ g ]ʷ = gate-semantics g
  semantics ε = Eq.refl
  semantics (u • v) = Eq.cong₂ _·*·_ (semantics u) (semantics v)

  soundness : ∀ {u v} → u ≈ v → C.interpret u ≡ C.interpret v
  soundness {u} {v} p = Eq.trans (semantics u) (Eq.trans (T.soundness p) (Eq.sym (semantics v)))

  completeness : ∀ {u v : Circuit 2} → C.interpret u ≡ C.interpret v → u ≈ v
  completeness {u} {v} eq = T.completeness
    (Eq.trans (Eq.sym (semantics u)) (Eq.trans eq (semantics v)))

  grouplike : Grouplike _===_
  grouplike g = [ g ]ʷ , completeness (matrix-involutive g)
