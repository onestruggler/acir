------------------------------------------------------------------------
-- Presentations of groups
--
-- The universal commutative quotient of the physical H circuit group.
-- Added commutations describe this quotient; they are not extra
-- physical circuit identities.  Hadamard parity descends to it.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Abelianization where

open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (Bool ; _xor_)
import Data.Bool.Properties as BP
open import Data.Product.Base using (_,_ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.GroupLike as GL
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.Orthogonal as O
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity

data Relations (n : ℕ) : WRel (Gen n) where
  source : ∀ {u v} → P.Relations n u v → Relations n u v
  commute : ∀ u v → Relations n (u • v) (v • u)

module At (n : ℕ) where
  open PB (Relations n) public hiding (_===_)

  source-cong : ∀ {u v : Circuit n} → n P.⊢ u ≈ v → u ≈ v
  source-cong PB.refl = refl
  source-cong (PB.sym p) = sym (source-cong p)
  source-cong (PB.trans p q) = trans (source-cong p) (source-cong q)
  source-cong (PB.cong p q) = cong (source-cong p) (source-cong q)
  source-cong PB.assoc = assoc
  source-cong PB.left-unit = left-unit
  source-cong PB.right-unit = right-unit
  source-cong (PB.axiom p) = axiom (source p)

  grouplike : GL.Grouplike (Relations n)
  grouplike g = [ g ]ʷ , source-cong (proj₂ (O.grouplike n g))

  sound : ∀ {u v} → u ≈ v → Parity.parity u ≡ Parity.parity v
  sound refl = Eq.refl
  sound (sym eq) = Eq.sym (sound eq)
  sound (trans eq eq′) = Eq.trans (sound eq) (sound eq′)
  sound (cong eq eq′) = Eq.cong₂ _xor_ (sound eq) (sound eq′)
  sound (assoc {x} {y} {z}) = BP.xor-assoc (Parity.parity x) (Parity.parity y) (Parity.parity z)
  sound left-unit = Eq.refl
  sound (right-unit {x}) = BP.xor-identityʳ (Parity.parity x)
  sound (axiom (source {u} {v} ax)) = Parity.physical-sound {u = u} {v = v}
    (P.sound n (PB.axiom ax))
  sound (axiom (commute u v)) = BP.xor-comm (Parity.parity u) (Parity.parity v)

  module Universal {Y : Set} (Δ : WRel Y) (f : Gen n → Word Y)
    (source-respects : ∀ {u v} → P.Relations n u v →
      PB._≈_ Δ ((f ʷ) u) ((f ʷ) v))
    (commutative : ∀ u v → PB._≈_ Δ (u • v) (v • u)) where

    private
      respects : ∀ {u v} → Relations n u v →
        PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
      respects (source p) = source-respects p
      respects (commute u v) = commutative ((f ʷ) u) ((f ʷ) v)

    factor : ∀ {u v} → u ≈ v → PB._≈_ Δ ((f ʷ) u) ((f ʷ) v)
    factor = PP.StarCongruence.fʷ-cong (Relations n) Δ f respects

  private module G = GL.Group-Lemmas (Relations n) grouplike

  commutator : Circuit n → Circuit n → Circuit n
  commutator u v = (u • v) • G._⁻¹ u • G._⁻¹ v

  Derived : Circuit n → Set
  Derived w = w ≈ ε

  commutator-member : ∀ u v → Derived (commutator u v)
  commutator-member u v = trans assoc
    (trans (cong refl (sym assoc))
      (trans (cong refl (cong (axiom (commute v (G._⁻¹ u))) refl))
        (trans (cong refl assoc)
          (trans (sym assoc)
            (trans (cong (G.inverseʳ {g = u}) (G.inverseʳ {g = v})) left-unit)))))
