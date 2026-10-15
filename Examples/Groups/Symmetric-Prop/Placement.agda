------------------------------------------------------------------------
-- Presentations of groups
--
-- Placing a circuit by a swap network, in any PROP.
--
-- A word on the bottom k wires commutes with every word shifted up k
-- wires (`apart`), by the structural rules gate by gate.  A placement
-- of a circuit is its conjugate by a network (`place N w`: the network,
-- the circuit, the network reversed, every swap being an involution),
-- and the placement of a word on the bottom k wires does not see a
-- change of the network on the wires above them (`frame`): composing
-- the network with any network k wires up leaves the placement as it
-- was.  With Networks.perm-≈ that says a placement depends only on
-- where the network sends the bottom k wires.
--
-- Scalars are central once they commute with one another, which is the
-- one hypothesis (Circuit.Base.Central-Scalars); a family with no
-- 0-ary gate discharges it by `()`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)
import Circuit.Base

module Examples.Groups.Symmetric-Prop.Placement
  (Gate : ℕ → Set) (Ex-gate : Gate 2)
  (_SRel,_===_ : (n : ℕ) → Circuit.Base.CRel Gate n)
  where

open import Data.Nat.Base using (zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
import Presentation.Base as PB

open import Circuit.Prop Gate Ex-gate
open Lift-To-Prop _SRel,_===_

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Symmetric-Prop.Networks Gate Ex-gate _SRel,_===_
  using (φ ; net ; net-↑)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- Shifting by k wires

↑ᵏ-suc : (v : Circuit n) (j : ℕ) → v ↑ᵏ suc j ≡ (v ↑ᵏ j) ↑
↑ᵏ-suc [ g ]ʷ  j = Eq.refl
↑ᵏ-suc ε       j = Eq.refl
↑ᵏ-suc (u • v) j = Eq.cong₂ _•_ (↑ᵏ-suc u j) (↑ᵏ-suc v j)

net-↑ᵏ : (w : Word (S.Gen n)) (j : ℕ) → net (w S.↑ᵏ j) ≡ net w ↑ᵏ j
net-↑ᵏ [ g ]ʷ  j = go g j
  where
  go : (g : S.Gen n) (j : ℕ) → φ (g S.↥ᵏ j) ≡ φ g ↑ᵏ j
  go g zero    = Eq.sym (↑ᵏ-zero (φ g))
    where
    ↑ᵏ-zero : (v : Circuit n) → v ↑ᵏ 0 ≡ v
    ↑ᵏ-zero [ h ]ʷ  = Eq.refl
    ↑ᵏ-zero ε       = Eq.refl
    ↑ᵏ-zero (u • v) = Eq.cong₂ _•_ (↑ᵏ-zero u) (↑ᵏ-zero v)
  go g (suc j) = Eq.trans (Eq.cong _↑ (go g j)) (Eq.sym (↑ᵏ-suc (φ g) j))
net-↑ᵏ ε       j = Eq.refl
net-↑ᵏ (u • v) j = Eq.cong₂ _•_ (net-↑ᵏ u j) (net-↑ᵏ v j)

------------------------------------------------------------------------
-- Reversed networks

rev : Word (S.Gen n) → Word (S.Gen n)
rev [ g ]ʷ  = [ g ]ʷ
rev ε       = ε
rev (u • v) = rev v • rev u

private
  -- Every letter of a network is an involution.
  φ-invol : (g : S.Gen n) → n ⊢ φ g • φ g ≈ ε
  φ-invol (S.gate₀ ())
  φ-invol (S.gate₁ ())
  φ-invol (S.gate₂ S.σ-gate) = σ-invol
  φ-invol {suc n} (g S.↥) = lemma-cong↑ (φ g • φ g) ε (φ-invol g)

-- A network followed by its reverse.
net-rev : (w : Word (S.Gen n)) → n ⊢ net w • net (rev w) ≈ ε
net-rev [ g ]ʷ  = φ-invol g
net-rev ε       = PB.left-unit
net-rev (u • v) =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
  (PB.trans (PB.cong PB.refl (PB.cong (net-rev v) PB.refl))
  (PB.trans (PB.cong PB.refl PB.left-unit)
    (net-rev u))))

-- The reverse followed by the network.
rev-net : (w : Word (S.Gen n)) → n ⊢ net (rev w) • net w ≈ ε
rev-net [ g ]ʷ  = φ-invol g
rev-net ε       = PB.left-unit
rev-net (u • v) =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
  (PB.trans (PB.cong PB.refl (PB.cong (rev-net u) PB.refl))
  (PB.trans (PB.cong PB.refl PB.left-unit)
    (rev-net v))))

-- The placement of a circuit by a network.
place : Word (S.Gen n) → Circuit n → Circuit n
place N w = net N • w • net (rev N)

------------------------------------------------------------------------
-- Disjoint circuits commute, and a placement sees only its wires

module _
  (scalars-comm : ∀ {n} (h h′ : Gate 0) →
     n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ)
  where

  open Central-Scalars scalars-comm using (comm-gate₀-w)

  -- A generator widened on top commutes with a circuit shifted past it.
  apart-gen : (g : Gen k) (v : Circuit m) →
    (k + m) ⊢ [ g ↧ᵏ m ]ʷ • (v ↑ᵏ k) ≈ (v ↑ᵏ k) • [ g ↧ᵏ m ]ʷ
  apart-gen (gate₀ h) v = PB.sym (comm-gate₀-w h (v ↑ᵏ _))
  apart-gen {m = m} (gate₁ {j} h) v =
    Eq.subst (λ x → (₁₊ j + m) ⊢ [ gate₁ h ]ʷ • x ≈ x • [ gate₁ h ]ʷ)
      (Eq.sym (↑ᵏ-suc v j))
      (PB.sym (comm-gate₁-w↑ h (v ↑ᵏ j)))
  apart-gen {m = m} (gate₂ {j} h) v =
    Eq.subst (λ x → (₂₊ j + m) ⊢ [ gate₂ h ]ʷ • x ≈ x • [ gate₂ h ]ʷ)
      (Eq.sym (Eq.trans (↑ᵏ-suc v (suc j)) (Eq.cong _↑ (↑ᵏ-suc v j))))
      (PB.sym (comm-gate₂-w↑↑ h (v ↑ᵏ j)))
  apart-gen {m = m} (gate₃ {j} h) v =
    Eq.subst (λ x → (₃₊ j + m) ⊢ [ gate₃ h ]ʷ • x ≈ x • [ gate₃ h ]ʷ)
      (Eq.sym (Eq.trans (↑ᵏ-suc v (₂₊ j))
        (Eq.cong _↑ (Eq.trans (↑ᵏ-suc v (suc j)) (Eq.cong _↑ (↑ᵏ-suc v j))))))
      (PB.sym (comm-gate₃-w↑↑↑ h (v ↑ᵏ j)))
  apart-gen {m = m} (_↥ {j} g) v =
    Eq.subst (λ x → (₁₊ j + m) ⊢ [ (g ↧ᵏ m) ↥ ]ʷ • x ≈ x • [ (g ↧ᵏ m) ↥ ]ʷ)
      (Eq.sym (↑ᵏ-suc v j))
      (lemma-cong↑ ([ g ↧ᵏ m ]ʷ • (v ↑ᵏ j)) ((v ↑ᵏ j) • [ g ↧ᵏ m ]ʷ) (apart-gen g v))

  -- A circuit on the bottom k wires commutes with one k wires up.
  apart : (w : Circuit k) (v : Circuit m) →
    (k + m) ⊢ (w ↓ᵏ m) • (v ↑ᵏ k) ≈ (v ↑ᵏ k) • (w ↓ᵏ m)
  apart [ g ]ʷ  v = apart-gen g v
  apart ε       v = PB.trans PB.left-unit (PB.sym PB.right-unit)
  apart (u • t) v =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (apart t v))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (apart u v) PB.refl)
              PB.assoc)))

  -- A placement of a circuit on the bottom k wires does not see the
  -- network change k wires up.
  frame : (N : Word (S.Gen (k + m))) (M : Word (S.Gen m)) (w : Circuit k) →
    (k + m) ⊢ place (N • (M S.↑ᵏ k)) (w ↓ᵏ m) ≈ place N (w ↓ᵏ m)
  frame {k} {m} N M w =
    Eq.subst (λ x → (k + m) ⊢ (net N • x) • (w ↓ᵏ m) • (net (rev (M S.↑ᵏ k)) • net (rev N))
                              ≈ place N (w ↓ᵏ m))
      (Eq.sym (net-↑ᵏ M k))
      (PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
      (PB.trans (PB.cong PB.refl (PB.cong (apart′) PB.refl))
      (PB.trans (PB.cong PB.refl PB.assoc)
      (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
      (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong cancel PB.refl)))
        (PB.cong PB.refl (PB.cong PB.refl PB.left-unit))))))))
    where
    X = net M ↑ᵏ k
    apart′ : (k + m) ⊢ X • (w ↓ᵏ m) ≈ (w ↓ᵏ m) • X
    apart′ = PB.sym (apart w (net M))
    cancel : (k + m) ⊢ X • net (rev (M S.↑ᵏ k)) ≈ ε
    cancel = Eq.subst (λ x → (k + m) ⊢ x • net (rev (M S.↑ᵏ k)) ≈ ε)
      (net-↑ᵏ M k) (net-rev (M S.↑ᵏ k))
