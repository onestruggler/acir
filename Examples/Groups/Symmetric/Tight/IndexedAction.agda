------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the coset normal form of Sₙ, via Circuit.Uniqueness
--
-- Circuit.Uniqueness derives uniqueness of a coset-tower normal form
-- from an interface: a semantics into a family of groups, a right
-- action of those groups on vectors of per-wire states, and a probe
-- state that lifted circuits fix.  This module supplies that
-- interface for Sₙ under the tight (permutation) semantics, so the
-- result comes out of the generic machinery rather than out of a
-- bespoke argument.
--
-- The states are bit vectors.  A permutation acts on Vec Bool n by
-- carrying the bit at k to position π k, and the distinguished object
-- is false, so the probe state is true ∷ false ⋯ false: one raised
-- bit, on the wire being decided.  A coset representative carries
-- that bit to the position given by the depth of its descriptor, so
-- the resulting vectors determine the coset — which is the c-inj
-- obligation.
--
-- The normal form here is Circuit.CosetNF's own tower, which differs
-- from Examples.Groups.Symmetric.Normalization's by a singleton C 0
-- factor at each level.  The two uniqueness theorems are therefore
-- independent statements about isomorphic towers, and this one does
-- not replace Tight.Uniqueness.unique-nf-tight.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Tight.IndexedAction where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin) renaming (suc to fsuc)
open import Data.Fin.Permutation
  using ( Permutation′ ; id ; _∘ₚ_ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _≈_
        ; inverseˡ ; inverseʳ ; lift₀ )
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base as Vec using (Vec ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties
  using ( lookup∘tabulate ; tabulate∘lookup ; tabulate-cong
        ; lookup-replicate )
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise-≡⇒≡ ; ≡⇒Pointwise-≡)
open import Data.Fin.Properties using (suc-injective)
open import ForStdlib.Algebra.IndexedAction using (IndexedRightAction)
open import ForStdlib.Data.Fin.Permutation.Properties
  using (∘ₚ-id-embedding)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl)

open import Notations
open import Word.Base using (Word)

import Circuit.CosetNF as CosetNF
import Circuit.Uniqueness as CU
import Presentation.Properties as PP
import Normalization.NormalForm.Uniqueness.Propositional as NFU

open import Examples.Groups.Symmetric.Cosets
  using (C ; [_]ᶜ ; σ•_) renaming (ε to εᶜ)
open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Tight.Semantics
  using (Perm ; ⟦_⟧ ; ⟦↑⟧ ; Permutation′-group)
open import Examples.Groups.Symmetric.Tight.Soundness using (sound)

private variable n : ℕ


------------------------------------------------------------------------
-- Permutations acting on bit vectors

-- A permutation acts on a bit vector by carrying the bit at k to
-- position π k; equivalently, the bit at position i of the result is
-- the one at π⁻¹ i.  Reading it through the inverse is what makes
-- this a RIGHT action: the inverse of π ∘ₚ ρ is π⁻¹ after ρ⁻¹, in
-- that order.

infixl 7 _◁_
_◁_ : Vec Bool n → Perm n → Vec Bool n
xs ◁ π = tabulate (λ i → lookup xs (π ⟨$⟩ˡ i))

private
  -- Permutations that agree agree on inverses too: apply the
  -- hypothesis at π⁻¹ i and cancel on both sides.
  ⟨$⟩ˡ-cong : (π ρ : Perm n) → π ≈ ρ → ∀ i → π ⟨$⟩ˡ i ≡ ρ ⟨$⟩ˡ i
  ⟨$⟩ˡ-cong π ρ π≈ρ i = ρ-injective
    (Eq.trans (Eq.trans (Eq.sym (π≈ρ (π ⟨$⟩ˡ i))) (inverseʳ π))
              (Eq.sym (inverseʳ ρ)))
    where
    ρ-injective : ∀ {a b} → ρ ⟨$⟩ʳ a ≡ ρ ⟨$⟩ʳ b → a ≡ b
    ρ-injective eq =
      Eq.trans (Eq.sym (inverseˡ ρ))
        (Eq.trans (Eq.cong (ρ ⟨$⟩ˡ_) eq) (inverseˡ ρ))

  -- The three action laws, stated as equalities of vectors; the
  -- record below wraps them as pointwise equalities.
  -- Everything is explicit here: left implicit, none of these can be
  -- recovered by unification.  π ≈ ρ compares permutations through a
  -- projection, and _◁_ buries its vector under a lookup.
  ◁-cong-≡ : (xs ys : Vec Bool n) (π ρ : Perm n) →
             xs ≡ ys → π ≈ ρ → xs ◁ π ≡ ys ◁ ρ
  ◁-cong-≡ xs _ π ρ refl π≈ρ =
    tabulate-cong (λ i → Eq.cong (lookup xs) (⟨$⟩ˡ-cong π ρ π≈ρ i))

  ◁-identity-≡ : (xs : Vec Bool n) → xs ◁ id ≡ xs
  ◁-identity-≡ xs = tabulate∘lookup xs

  ◁-compose-≡ : (xs : Vec Bool n) (π ρ : Perm n) →
                xs ◁ (π ∘ₚ ρ) ≡ (xs ◁ π) ◁ ρ
  ◁-compose-≡ xs π ρ = Eq.sym
    (tabulate-cong (λ i →
       lookup∘tabulate (λ j → lookup xs (π ⟨$⟩ˡ j)) (ρ ⟨$⟩ˡ i)))

-- The states: bits, compared by propositional equality.
Ob : Setoid 0ℓ 0ℓ
Ob = Eq.setoid Bool

act : IndexedRightAction
        (λ n → Group.rawMonoid (Permutation′-group n)) Ob
act = record
  { _◁_        = _◁_
  ; ◁-cong     = λ {_} {xs} {ys} {π} {ρ} xs≋ys π≈ρ →
                   ≡⇒Pointwise-≡
                     (◁-cong-≡ xs ys π ρ (Pointwise-≡⇒≡ xs≋ys) π≈ρ)
  ; ◁-identity = λ xs → ≡⇒Pointwise-≡ (◁-identity-≡ xs)
  ; ◁-compose  = λ xs π ρ → ≡⇒Pointwise-≡ (◁-compose-≡ xs π ρ)
  }


------------------------------------------------------------------------
-- The probe state

-- A lifted permutation fixes the head and acts on the tail, on the
-- nose: tabulate splits as f zero ∷ tabulate (f ∘ suc), and lift₀'s
-- inverse sends zero to zero and suc j to suc (π⁻¹ j).
private
  lift₀-step : (h : Bool) (t : Vec Bool n) (π : Perm n) →
               (h ∷ t) ◁ lift₀ π ≡ h ∷ (t ◁ π)
  lift₀-step h t π = refl

  -- Every entry of the constant-false vector is false, so any
  -- reindexing of it is itself.
  tabulate-false : ∀ n → tabulate {n = n} (λ _ → false) ≡
                         Vec.replicate n false
  tabulate-false ₀      = refl
  tabulate-false (₁₊ n) = Eq.cong (false ∷_) (tabulate-false n)

  false-fix-≡ : (π : Perm n) →
                Vec.replicate n false ◁ π ≡ Vec.replicate n false
  false-fix-≡ {n} π =
    Eq.trans (tabulate-cong (λ i → lookup-replicate (π ⟨$⟩ˡ i) false))
             (tabulate-false n)

open VecEq Ob using (_≋_)

-- The two obligations about lifting and the probe tail, in the form
-- Circuit.Uniqueness asks for.  ⟦↑⟧ identifies ⟦ w ↑ ⟧ with the
-- embedding lift₀ ⟦ w ⟧, after which lift₀-step applies.
head-fix : (h : Bool) (t : Vec Bool n) (w : Circuit n) →
           ((h ∷ t) ◁ ⟦ w ↑ ⟧) ≋ (h ∷ (t ◁ ⟦ w ⟧))
head-fix h t w = ≡⇒Pointwise-≡
  (Eq.trans (◁-cong-≡ (h ∷ t) (h ∷ t) ⟦ w ↑ ⟧ (lift₀ ⟦ w ⟧)
                      refl (⟦↑⟧ w))
            (lift₀-step h t ⟦ w ⟧))

zz-fix : (w : Circuit n) →
         (Vec.replicate n false ◁ ⟦ w ⟧) ≋ Vec.replicate n false
zz-fix w = ≡⇒Pointwise-≡ (false-fix-≡ ⟦ w ⟧)


------------------------------------------------------------------------
-- Coset representatives are determined by the probe

-- The depth of a coset descriptor is the wire its representative
-- sends wire 0 to.  Distinct descriptors have distinct depths, so
-- recovering the depth recovers the descriptor.

depth : C n → Fin (₁₊ n)
depth εᶜ      = ₀
depth (σ• c) = ₁₊ (depth c)

depth-injective : {c c' : C n} → depth c ≡ depth c' → c ≡ c'
depth-injective {c = εᶜ}    {εᶜ}     _  = refl
depth-injective {c = σ• c} {σ• c'} eq =
  Eq.cong σ•_ (depth-injective (suc-injective eq))

-- [ c ]ᶜ sends wire 0 to wire (depth c): the ε case is the identity,
-- and σ• c first swaps wires 0 and 1, then the lifted [ c ]ᶜ carries
-- wire 1 to wire (1 + depth c) by ⟦↑⟧.
coset-zero : (c : C n) → ⟦ [ c ]ᶜ ⟧ ⟨$⟩ʳ ₀ ≡ depth c
coset-zero εᶜ      = refl
coset-zero (σ• c) =
  Eq.trans (⟦↑⟧ ([ c ]ᶜ) (₁₊ ₀)) (Eq.cong fsuc (coset-zero c))

private
  -- The probe has its single raised bit at wire 0.
  probe : ∀ n → Vec Bool (₁₊ n)
  probe n = true ∷ Vec.replicate n false

  probe-true : {k : Fin (₁₊ n)} → lookup (probe n) k ≡ true → k ≡ ₀
  probe-true {k = ₀}    _  = refl
  probe-true {k = ₁₊ j} eq
    with Eq.trans (Eq.sym (lookup-replicate j false)) eq
  ... | ()

c-inj : {c1 c2 : C n} →
        (∀ (h : Bool) → let t = Vec.replicate n false in
           ((h ∷ t) ◁ ⟦ [ c1 ]ᶜ ⟧) ≋ ((h ∷ t) ◁ ⟦ [ c2 ]ᶜ ⟧)) →
        c1 ≡ c2
c-inj {n} {c1} {c2} hyp = depth-injective claim
  where
  π1 = ⟦ [ c1 ]ᶜ ⟧
  π2 = ⟦ [ c2 ]ᶜ ⟧

  -- Acting on the probe and reading position j gives the bit at π⁻¹ j.
  at : (π : Perm (₁₊ n)) (j : Fin (₁₊ n)) →
       lookup (probe n ◁ π) j ≡ lookup (probe n) (π ⟨$⟩ˡ j)
  at π j = lookup∘tabulate (λ i → lookup (probe n) (π ⟨$⟩ˡ i)) j

  -- π1 carries the raised bit to depth c1, so the vectors agree there
  -- only if π2 carries it there too.
  raised : lookup (probe n ◁ π1) (depth c1) ≡ true
  raised = Eq.trans (at π1 (depth c1))
             (Eq.cong (lookup (probe n))
               (Eq.trans (Eq.cong (π1 ⟨$⟩ˡ_) (Eq.sym (coset-zero c1)))
                         (inverseˡ π1)))

  shared : lookup (probe n) (π2 ⟨$⟩ˡ (depth c1)) ≡ true
  shared = Eq.trans (Eq.sym (at π2 (depth c1)))
             (Eq.trans (Eq.cong (λ v → lookup v (depth c1))
                                (Eq.sym (Pointwise-≡⇒≡ (hyp true))))
                       raised)

  claim : depth c1 ≡ depth c2
  claim = Eq.trans
    (Eq.trans (Eq.sym (inverseʳ π2))
              (Eq.cong (π2 ⟨$⟩ʳ_) (probe-true shared)))
    (coset-zero c2)


------------------------------------------------------------------------
-- The semantics as a monoid homomorphism

-- ⟦_⟧ is built by Normalization.StarInterp.Extend, which preserves ε
-- and _•_ on the nose, so only the congruence has content — and that
-- is soundness.
mhomo : ∀ n → MonoidMorphisms.IsMonoidHomomorphism
                (Monoid.rawMonoid (PP.•-ε-monoid (n VRel,_===_)))
                (Group.rawMonoid (Permutation′-group n))
                (⟦_⟧ {n})
mhomo n = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism =
        record { cong = λ {w} {v} → sound {n} {w} {v} }
    ; homo = λ _ _ _ → refl
    }
  ; ε-homo = λ _ → refl
  }

-- Lifting a circuit by a wire is the embedding lift₀ of Sₙ into Sₙ₊₁.
-- Stated with w explicit: passed against Circuit.Uniqueness's
-- implicit-headed parameter it would be left as an unsolved meta,
-- permutation equality comparing through a projection.
compat : (w : Circuit n) → ⟦ w ↑ ⟧ ≈ lift₀ ⟦ w ⟧
compat w = ⟦↑⟧ w


------------------------------------------------------------------------
-- Uniqueness of the normal form

module Uniq = CU C εᶜ Gate [_]ᶜ Permutation′-group ∘ₚ-id-embedding
                 _SRel,_===_ ⟦_⟧ mhomo (λ {n} {w} → compat {n} w)
                 Ob act head-fix false zz-fix c-inj

open CosetNF C εᶜ Gate [_]ᶜ using (NF ; inv-nf)

-- Normal forms of the coset tower with equal denotations are equal.
unique-nf : ∀ n →
            let open NFU (n VRel,_===_) (NF n)
                         (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
            in UniqueNormalForm (inv-nf {n})
unique-nf = Uniq.unique-nf
