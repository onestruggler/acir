------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the coset normal form of Sₙ, via Circuit.Uniqueness
--
-- Circuit.Uniqueness derives uniqueness of a coset-tower normal form
-- from an interface: a semantics into a family of monoids, a left
-- action of those monoids on vectors of per-wire states, and the fact
-- that lifted circuits fix the head.  This module supplies that
-- interface for Sₙ under the tight (permutation) semantics, so the
-- result comes out of the generic machinery rather than out of a
-- bespoke argument.
--
-- The states are bit vectors: a permutation carries the bit at π k to
-- position k, which is a LEFT action.  Its two coset obligations both
-- come out of the single fact that [ c ]ᶜ sends wire 0 to wire
-- (depth c) — injectivity because a bit vector can be chosen to
-- separate any two wires, and surjectivity because a permutation can
-- be run backwards.
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
open import Data.Fin.Properties using (_≟_ ; suc-injective)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax ; _,_)
open import Data.Vec.Base as Vec using (Vec ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties
  using ( lookup∘tabulate ; tabulate∘lookup ; tabulate-cong
        ; lookup-replicate )
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise-≡⇒≡ ; ≡⇒Pointwise-≡)
open import ForStdlib.Algebra.IndexedAction using (IndexedLeftAction)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (yes ; no)
open import Relation.Nullary.Negation using (contradiction)

open import Notations
open import Word.Base using (Word)

import Circuit.CosetNF as CosetNF
import Circuit.Uniqueness as CU
import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Presentation.Properties as PP

open import Examples.Groups.Symmetric.Cosets
  using (C ; [_]ᶜ ; σ•_) renaming (ε to εᶜ)
open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Tight.Semantics
  using (Perm ; ⟦_⟧ ; ⟦↑⟧ ; Permutation′-group)
open import Examples.Groups.Symmetric.Tight.Soundness using (sound)

private variable n : ℕ


------------------------------------------------------------------------
-- Permutations acting on bit vectors

-- π carries the bit at π k to position k; equivalently the bit at
-- position i of the result is the one at π i.  Reading it forwards is
-- what makes this a LEFT action: π ∘ₚ ρ applies π first, so acting by
-- it is acting by ρ and then by π.

infixr 7 _▷_
_▷_ : Perm n → Vec Bool n → Vec Bool n
π ▷ xs = tabulate (λ i → lookup xs (π ⟨$⟩ʳ i))

private
  -- Everything is explicit here: left implicit, none of these can be
  -- recovered by unification, since π ≈ ρ compares permutations
  -- through a projection and _▷_ buries its vector under a lookup.
  ▷-cong-≡ : (π ρ : Perm n) (xs ys : Vec Bool n) →
             π ≈ ρ → xs ≡ ys → π ▷ xs ≡ ρ ▷ ys
  ▷-cong-≡ π ρ xs _ π≈ρ refl =
    tabulate-cong (λ i → Eq.cong (lookup xs) (π≈ρ i))

  ▷-identity-≡ : (xs : Vec Bool n) → id ▷ xs ≡ xs
  ▷-identity-≡ xs = tabulate∘lookup xs

  ▷-compose-≡ : (π ρ : Perm n) (xs : Vec Bool n) →
                (π ∘ₚ ρ) ▷ xs ≡ π ▷ (ρ ▷ xs)
  ▷-compose-≡ π ρ xs = Eq.sym
    (tabulate-cong (λ i →
       lookup∘tabulate (λ j → lookup xs (ρ ⟨$⟩ʳ j)) (π ⟨$⟩ʳ i)))

-- The states: bits, compared by propositional equality.
Ob : Setoid 0ℓ 0ℓ
Ob = Eq.setoid Bool

act : IndexedLeftAction
        (λ n → Monoid.rawMonoid (Group.monoid (Permutation′-group n)))
        Ob
act = record
  { _▷_        = _▷_
  ; ▷-cong     = λ {_} {π} {ρ} {xs} {ys} π≈ρ xs≋ys →
                   ≡⇒Pointwise-≡
                     (▷-cong-≡ π ρ xs ys π≈ρ (Pointwise-≡⇒≡ xs≋ys))
  ; ▷-identity = λ xs → ≡⇒Pointwise-≡ (▷-identity-≡ xs)
  ; ▷-compose  = λ π ρ xs → ≡⇒Pointwise-≡ (▷-compose-≡ π ρ xs)
  }

open VecEq Ob using (_≋_)

-- A lifted permutation fixes the head and acts on the tail, on the
-- nose: tabulate splits as f zero ∷ tabulate (f ∘ suc), and lift₀
-- sends zero to zero and suc j to suc (π j).
head-fix : (h : Bool) (t : Vec Bool n) (w : Circuit n) →
           (⟦ w ↑ ⟧ ▷ (h ∷ t)) ≋ (h ∷ (⟦ w ⟧ ▷ t))
head-fix h t w = ≡⇒Pointwise-≡
  (▷-cong-≡ ⟦ w ↑ ⟧ (lift₀ ⟦ w ⟧) (h ∷ t) (h ∷ t) (⟦↑⟧ w) refl)


------------------------------------------------------------------------
-- Where a coset representative sends wire 0

-- The depth of a coset descriptor is the wire its representative
-- sends wire 0 to.  Distinct descriptors have distinct depths, so
-- recovering the depth recovers the descriptor.

depth : C n → Fin (₁₊ n)
depth εᶜ     = ₀
depth (σ• c) = ₁₊ (depth c)

depth-injective : {c c' : C n} → depth c ≡ depth c' → c ≡ c'
depth-injective {c = εᶜ}   {εᶜ}    _  = refl
depth-injective {c = σ• c} {σ• c'} eq =
  Eq.cong σ•_ (depth-injective (suc-injective eq))

-- [ c ]ᶜ sends wire 0 to wire (depth c): the ε case is the identity,
-- and σ• c first swaps wires 0 and 1, then the lifted [ c ]ᶜ carries
-- wire 1 to wire (1 + depth c) by ⟦↑⟧.
coset-zero : (c : C n) → ⟦ [ c ]ᶜ ⟧ ⟨$⟩ʳ ₀ ≡ depth c
coset-zero εᶜ     = refl
coset-zero (σ• c) =
  Eq.trans (⟦↑⟧ ([ c ]ᶜ) (₁₊ ₀)) (Eq.cong fsuc (coset-zero c))


------------------------------------------------------------------------
-- The two coset obligations

-- Acting on a state and reading its head reads the state at the wire
-- that the representative sends wire 0 to.
private
  head-▷ : (π : Perm (₁₊ n)) (ps : Vec Bool (₁₊ n)) →
           Vec.head (π ▷ ps) ≡ lookup ps (π ⟨$⟩ʳ ₀)
  head-▷ π ps = refl

  -- The bit vector raised at exactly one wire.
  δ : Fin n → Vec Bool n
  δ ₀      = true ∷ Vec.replicate _ false
  δ (₁₊ i) = false ∷ δ i

  δ-diag : (i : Fin n) → lookup (δ i) i ≡ true
  δ-diag ₀      = refl
  δ-diag (₁₊ i) = δ-diag i

  δ-raised : (i j : Fin n) → lookup (δ i) j ≡ true → i ≡ j
  δ-raised ₀      ₀      _  = refl
  δ-raised ₀      (₁₊ j) eq =
    contradiction (Eq.trans (Eq.sym (lookup-replicate j false)) eq) λ ()
  δ-raised (₁₊ i) ₀      ()
  δ-raised (₁₊ i) (₁₊ j) eq = Eq.cong fsuc (δ-raised i j eq)

  -- Two wires that no bit vector separates are equal: δ i separates i
  -- from every other wire.
  lookup-injective : {i j : Fin n} →
                     (∀ (ps : Vec Bool n) → lookup ps i ≡ lookup ps j) →
                     i ≡ j
  lookup-injective {i = i} {j} h =
    δ-raised i j (Eq.trans (Eq.sym (h (δ i))) (δ-diag i))

c-inj : {c1 c2 : C n} →
        (∀ (ps : Vec Bool (₁₊ n)) →
           Vec.head (⟦ [ c1 ]ᶜ ⟧ ▷ ps) ≡ Vec.head (⟦ [ c2 ]ᶜ ⟧ ▷ ps)) →
        c1 ≡ c2
c-inj {n} {c1} {c2} hyp = depth-injective claim
  where
  claim : depth c1 ≡ depth c2
  claim = Eq.trans (Eq.sym (coset-zero c1))
            (Eq.trans (lookup-injective hyp) (coset-zero c2))

-- Every tail is the tail of the representative's action on some
-- state: run the permutation backwards on false ∷ qs.
c-surj : (c : C n) (qs : Vec Bool n) →
         Σ[ ps ∈ Vec Bool (₁₊ n) ] (Vec.tail (⟦ [ c ]ᶜ ⟧ ▷ ps)) ≋ qs
c-surj {n} c qs = pull , ≡⇒Pointwise-≡ claim
  where
  π = ⟦ [ c ]ᶜ ⟧

  pull : Vec Bool (₁₊ n)
  pull = tabulate (λ k → lookup (false ∷ qs) (π ⟨$⟩ˡ k))

  claim : Vec.tail (π ▷ pull) ≡ qs
  claim = Eq.trans
    (tabulate-cong (λ j → Eq.trans
      (lookup∘tabulate (λ k → lookup (false ∷ qs) (π ⟨$⟩ˡ k))
                       (π ⟨$⟩ʳ (₁₊ j)))
      (Eq.cong (lookup (false ∷ qs)) (inverseˡ π))))
    (tabulate∘lookup qs)


------------------------------------------------------------------------
-- The semantics as a monoid homomorphism

-- ⟦_⟧ is built by Normalization.StarInterp.Extend, which preserves ε
-- and _•_ on the nose, so only the congruence has content — and that
-- is soundness.
mhomo : ∀ n → MonoidMorphisms.IsMonoidHomomorphism
                (Monoid.rawMonoid (PP.•-ε-monoid (n VRel,_===_)))
                (Monoid.rawMonoid (Group.monoid (Permutation′-group n)))
                (⟦_⟧ {n})
mhomo n = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism =
        record { cong = λ {w} {v} → sound {n} {w} {v} }
    ; homo = λ _ _ _ → refl
    }
  ; ε-homo = λ _ → refl
  }


------------------------------------------------------------------------
-- Uniqueness of the normal form

module Uniq =
  CU C εᶜ Gate [_]ᶜ (λ n → Group.monoid (Permutation′-group n))
     _SRel,_===_ ⟦_⟧ mhomo Ob act head-fix
                 (λ {n} {c1} {c2} → c-inj {n} {c1} {c2}) c-surj

open CosetNF C εᶜ Gate [_]ᶜ using (NF ; inv-nf)

-- Normal forms of the coset tower with equal denotations are equal.
unique-nf : ∀ n →
            let open NFU (n VRel,_===_) (NF n)
                         (Monoid.setoid
                            (Group.monoid (Permutation′-group n)))
                         (⟦_⟧ {n})
            in UniqueNormalForm (inv-nf {n})
unique-nf = Uniq.unique-nf
