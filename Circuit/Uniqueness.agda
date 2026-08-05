{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word ; ε ; _•_)
open import Level using (0ℓ ; _⊔_)
open import Relation.Binary using (Setoid)
open import Data.Nat using (ℕ)
open import Data.Vec.Base using (Vec)
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Algebra.Bundles.Raw using (RawMonoid)
import Circuit.Base as CB
import Presentation.Base as PB
open import Notations
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import ForStdlib.Algebra.IndexedAction using (IndexedRightAction)

module Circuit.Uniqueness
  (C : ℕ -> Set)
  (I : ∀ {n} -> C n)
  (Gate : ℕ -> Set)
  (let open CB Gate)
  ([_]ᶜ : ∀ {n} -> C n -> Circuit (₁₊ n))
  {c d} (Sem : ℕ -> Setoid c d)
  (⟦_⟧ : ∀ {n} -> Circuit n → Setoid.Carrier (Sem n))
  (_SRel,_===_ : (n : ℕ) → CRel n)
  (let open Lift-Relation _SRel,_===_)
  (sem-sound : ∀ {n} ->
    let open PB (n VRel,_===_) renaming (_≈_ to _≈ₐ_) in
    let open Setoid (Sem n) renaming (_≈_ to _≈ₛ_) in
    ∀ {w v} -> w ≈ₐ v -> ⟦ w ⟧ ≈ₛ ⟦ v ⟧)
  -- Circuits compared through their semantics form a raw monoid ...
  (let ⟦⟧-rawMonoid : ℕ -> RawMonoid 0ℓ d
       ⟦⟧-rawMonoid n = record
         { Carrier = Circuit n
         ; _≈_     = λ w v -> Setoid._≈_ (Sem n) ⟦ w ⟧ ⟦ v ⟧
         ; _∙_     = _•_
         ; ε       = ε
         })
  -- ... which acts on the right on vectors of single-wire states
  -- over the object setoid Ob, one object per wire
  -- (ForStdlib.Algebra.IndexedAction): ◁-cong says the action
  -- factors through the semantics, ◁-compose that acting by w • v is
  -- acting by w then v.
  {s e} (Ob : Setoid s e)
  (act : IndexedRightAction ⟦⟧-rawMonoid Ob)
  (let open IndexedRightAction act using (_◁_ ; ◁-cong ; ◁-compose))
  (let open VecEq Ob using (_≋_))
  -- A base state fixed by every lifted circuit ...
  (base : ∀ {n} -> Vec (Setoid.Carrier Ob) n)
  (base-fix : ∀ {n} (w : Circuit n) -> (base ◁ (w ↑)) ≋ base)
  -- ... on which the coset representatives act injectively.
  (c-inj : ∀ {n} {c1 c2 : C n} ->
    (base ◁ [ c1 ]ᶜ) ≋ (base ◁ [ c2 ]ᶜ) -> c1 ≡ c2)
  where

open import Circuit.CosetNF C I Gate [_]ᶜ

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Function using (_∘_)
open import Function.Bundles using (Injection ; Bijection ; RightInverse ; _⟶ₛ_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable using (via-injection)
open import Word.Base

open VecEq Ob using (≋-setoid ; ≋-refl ; ≋-sym)

-- The top coset of a normal form is determined by the semantics: act
-- with both sides of eq on the base state.  The lifted prefixes fix
-- it (base-fix), so what remains is the action of the two coset
-- representatives, which c-inj separates.  No case split on the
-- width: at width 0 the lifted prefix is ε ↑ = ε, fixed by base-fix
-- like any other lift.
coset-unique : ∀ n (l l' : NF n) (r r' : C n)
  → let open Setoid (Sem (₁₊ n)) in
  (eq : ⟦ (inv-nf {n} l ↑) • [ r ]ᶜ ⟧ ≈ ⟦ (inv-nf l') ↑ • [ r' ]ᶜ ⟧)
  → r ≡ r'
coset-unique n l l' r r' eq = c-inj claim
  where
  module Semn = Setoid (Sem (₁₊ n))
  open SR (≋-setoid (₁₊ n))

  claim : (base ◁ [ r ]ᶜ) ≋ (base ◁ [ r' ]ᶜ)
  claim = begin
    base ◁ [ r ]ᶜ
      ≈⟨ ◁-cong (≋-sym (base-fix (inv-nf l))) Semn.refl ⟩
    (base ◁ (inv-nf l ↑)) ◁ [ r ]ᶜ
      ≈⟨ ≋-sym (◁-compose base (inv-nf l ↑) [ r ]ᶜ) ⟩
    base ◁ ((inv-nf l ↑) • [ r ]ᶜ)
      ≈⟨ ◁-cong ≋-refl eq ⟩
    base ◁ ((inv-nf l' ↑) • [ r' ]ᶜ)
      ≈⟨ ◁-compose base (inv-nf l' ↑) [ r' ]ᶜ ⟩
    (base ◁ (inv-nf l' ↑)) ◁ [ r' ]ᶜ
      ≈⟨ ◁-cong (base-fix (inv-nf l')) Semn.refl ⟩
    base ◁ [ r' ]ᶜ
      ∎



{-
open import Presentation.Base Γ
open import Presentation.Core Γ using (word-setoid)
open import Function.Definitions using (Congruent ; Injective ; Surjective ; StrictlySurjective)
open import Function.Consequences using (surjective⇒strictlySurjective ; strictlySurjective⇒surjective)


NFs : Setoid 0ℓ 0ℓ
NFs = {!!}

open import Normalization.NormalForm.Propositional Γ (NF 0) using (NormalForm)
open import Normalization.NormalForm.Uniqueness.Setoid Γ (NF 0) Sem ⟦_⟧

private
  variable
    w v : Word X

open Setoid NFs public using ()
  renaming (Carrier to |NF| ; _≈_ to _≈ₙ_ ; refl to reflₙ ; sym to symₙ ; trans to transₙ)
open Setoid Sem using ()
  renaming (Carrier to Cₛ ; _≈_ to _≈₂_ ; sym to sym₂)

--module _
-}
