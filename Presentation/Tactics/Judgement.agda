------------------------------------------------------------------------
-- Presentations of groups
--
-- Judgements Γ ⊢ w === v, as a view of the monoid congruence of
-- Presentation.Base: a context Γ is a word relation, and Γ ⊢ w === v
-- is PB._≈_ Γ w v, with the same rules (axiom, refl, symm, trans,
-- cong, assoc, left-unit, right-unit), available here as patterns.
--
-- This is the interface of the Agda code accompanying Bian and
-- Selinger, "Generators and relations for 2-qubit Clifford+T
-- operators" and "… for 3-qubit Clifford+CS operators" (CC BY 2.0),
-- whose tactics (Presentation.Tactics.*) and computer-generated proofs
-- are written against it.  Besides the judgement it provides their
-- equational syntax, subtheories, and the combination of presentations
-- over a sum of alphabets.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Presentation.Tactics.Judgement where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB

infix 6 _===_
infix 5 _⊢_ _∈_

------------------------------------------------------------------------
-- Relations, contexts and judgements

-- A relation is a pair of words, written w === v.
data Relation (X : Set) : Set where
  _===_ : Word X → Word X → Relation X

-- A context is a set of relations: a word relation.
Context : Set → Set₁
Context X = WRel X

_∈_ : ∀ {X} → Relation X → Context X → Set
(w === v) ∈ Γ = Γ w v

-- The empty context.
∅ : ∀ {X} → Context X
∅ _ _ = ⊥

-- Γ ⊢ w === v: the relation follows from Γ.
_⊢_ : ∀ {X} → Context X → Relation X → Set
Γ ⊢ (w === v) = PB._≈_ Γ w v

-- The rules are the constructors of Presentation.Base._≈_.
pattern axiom a = PB.axiom a
pattern refl = PB.refl
pattern symm p = PB.sym p
pattern trans p q = PB.trans p q
pattern cong p q = PB.cong p q
pattern assoc = PB.assoc
pattern left-unit = PB.left-unit
pattern right-unit = PB.right-unit

------------------------------------------------------------------------
-- Soundness and completeness of a translation

_is-sound-wrt_and_ : ∀ {X Y} → Context X → Context Y → (f : X → Word Y) → Set
_is-sound-wrt_and_ {X} Γ Δ f = ∀ {w v : Word X} → Γ ⊢ w === v → Δ ⊢ (f ʷ) w === (f ʷ) v

_is-complete-wrt_and_ : ∀ {X Y} → Context X → Context Y → (f : X → Word Y) → Set
_is-complete-wrt_and_ {X} Γ Δ f = ∀ {w v : Word X} → Δ ⊢ (f ʷ) w === (f ʷ) v → Γ ⊢ w === v

------------------------------------------------------------------------
-- Equational reasoning
--
-- To prove Γ ⊢ a₀ === aₙ:
--
--   equational a₀
--           by reason₁
--       equals a₁
--          …
--           by reasonₙ
--       equals aₙ

module Monoid-Equational where

  infix 2 equational_
  infixl 1 by-equals
  infixl 4 _reversed
  infixl 3 left_
  infixl 3 right_

  equational_ : ∀ {X : Set} {Γ : Context X} (w : Word X) → Γ ⊢ w === w
  equational_ w = refl

  by-equals : ∀ {X : Set} {Γ : Context X} {w v : Word X} → Γ ⊢ w === v → (u : Word X) → Γ ⊢ v === u → Γ ⊢ w === u
  by-equals E u reason = trans E reason

  syntax by-equals E u reason = E by reason equals u

  _reversed : ∀ {X : Set} {Γ : Context X} {w v : Word X} → Γ ⊢ w === v → Γ ⊢ v === w
  _reversed p = symm p

  left_ : ∀ {X : Set} {Γ : Context X} {w v u : Word X} → Γ ⊢ w === v → Γ ⊢ w • u === v • u
  left_ E = cong E refl

  right_ : ∀ {X : Set} {Γ : Context X} {w v u : Word X} → Γ ⊢ w === v → Γ ⊢ u • w === u • v
  right_ E = cong refl E

  -- Reflexivity from propositional equality.
  refl' : ∀ {X : Set} {Γ : Context X} {w v : Word X} → w ≡ v → Γ ⊢ w === v
  refl' Eq.refl = refl

  -- A synonym for refl: "by definition".
  definition : ∀ {X : Set} {Γ : Context X} {w} → Γ ⊢ w === w
  definition = refl

------------------------------------------------------------------------
-- Subtheories

module Monoid-Subtheories where

  -- Γ ⊆ Γ′: every theorem of Γ is a theorem of Γ′.
  _⊆_ : ∀ {X : Set} → Context X → Context X → Set
  Γ ⊆ Γ′ = ∀ {w v} → Γ ⊢ w === v → Γ′ ⊢ w === v

  -- It suffices that each axiom of Γ be a theorem of Γ′.
  lemma-⊆ : ∀ {X : Set} {Γ Γ′ : Context X} → (∀ {w v} → w === v ∈ Γ → Γ′ ⊢ w === v) → Γ ⊆ Γ′
  lemma-⊆ hyp (axiom x) = hyp x
  lemma-⊆ hyp refl = refl
  lemma-⊆ hyp (symm p) = symm (lemma-⊆ hyp p)
  lemma-⊆ hyp (trans p q) = trans (lemma-⊆ hyp p) (lemma-⊆ hyp q)
  lemma-⊆ hyp (cong p q) = cong (lemma-⊆ hyp p) (lemma-⊆ hyp q)
  lemma-⊆ hyp assoc = assoc
  lemma-⊆ hyp left-unit = left-unit
  lemma-⊆ hyp right-unit = right-unit

------------------------------------------------------------------------
-- Sums of alphabets

infixr 2 _∪_
infix 9 ⌜_
infix 10 _⌝

data _∪_ (A B : Set) : Set where
  ⌜_ : A → A ∪ B
  _⌝ : B → A ∪ B

infix 10 _⌟
infix 9 ⌞_

-- Words over the right and left summands.
_⌟ : ∀ {A B} → Word B → Word (A ∪ B)
x ⌟ = wmap _⌝ x

⌞_ : ∀ {A B} → Word A → Word (A ∪ B)
⌞ x = wmap ⌜_ x

infix 10 _◹
infix 9 ◸_

◸_ : ∀ {A B} → Relation A → Relation (A ∪ B)
◸ (x === y) = ⌞ x === ⌞ y

_◹ : ∀ {A B} → Relation B → Relation (A ∪ B)
(x === y) ◹ = x ⌟ === y ⌟

infixr 10 _⊹_⊹_
infix 10 ◃_▹
infix 10 ◂_▸
infix 10 _⌋
infix 9 ⌊_

-- The relations of Γ₁ and Γ₂ over the two summands, and Γ over the sum.
data _⊹_⊹_ {A B} (Γ₁ : Context A) (Γ₂ : Context B) (Γ : Context (A ∪ B)) : Context (A ∪ B) where
  ⌜_ : ∀ {u v} → u === v ∈ Γ₁ → ◸ (u === v) ∈ Γ₁ ⊹ Γ₂ ⊹ Γ
  _⌝ : ∀ {u v} → u === v ∈ Γ₂ → (u === v) ◹ ∈ Γ₁ ⊹ Γ₂ ⊹ Γ
  ◃_▹ : ∀ {u v} → u === v ∈ Γ → u === v ∈ Γ₁ ⊹ Γ₂ ⊹ Γ

⌊_ : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ : Context (A ∪ B)} {u v} →
     Γ₁ ⊢ u === v → Γ₁ ⊹ Γ₂ ⊹ Γ ⊢ ◸ (u === v)
⌊ (axiom x) = axiom (⌜ x)
⌊ refl = refl
⌊ (symm d) = symm (⌊ d)
⌊ (trans d d₁) = trans (⌊ d) (⌊ d₁)
⌊ (cong d d₁) = cong (⌊ d) (⌊ d₁)
⌊ assoc = assoc
⌊ left-unit = left-unit
⌊ right-unit = right-unit

_⌋ : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ : Context (A ∪ B)} {u v} →
     Γ₂ ⊢ u === v → Γ₁ ⊹ Γ₂ ⊹ Γ ⊢ (u === v) ◹
(axiom x) ⌋ = axiom (x ⌝)
refl ⌋ = refl
(symm d) ⌋ = symm (d ⌋)
(trans d d₁) ⌋ = trans (d ⌋) (d₁ ⌋)
(cong d d₁) ⌋ = cong (d ⌋) (d₁ ⌋)
assoc ⌋ = assoc
left-unit ⌋ = left-unit
right-unit ⌋ = right-unit

◂_▸ : ∀ {A B} {Γ₁ : Context A} {Γ₂ : Context B} {Γ : Context (A ∪ B)} {u v} →
      Γ ⊢ u === v → Γ₁ ⊹ Γ₂ ⊹ Γ ⊢ u === v
◂ (axiom x) ▸ = axiom ◃ x ▹
◂ refl ▸ = refl
◂ (symm d) ▸ = symm ◂ d ▸
◂ (trans d d₁) ▸ = trans ◂ d ▸ ◂ d₁ ▸
◂ (cong d d₁) ▸ = cong ◂ d ▸ ◂ d₁ ▸
◂ assoc ▸ = assoc
◂ left-unit ▸ = left-unit
◂ right-unit ▸ = right-unit
