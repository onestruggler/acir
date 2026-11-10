------------------------------------------------------------------------
-- Presentations of groups
--
-- The alternating group 𝔄₁₆ as reversible circuits on four wires over
-- X, CX, CCX and Ex: the main theorem
--
-- The circuits on four wires over NOT, CNOT, Toffoli and the swap,
-- modulo the seven rules of Theory (r1, …, r7, the rules of
-- XCXCCX-4bit's Figure 1 restated over Circuit.Prop), are a
-- presentation of the even permutations of the sixteen states.  It is
-- obtained from Lafont's presentation of 𝔄₁₆ by the cycles ω₀, …, ω₁₃
-- (Examples.Groups.Alternating) in two Reidemeister–Schreier steps,
-- each a pair of translations that carry the relations of their source
-- to consequences of those of their target and are inverse on
-- generators.
--
-- * From Lafont's words to circuits: f reads a gate as a word in the
--   cycles, g a cycle as a circuit, and the circuits' relation is the
--   translated one (_CRel,_===_, Syntactics): Lafont's relations read
--   on the cycles' circuits, and one rule per gate naming its word.
--
-- * From the translated relation to the rules (_RRel,_===_): the same
--   gates and the identity translations, so the step is that each
--   relation set's rules follow from the other's.  The translated
--   relations are derived from r1, …, r7 without another development's
--   theorems: the rules are complete on one, two and three wires by a
--   step of the same kind from Symmetric's presentation
--   (presentation₁, …, complete₃), and the four-wire derivations rest
--   on those and on rule (7).
--
-- Both relation sets are sound and complete for the functions on
-- states, and every circuit is equal to a unique canonical circuit,
-- the translation of Lafont's canonical form.
--
-- This module collects the statements behind one import: the circuits
-- and their relations, derivability ⊢_≈_ and ⊢ᴿ_≈_, a circuit's
-- function ⟦_⟧ with pointwise equality _≐_ and its even permutation
-- ⟦_⟧ᴬ, the numbering enc, dec of the states, and the theorems.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.MainTheorem where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike
  using (Grouplike ; module Group-Lemmas)
open import Word.Base using ([_]ʷ ; _ʷ)

open import Examples.Groups.Alternating.Normalization using (inv-nf)
import Examples.Groups.Alternating.Presentation as LA
open import Examples.Groups.Alternating.Semantics
  using (Alt ; Alt-group ; _≈ᴬ_ ; perm)
import Examples.Groups.Alternating.Syntactics as L

open import Examples.Groups.Alt16-RevCir.Syntactics public
  using (Gen ; Circuit) renaming (_VRel,_===_ to _CRel,_===_)
open import Examples.Groups.Alt16-RevCir.Translation public
  using (f ; g)
open import Examples.Groups.Alt16-RevCir.Semantics public
  using (Bits ; _≐_)
open import Examples.Groups.Alt16-RevCir.Numbering public
  using (enc ; dec)
open import Examples.Groups.Alt16-RevCir.NormalForm public
  using (NF ; canon ; nf)
open import Examples.Groups.Alt16-RevCir.Theory public
  using (_TRel,_===_ ; r1 ; r2 ; r3 ; r4 ; r5 ; r6 ; r7)
open import Examples.Groups.Alt16-RevCir.ThreeWire public
  using ( presentation₁ ; presentation₂ ; presentation₃
        ; complete₁ ; complete₂ ; complete₃ )
import Examples.Groups.Alt16-RevCir.Equivalence as E
import Examples.Groups.Alt16-RevCir.Iso as I
import Examples.Groups.Alt16-RevCir.NormalForm as N
import Examples.Groups.Alt16-RevCir.Presentation as P
import Examples.Groups.Alt16-RevCir.Semantics as Sem
import Examples.Groups.Alt16-RevCir.Theory as Th

open GroupMorphisms using (IsGroupIsomorphism)

-- Lafont's relation between the words in the cycles ω₀, …, ω₁₃.
infix 4 _LRel_
_LRel_ : L.Circuit 16 → L.Circuit 16 → Set
_LRel_ = L._VRel,_===_ 16

-- Equality by the rules, of circuits and of words in the cycles.
infix 4 ⊢_≈_ ⊢ᴸ_≈_
⊢_≈_ : Circuit 4 → Circuit 4 → Set
⊢_≈_ = PB._≈_ (4 CRel,_===_)

⊢ᴸ_≈_ : L.Circuit 16 → L.Circuit 16 → Set
⊢ᴸ_≈_ = PB._≈_ _LRel_

-- The rules r1, …, r7, with the laws of the swap and the structural
-- rules, and equality by them.
infix 4 _RRel,_===_ ⊢ᴿ_≈_
_RRel,_===_ : (n : ℕ) → Circuit n → Circuit n → Set
_RRel,_===_ = Th.T._VRel,_===_

⊢ᴿ_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢ᴿ_≈_ {n} = PB._≈_ (n RRel,_===_)

-- A circuit's function on the states of its wires,
⟦_⟧ : ∀ {n} → Circuit n → Bits n → Bits n
⟦_⟧ = Sem.⟦_⟧

-- and its even permutation of the sixteen positions: that of its word
-- in the cycles.
⟦_⟧ᴬ : Circuit 4 → Alt 16
⟦_⟧ᴬ = P.⟦_⟧ᴬ

------------------------------------------------------------------------
-- The first step: Lafont's words and the circuits

-- Each translation carries the relations of its source to consequences
-- of the relations of its target,
f-well-defined : ∀ {w v} → 4 CRel, w === v → ⊢ᴸ (f ʷ) w ≈ (f ʷ) v
f-well-defined = I.Theorem.f-well-defined

g-well-defined : ∀ {u t} → u LRel t → ⊢ (g ʷ) u ≈ (g ʷ) t
g-well-defined = I.Theorem.g-well-defined

-- and the two are inverse to each other on generators.
f-left-inv-gen : (y : L.Gen 16) → ⊢ᴸ [ y ]ʷ ≈ (f ʷ) (g y)
f-left-inv-gen = I.Theorem.f-left-inv-gen

g-left-inv-gen : (x : Gen 4) → ⊢ [ x ]ʷ ≈ (g ʷ) (f x)
g-left-inv-gen = I.Theorem.g-left-inv-gen

-- So the circuits modulo their rules and the words in the cycles
-- modulo Lafont's relations are isomorphic groups.
grouplike : Grouplike (4 CRel,_===_)
grouplike = I.Theorem.grouplike

grouplikeᴸ : Grouplike _LRel_
grouplikeᴸ = _IsPresentationOf_.gl (LA.presentation {16})

circuits≅cycles :
  IsGroupIsomorphism
    (Group.rawGroup (Group-Lemmas.•-ε-group (4 CRel,_===_) grouplike))
    (Group.rawGroup (Group-Lemmas.•-ε-group _LRel_ grouplikeᴸ))
    (f ʷ)
circuits≅cycles = I.Theorem.Theorem-Circuits-iso-Cycles

-- With Lafont's theorem, the circuits modulo the translated relation
-- present 𝔄₁₆.
presentation : (4 CRel,_===_) IsPresentationOf Alt-group 16
presentation = P.presentation

------------------------------------------------------------------------
-- The second step: the translated relation and the rules

-- Each relation set's rules are consequences of the other's,
relations⇒rules : ∀ {w v} → 4 CRel, w === v → ⊢ᴿ w ≈ v
relations⇒rules = E.s⇒t-ax

rules⇒relations : ∀ {w v} → 4 RRel, w === v → ⊢ w ≈ v
rules⇒relations = E.t⇒s-ax

-- so the identity is an isomorphism of the two word groups,
grouplikeᴿ : Grouplike (4 RRel,_===_)
grouplikeᴿ = E.grouplikeᵀ

rules≅relations :
  IsGroupIsomorphism
    (Group.rawGroup (Group-Lemmas.•-ε-group (4 RRel,_===_) grouplikeᴿ))
    (Group.rawGroup (Group-Lemmas.•-ε-group (4 CRel,_===_) grouplike))
    id
rules≅relations = E.rules≅relations

-- and the first step holds for the rules, with the same translations.
rules≅cycles :
  IsGroupIsomorphism
    (Group.rawGroup (Group-Lemmas.•-ε-group (4 RRel,_===_) grouplikeᴿ))
    (Group.rawGroup (Group-Lemmas.•-ε-group _LRel_ grouplikeᴸ))
    (f ʷ)
rules≅cycles = E.Theoremᵀ.Theorem-Rules-iso-Cycles

------------------------------------------------------------------------
-- The presentation of 𝔄₁₆ by the rules

presentationᴿ : (4 RRel,_===_) IsPresentationOf Alt-group 16
presentationᴿ = E.presentationᵀ

-- Circuits equal by the rules are the same function on states, on any
-- number of wires, and on four wires the converse holds,
soundᴿ : ∀ {n} {w v : Circuit n} → ⊢ᴿ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
soundᴿ = Th.T-sound

completeᴿ : ∀ {w v : Circuit 4} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⊢ᴿ w ≈ v
completeᴿ = E.completeᵀ

-- every circuit is equal by the rules to its canonical circuit, and
-- circuits equal by the rules have the same normal form.
normal-formᴿ : (w : Circuit 4) → ⊢ᴿ canon (nf w) ≈ w
normal-formᴿ = E.normal-formᵀ

nf-congᴿ : ∀ {w v : Circuit 4} → ⊢ᴿ w ≈ v → nf w ≡ nf v
nf-congᴿ = E.nf-congᵀ

------------------------------------------------------------------------
-- The translated relation and the functions on states

-- A circuit's permutation carries the position of a state to the
-- position of the state the circuit sends it to.
⟦⟧ᴬ-sem : (w : Circuit 4) (i : Fin 16) →
          perm ⟦ w ⟧ᴬ ⟨$⟩ʳ i ≡ dec (⟦ w ⟧ (enc i))
⟦⟧ᴬ-sem = P.⟦⟧ᴬ-sem

-- Two circuits are equal by the rules exactly when they are the same
-- function.
sound : ∀ {w v : Circuit 4} → ⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound = P.sound

complete : ∀ {w v : Circuit 4} → ⟦ w ⟧ ≐ ⟦ v ⟧ → ⊢ w ≈ v
complete = P.complete

------------------------------------------------------------------------
-- The normal form

-- A canonical circuit is the translation of Lafont's canonical form.
canon-g : (x : NF) → canon x ≡ (g ʷ) (inv-nf x)
canon-g = N.canon-g

-- Every circuit is equal by the rules to its canonical circuit,
normal-form : (w : Circuit 4) → ⊢ canon (nf w) ≈ w
normal-form = N.normal-form

-- which is its own normal form.
nf-canon : (x : NF) → nf (canon x) ≡ x
nf-canon = N.nf-canon

-- Canonical circuits with the same function are the same,
canon-unique : ∀ {x y : NF} → ⟦ canon x ⟧ ≐ ⟦ canon y ⟧ → x ≡ y
canon-unique = N.canon-unique

-- and every even permutation is carried out by one.
canon-onto : (a : Alt 16) → Σ NF (λ x → ⟦ canon x ⟧ᴬ ≈ᴬ a)
canon-onto = N.canon-onto
