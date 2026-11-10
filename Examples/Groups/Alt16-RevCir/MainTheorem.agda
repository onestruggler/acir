------------------------------------------------------------------------
-- Presentations of groups
--
-- The alternating group 𝔄₁₆ as reversible circuits on four wires over
-- X, CX, CCX and Ex: the main theorem
--
-- The circuits on four wires over NOT, CNOT, Toffoli and the swap,
-- modulo the rules of Syntactics, are a presentation of the even
-- permutations of the sixteen states.  It is obtained from Lafont's
-- presentation of 𝔄₁₆ by the cycles ω₀, …, ω₁₃
-- (Examples.Groups.Alternating) by a Reidemeister–Schreier step: the
-- generators are translated in both directions (f reads a gate as a
-- word in the cycles, g a cycle as a circuit), each translation
-- carries the relations of its source to consequences of those of its
-- target, and the two are inverse on generators, so the two word
-- groups are isomorphic.  The rules are sound and complete for the
-- functions on states, and every circuit is equal to a unique
-- canonical circuit, the translation of Lafont's canonical form.
--
-- This module collects the statements behind one import: the circuits
-- and their rules (_CRel,_===_), derivability ⊢_≈_, a circuit's
-- function ⟦_⟧ with pointwise equality _≐_ and its even permutation
-- ⟦_⟧ᴬ, the numbering enc, dec of the states, and the theorems.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.MainTheorem where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Product using (Σ)
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
import Examples.Groups.Alt16-RevCir.Iso as I
import Examples.Groups.Alt16-RevCir.NormalForm as N
import Examples.Groups.Alt16-RevCir.Presentation as P
import Examples.Groups.Alt16-RevCir.Semantics as Sem

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

-- A circuit's function on the states of the four wires,
⟦_⟧ : Circuit 4 → Bits 4 → Bits 4
⟦_⟧ = Sem.⟦_⟧

-- and its even permutation of the sixteen positions: that of its word
-- in the cycles.
⟦_⟧ᴬ : Circuit 4 → Alt 16
⟦_⟧ᴬ = P.⟦_⟧ᴬ

------------------------------------------------------------------------
-- The Reidemeister–Schreier step

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

------------------------------------------------------------------------
-- The presentation of 𝔄₁₆

presentation : (4 CRel,_===_) IsPresentationOf Alt-group 16
presentation = P.presentation

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
