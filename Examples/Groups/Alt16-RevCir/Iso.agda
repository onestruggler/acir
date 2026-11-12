------------------------------------------------------------------------
-- Presentations of groups
--
-- The isomorphism between the circuits on four wires modulo the rules
-- of Syntactics and Lafont's words in the cycles on sixteen points
-- modulo his relations: a Reidemeister–Schreier step
--
-- The two rule sets are over different alphabets.  The circuits' are
-- the gates X, CX, CCX and Ex on four wires, with the rules of
-- Syntactics, the laws of the swap and the structural rules
-- (4 VRel,_===_).  Lafont's are the cycles ω₀, …, ω₁₃, with the three
-- relations of his Theorem 4 and the commutations of cycles three or
-- more points apart (the relation of Examples.Groups.Alternating at
-- width 16).  Translation has the translations in both directions: f
-- reads a gate as a word in the cycles, g a cycle as a circuit.  The
-- content is that the two relation sets are equivalent along them:
--
--   f-well-defined : every rule of the circuits, translated by f,
--                    follows from Lafont's relations;
--   g-well-defined : every relation of Lafont's, translated by g,
--                    follows from the circuits' rules;
--   f-left-inv-gen : every cycle is, by Lafont's relations, the word of
--                    its circuit;
--   g-left-inv-gen : every gate is, by the circuits' rules, the circuit
--                    of its word.
--
-- Where the two halves are proved:
--
-- * The half towards the circuits is syntactic (Lemmas).  The rules of
--   Syntactics are Lafont's relations read through g and one rule per
--   gate naming its word, so each instance of his relation goes to one
--   rule (lemma-g-rel), and each gate is the circuit of its word by its
--   rule, or by that of the gate on the bottom wires and the naturality
--   of the swap (lemma-g-f).
--
-- * The half towards Lafont's words is semantic.  A word in the cycles
--   permutes the sixteen positions as its circuit maps the sixteen
--   states, and conversely (Bridge.f-sem, g-sem-gen); the circuits'
--   rules are sound for the functions on states (Semantics.ax-sound);
--   and two words in the cycles with the same permutation are equal by
--   Lafont's relations: the completeness half of his theorem.  So no
--   derivation between the words of the gates, some of a hundred
--   cycles, is written out.
--
-- Presentation.Morphism turns the four facts into the isomorphism: they
-- are the hypotheses of Normalization.Reidemeister-Schreier's simplified
-- step in each direction, which make f ʷ injective and surjective.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Iso where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using ()

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.Morphism as Morphism
open import Word.Base using ([_]ʷ ; _ʷ)

open import Examples.Groups.Alternating.Presentation as LA using ()
import Examples.Groups.Alternating.Syntactics as L

open import Examples.Groups.Alt16-RevCir.Bridge using (f-sem ; g-sem-gen)
open import Examples.Groups.Alt16-RevCir.Lemmas
  using (lemma-g-rel ; lemma-g-f)
open import Examples.Groups.Alt16-RevCir.Numbering using (enc ; dec)
open import Examples.Groups.Alt16-RevCir.Semantics using (ax-sound)
open import Examples.Groups.Alt16-RevCir.Syntactics
open import Examples.Groups.Alt16-RevCir.Translation using (f ; g)

open GroupMorphisms using (IsGroupIsomorphism)

private
  -- Lafont's presentation of 𝔄₁₆; its words are a group by its gl.
  module LP = _IsPresentationOf_ (LA.presentation {16})

  -- The two congruences: the circuits' and Lafont's.
  infix 4 _≈₁_ _≈₂_
  _≈₁_ : Circuit 4 → Circuit 4 → Set
  _≈₁_ = PB._≈_ (4 VRel,_===_)

  _≈₂_ : L.Circuit 16 → L.Circuit 16 → Set
  _≈₂_ = PB._≈_ (L._VRel,_===_ 16)

------------------------------------------------------------------------
-- The isomorphism

module Theorem where

  -- f : circuits → Lafont's words.  A rule of the circuits equates two
  -- circuits with the same function on states, so their words have the
  -- same permutation of the positions, and are equal by completeness.
  f-well-defined : ∀ {w v} → 4 VRel, w === v → (f ʷ) w ≈₂ (f ʷ) v
  f-well-defined {w} {v} r =
    LA.completeness {16} {(f ʷ) w} {(f ʷ) v} λ i →
      Eq.trans (f-sem w i)
      (Eq.trans (Eq.cong dec (ax-sound r (enc i)))
                (Eq.sym (f-sem v i)))

  -- g : Lafont's words → circuits.  Each instance of his relation is
  -- read as a rule of Syntactics.
  g-well-defined : ∀ {u t} → L._VRel,_===_ 16 u t → (g ʷ) u ≈₁ (g ʷ) t
  g-well-defined = lemma-g-rel 0 Eq.refl

  -- A cycle and the word of its circuit have the same permutation.
  f-left-inv-gen : (y : L.Gen 16) → [ y ]ʷ ≈₂ (f ʷ) (g y)
  f-left-inv-gen y =
    LA.completeness {16} {[ y ]ʷ} {(f ʷ) (g y)} λ i →
      Eq.trans (Eq.sym (g-sem-gen y i)) (Eq.sym (f-sem (g y) i))

  g-left-inv-gen : (x : Gen 4) → [ x ]ʷ ≈₁ (g ʷ) (f x)
  g-left-inv-gen = lemma-g-f

  ----------------------------------------------------------------------
  -- Group-likeness of the circuits' rules
  --
  -- Transported rather than reproved: g-well-defined lifts to the whole
  -- congruence, so the inverse of a gate x is the circuit of the
  -- inverse, in Lafont's word group, of the word of x.

  open Morphism (L._VRel,_===_ 16) (4 VRel,_===_)
    using (module Star-Congruence)
  open Star-Congruence g g-well-defined
    using () renaming (fʷ-cong to gʷ-cong)

  grouplike : Grouplike (4 VRel,_===_)
  grouplike x =
    (g ʷ) (f x LP.GL.⁻¹) ,
    PB.trans (PB.cong PB.refl (g-left-inv-gen x))
             (gʷ-cong (LP.GL.inverseˡ {f x}))

  ----------------------------------------------------------------------
  -- The theorem

  private
    module G₁ = Group-Lemmas (4 VRel,_===_) grouplike
    module G₂ = LP.GL

  open Morphism (4 VRel,_===_) (L._VRel,_===_ 16)
    using (module GroupMorphism)
  open GroupMorphism grouplike LP.gl using (module StarGroupIsomorphism)

  Theorem-Circuits-iso-Cycles :
    IsGroupIsomorphism (Group.rawGroup G₁.•-ε-group)
                       (Group.rawGroup G₂.•-ε-group) (f ʷ)
  Theorem-Circuits-iso-Cycles =
    StarGroupIsomorphism.isGroupIsomorphism
      f g f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen
