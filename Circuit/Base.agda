------------------------------------------------------------------------
-- Presentations of groups
--
-- Inductively defined circuits with structural congruence rules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero ; suc ; _+_)

module Circuit.Base (Gate : ℕ → Set) where

open import Level using (0ℓ)
open import Relation.Binary using (Rel)

open import Notations
open import Word.Base
import Presentation.Base as PB

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- Generators and circuits

-- Gen n: a single-step generator on exactly n wires.
-- gate₀ h occupies no wires, so it is available at EVERY width — a
--   global gate, such as a scalar, and the only constructor that
--   inhabits Gen 0.  Being available at every width is not yet the same
--   as being the SAME gate at every width: _↑ still relabels it, and
--   Lift-Relation's ω↑=ω is what identifies the two spellings;
-- gate₁ h acts on the bottom 1 wire of a (₁₊ k)-wire circuit;
-- gate₂ h acts on the bottom 2 wires of a (₂₊ k)-wire circuit.
-- _↥ shifts any generator up by one wire.
--
-- The wire-consuming constructors begin their index with suc (no
-- top-level addition) so Agda's coverage checker can solve unification
-- goals by injectivity of ₁₊ alone, avoiding stuck Diophantine equations
-- of the form arity + k ≟ target.  gate₀ needs no such care: its index is
-- an unconstrained n, which is precisely what makes it width-polymorphic.
--
-- Note for clients: a function defined by cases on Gen owes a gate₀
-- clause, and one defined by cases on Lift-Relation's _VRel,_===_ owes
-- an ω↑=ω clause.  Where Gate 0 is empty — as it is for SympGate — both
-- are the absurd patterns `gate₀ ()` and `ω↑=ω ()`.
data Gen : ℕ → Set where
  gate₀ : Gate 0 → Gen n
  gate₁ : Gate 1 → Gen (₁₊ n)
  gate₂ : Gate 2 → Gen (₂₊ n)
  _↥   : Gen n → Gen (₁₊ n)

Circuit : ℕ → Set
Circuit n = Word (Gen n)

-- A relation on n-wire circuit.
CRel : ℕ → Set₁
CRel n = Rel (Circuit n) 0ℓ

private
  variable
    w v : Circuit n

------------------------------------------------------------------------
-- Structural lift operations


-- Shift a generator up by k wires.
-- Type Gen (k + n) (k on the left) avoids the n + 0 ≢ n issue.
infixl 8 _↥ᵏ_
_↥ᵏ_ : Gen n → (k : ℕ) → Gen (k + n)
g ↥ᵏ zero    = g
g ↥ᵏ ₁₊ k   = (g ↥ᵏ k) ↥

-- Lift a circuit up by k wires.
infixl 7 _↑ᵏ_
_↑ᵏ_ : Circuit n → (k : ℕ) → Circuit (k + n)
w ↑ᵏ k  = wmap (_↥ᵏ k) w

-- Shift all generators up by one wire.
_↑ : Circuit n → Circuit (₁₊ n)
_↑ = _↑ᵏ 1

-- Widen a generator by k extra wires on top, keeping its action on the
-- bottom wires.  Dual to _↥ᵏ_: whereas _↥ᵏ_ inserts wires below and
-- shifts the gate up onto them, _↧ᵏ_ leaves the gate where it is and
-- pads new wires above.  The result type Gen (n + k) puts the new wires
-- on the right, so e.g. Gen 2 embeds into Gen (2 + k) ≡ Gen (₂₊ k).
-- A gate₀ is width-polymorphic already, so widening only re-indexes it.
infixl 8 _↧ᵏ_
_↧ᵏ_ : Gen n → (k : ℕ) → Gen (n + k)
gate₀ h ↧ᵏ k = gate₀ h
gate₁ h ↧ᵏ k = gate₁ h
gate₂ h ↧ᵏ k = gate₂ h
(g ↥)   ↧ᵏ k = (g ↧ᵏ k) ↥

-- Widen a circuit by k extra wires on top (the _↧ᵏ_ map on every gate).
-- In particular _↓ᵏ_ {2} embeds Circuit 2 into Circuit (₂₊ k).
infixl 7 _↓ᵏ_
_↓ᵏ_ : Circuit n → (k : ℕ) → Circuit (n + k)
w ↓ᵏ k = wmap (_↧ᵏ k) w

-- Identity: marks a circuit acting on the bottom wires (notation only).
-- Kept as the identity (not _↓ᵏ 1): downstream code writes `w ↓` to pin a
-- polymorphic gate to the bottom wires, letting the surrounding context
-- fix the wire count by unification — the dual of the genuine shift `_↑`.
_↓ : Circuit n → Circuit n
_↓ x = x

------------------------------------------------------------------------
-- Lift-Relation
--
-- Extends any family of circuit relations (indexed by wire count) with
-- the structural rules shared by ALL circuit presentations:
--
--   cong↑  — equalities are preserved under _↑
--   comm   — an m-ary gate at the bottom commutes with any generator
--            that has been shifted up m wires.  One rule per arity:
--            comm₀, comm₁, comm₂.  At m = 0 there is nothing to shift,
--            so a global gate commutes with every generator outright.
--   ω↑=ω   — a 0-ary gate is the same gate on every wire, so shifting
--            one leaves it unchanged.
--
-- The last two are the price and the payoff of admitting global gates:
-- a 0-ary gate is central (comm₀) and width-independent (ω↑=ω), and both
-- facts are uniform enough to belong here rather than being restated by
-- every presentation that has a scalar.
--
-- Usage: define a group-specific CRel (order relations, braid
-- relations, etc.), then open Lift-Relation CRel to obtain the full
-- relation that includes the structural rules automatically.
module Lift-Relation (_SRel,_===_ : (n : ℕ) → CRel n) where

  infix 4 _VRel,_===_
  data _VRel,_===_ : (n : ℕ) → CRel n where

    -- Embed the group-specific relation.
    srel  : n SRel, w === v → n VRel, w === v

    -- Structural: congruence under wire-shifting.
    cong↑ : n VRel, w === v → (₁₊ n) VRel, w ↑ === v ↑

    -- Structural: a gate at the bottom commutes with any generator
    -- that has been shifted up past it.
    --
    -- comm₀: a 0-ary gate holds no wires, so it commutes with EVERY
    --        generator at the same width, with no shift on either side.
    -- comm₁: a 1-ary gate at wire 0 commutes with g shifted up 1 wire.
    -- comm₂: a 2-ary gate at wires 0-1 commutes with g shifted up 2 wires.
    comm₀ : (h : Gate 0) (g : Gen n) → n VRel,
      [ g ]ʷ • [ gate₀ h ]ʷ === [ gate₀ h ]ʷ • [ g ]ʷ
    comm₁ : (h : Gate 1) (g : Gen n) → (₁₊ n) VRel,
      [ g ↥ ]ʷ • [ gate₁ h ]ʷ === [ gate₁ h ]ʷ • [ g ↥ ]ʷ
    comm₂ : (h : Gate 2) (g : Gen n) → (₂₊ n) VRel,
      [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ === [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ

    -- Structural: a global gate does not depend on the wire it is
    -- written on.
    --
    -- gate₀ is width-polymorphic, but _↑ is a wmap and relabels it all
    -- the same: at width ₁₊ n the shift of gate₀ ω is (gate₀ ω) ↥, a
    -- term distinct from the gate₀ ω that already lives at that width.
    -- This rule identifies the two, so that one 0-ary gate is one
    -- generator and not one generator per wire-depth.
    --
    -- It does not follow from cong↑, which carries an equation from one
    -- width to the next but cannot relate w ↑ to w at the SAME width.
    -- Nor is there an analogue at the wire-consuming arities: gate₁ h
    -- and (gate₁ h) ↥ act on different wires and must stay apart — which
    -- is why this is the only rule of its shape.
    --
    -- Presentations with a global gate used to state this for
    -- themselves; Selinger's Figure 8 carried it as cω↑.
    ω↑=ω : (ω : Gate 0) → (₁₊ n) VRel, [ gate₀ ω ]ʷ ↑ === [ gate₀ ω ]ʷ

  -- The monoid congruence at wire count n lifts to wire count ₁₊ n.
  lemma-cong↑ : ∀ {n} (w v : Circuit n)
    → let open PB (_VRel,_===_ n)       using (_≈_)
          open PB (_VRel,_===_ (₁₊ n)) renaming (_≈_ to _≈↑_) using ()
      in w ≈ v → w ↑ ≈↑ v ↑
  lemma-cong↑ w v PB.refl              = PB.refl
  lemma-cong↑ w v (PB.sym eq)          = PB.sym (lemma-cong↑ v w eq)
  lemma-cong↑ w v (PB.trans eq eq₁)   = PB.trans (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v (PB.cong eq eq₁)    = PB.cong  (lemma-cong↑ _ _ eq) (lemma-cong↑ _ _ eq₁)
  lemma-cong↑ w v PB.assoc            = PB.assoc
  lemma-cong↑ w v PB.left-unit        = PB.left-unit
  lemma-cong↑ w v PB.right-unit       = PB.right-unit
  lemma-cong↑ w v (PB.axiom x)        = PB.axiom (cong↑ x)
