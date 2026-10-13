------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits in a PROP, and the axioms of a circuit fragment
--
-- Blake, "Simpler presentations for many fragments of quantum
-- circuits" (FSCD 2026, arXiv:2602.09874), presents six fragments in
-- PROPs, where wire permutations are structural and a rule set lists
-- only the equations specific to its fragment.  Circuit.Base is a PRO:
-- gates sit on the bottom wires and are shifted up, gates on disjoint
-- wires commute, and a 0-ary gate is the same on every wire.  The
-- symmetry is added here as one more two-wire generator, the swap,
-- beside the fragment's gates, and Circuit.Prop supplies the rules
-- that make the PRO a PROP (Definition 2): σ is an involution and is
-- natural in every generator (σ-inv, σ-nat₁, σ-nat₂, σ-nat₃) — σ-nat₂
-- at σ itself is the Yang–Baxter equation.  With Circuit.Base's rules
-- these present the free PROP on the fragment's gates.
--
-- A fragment (Section 3) is given by its axioms, a relation
-- _SRel,_===_ with one constructor for each, between circuits on its
-- own wires: n SRel, w === v says the axiom has arity n.  The fragment
-- opens Circuit.Prop's Lift-To-Prop over it, which adds the swap rules
-- and the structural ones: an axiom instance is srel (srel a), a swap
-- rule srel (σrel s).  Lift-Relation's cong↑ moves an axiom up and the
-- symmetry moves it down, so it holds on the bottom wires of every
-- wider circuit too (Circuit.Prop's pad).
--
-- Independence of an axiom ρ (Definition 23) is that of
-- Presentation.Independence at the selection Without ρ of every axiom
-- instance other than ρ (Axioms, over the fragment's relation): the
-- axioms are the constructors themselves, so there is nothing to name
-- them by.  Every generator has as many outputs as inputs (Remark 14),
-- so a derivation between n-wire circuits uses only axioms of arity at
-- most n (truncate): an n-wire axiom can be tested inside the
-- subsystem of arity at most n, which is what the paper's bounded
-- separators rely on (Section 5.1).  Keep ρ b is that subsystem,
-- without ρ.  The swap rules are structural, and a selection never
-- removes one.
--
-- Wire 0 is the bottom wire, the paper's last.  Words are in diagram
-- order: w • v is w followed by v, as the paper's figures read.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Independence.Prop (Gate : ℕ → Set) where

open import Data.Empty using (⊥)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Negation using (¬_)

import Presentation.Base as PB
open import Presentation.Independence

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates and the swap

data PGate : ℕ → Set where
  ⌈_⌉  : Gate n → PGate n
  swap : PGate 2

-- The swap σ, its cycles σ[ k ], and the symmetry rules _Sym,_===_:
-- read in diagram order, a k-wire gate on wires 0 … k − 1 followed by
-- σ[ k ] (wire k moved down to wire 0) is σ[ k ] followed by the gate
-- on wires 1 … k.  A 0-ary gate needs no naturality: ω↑=ω of
-- Circuit.Base already makes it central.
open import Circuit.Prop PGate swap public

private
  variable
    w v : Circuit n

------------------------------------------------------------------------
-- The axioms of a fragment, one at a time

module Axioms (_SRel,_===_ : (n : ℕ) → CRel n) where

  open Lift-To-Prop _SRel,_===_

  private
    variable
      m : ℕ
      w′ v′ : Circuit m

  -- The axioms as one type, so that two can be compared whatever their
  -- arities and sides.
  data Axiom : Set where
    ⟨_⟩ : n SRel, w === v → Axiom

  ----------------------------------------------------------------------
  -- Selections

  -- Uses ρ a: the axiom ρ occurs in the instance a.  Removing ρ
  -- removes its shifts as well.
  Uses : m SRel, w′ === v′ → n VRel, w === v → Set
  Uses ρ (srel (σrel _)) = ⊥
  Uses ρ (srel (srel a)) = ⟨ a ⟩ ≡ ⟨ ρ ⟩
  Uses ρ (cong↑ a)       = Uses ρ a
  Uses ρ (comm₁ _ _)     = ⊥
  Uses ρ (comm₂ _ _)     = ⊥
  Uses ρ (comm₃ _ _)     = ⊥
  Uses ρ (ω↑=ω _)        = ⊥

  -- Every axiom instance not using ρ: "the other axioms".
  Without : m SRel, w′ === v′ → Select (n VRel,_===_)
  Without ρ a = ¬ Uses ρ a

  -- Within b a: every axiom occurring in a has arity at most b.
  Within : ℕ → n VRel, w === v → Set
  Within     b (srel (σrel _)) = ⊤
  Within {n} b (srel (srel _)) = n ≤ b
  Within     b (cong↑ a)       = Within b a
  Within     b (comm₁ _ _)     = ⊤
  Within     b (comm₂ _ _)     = ⊤
  Within     b (comm₃ _ _)     = ⊤
  Within     b (ω↑=ω _)        = ⊤

  -- The other axioms of arity at most b (C_{•,b} \ {ρ}, Definition 24).
  Keep : m SRel, w′ === v′ → ℕ → Select (n VRel,_===_)
  Keep ρ b a = Without ρ a × Within b a

  Within-mono : ∀ {b b'} → b ≤ b' → (a : n VRel, w === v) →
                Within b a → Within b' a
  Within-mono b≤b' (srel (σrel _)) _ = tt
  Within-mono b≤b' (srel (srel _)) p = ≤-trans p b≤b'
  Within-mono b≤b' (cong↑ a)       p = Within-mono b≤b' a p
  Within-mono b≤b' (comm₁ _ _)     _ = tt
  Within-mono b≤b' (comm₂ _ _)     _ = tt
  Within-mono b≤b' (comm₃ _ _)     _ = tt
  Within-mono b≤b' (ω↑=ω _)        _ = tt

  -- Remark 14: an instance at width n has arity at most n.
  within : (a : n VRel, w === v) → Within n a
  within (srel (σrel _)) = tt
  within (srel (srel _)) = ≤-refl
  within (cong↑ a)       = Within-mono (n≤1+n _) a (within a)
  within (comm₁ _ _)     = tt
  within (comm₂ _ _)     = tt
  within (comm₃ _ _)     = tt
  within (ω↑=ω _)        = tt

  -- So a derivation at width n ≤ b from the other axioms is one from
  -- the other axioms of arity at most b.
  truncate : ∀ {ρ : m SRel, w′ === v′} {b} → n ≤ b →
             let open PB ((n VRel,_===_) ∣ Without ρ) using (_≈_)
                 open PB ((n VRel,_===_) ∣ Keep ρ b) using ()
                   renaming (_≈_ to _≈ₖ_)
             in w ≈ v → w ≈ₖ v
  truncate {n = n} n≤b =
    ≈-mono (n VRel,_===_) (λ {_} {_} {a} p → p , Within-mono n≤b a (within a))

  ----------------------------------------------------------------------
  -- Independence and minimality (Definitions 23 and 24)

  -- The axiom ρ, on its own wires, is not derivable from the others.
  Independent-axiom : n SRel, w === v → Set
  Independent-axiom {n} ρ =
    Independent (n VRel,_===_) (Without ρ) (srel (srel ρ))

  -- So is it from the others of arity at most b; for b at least the
  -- arity of ρ, the two say the same (truncate).
  Independent-axiom-upto : ℕ → n SRel, w === v → Set
  Independent-axiom-upto {n} b ρ =
    Independent (n VRel,_===_) (Keep ρ b) (srel (srel ρ))

  upto⇒independent : ∀ {ρ : n SRel, w === v} {b} → n ≤ b →
                     Independent-axiom-upto b ρ → Independent-axiom ρ
  upto⇒independent n≤b ind d = ind (truncate n≤b d)

  -- Every axiom is independent.
  Minimal : Set
  Minimal = ∀ {n} {w v : Circuit n} (ρ : n SRel, w === v) → Independent-axiom ρ

  -- Every axiom of arity at most b is independent (of all the others:
  -- by truncate, this is Definition 24's independence relative to the
  -- axioms of arity at most b).
  Minimal-upto : ℕ → Set
  Minimal-upto b =
    ∀ {n} {w v : Circuit n} (ρ : n SRel, w === v) → n ≤ b → Independent-axiom ρ
