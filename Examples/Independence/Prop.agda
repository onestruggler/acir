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
-- A fragment (Section 3) is given by its axioms: for each name r an
-- arity and the two sides, circuits on that many wires.  The axiom
-- holds on the bottom wires of every wider circuit (ax r k), and
-- Lift-Relation's cong↑ moves it up.  Circuit.Prop's Lift-To-Prop adds
-- the swap rules to them: an axiom instance is srel (srel (ax r k)),
-- a swap rule srel (σrel s).  The swap rules are structural, and a
-- selection never removes one.
--
-- Independence of an axiom ρ (Definition 23) is that of
-- Presentation.Independence at the selection Without ρ of every axiom
-- instance not using ρ.  Every generator has as many outputs as
-- inputs (Remark 14), so a derivation between n-wire circuits uses
-- only axioms of arity at most n (truncate): an n-wire axiom can be
-- tested inside the subsystem of arity at most n, which is what the
-- paper's bounded separators rely on (Section 5.1).  Keep ρ b is that
-- subsystem, without ρ.
--
-- Wire 0 is the bottom wire, the paper's last.  Words are in diagram
-- order: w • v is w followed by v, as the paper's figures read.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Independence.Prop (Gate : ℕ → Set) where

open import Data.Empty using (⊥)
open import Data.Nat using (_+_ ; _≤_)
open import Data.Nat.Properties using (≤-trans ; m≤m+n ; n≤1+n ; +-identityʳ)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Negation using (¬_)

open import Notations
open import Word.Base using ([_]ʷ ; ε ; _•_)
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
-- A fragment: named axioms, each with an arity and two sides

module Fragment
  {Rule : Set} (arity : Rule → ℕ)
  (lhs rhs : (r : Rule) → Circuit (arity r))
  where

  infix 4 _SRel,_===_
  data _SRel,_===_ : (n : ℕ) → CRel n where
    ax : (r : Rule) (k : ℕ) →
         (arity r + k) SRel, lhs r ↓ᵏ k === rhs r ↓ᵏ k

  -- The swap rules and the structural rules on top; n ⊢ w ≈ v is
  -- derivability at width n.
  open Lift-To-Prop _SRel,_===_ public

  ----------------------------------------------------------------------
  -- Selections

  -- Uses ρ a: the axiom ρ occurs in the instance a.  Removing ρ
  -- removes its shifts as well.
  Uses : Rule → n VRel, w === v → Set
  Uses ρ (srel (σrel _))  = ⊥
  Uses ρ (srel (srel (ax r _))) = r ≡ ρ
  Uses ρ (cong↑ a)       = Uses ρ a
  Uses ρ (comm₁ _ _)     = ⊥
  Uses ρ (comm₂ _ _)     = ⊥
  Uses ρ (comm₃ _ _)     = ⊥
  Uses ρ (ω↑=ω _)        = ⊥

  -- Every axiom instance not using ρ: "the other axioms".
  Without : Rule → Select (n VRel,_===_)
  Without ρ a = ¬ Uses ρ a

  -- Within b a: every axiom of the fragment occurring in a has arity
  -- at most b.
  Within : ℕ → n VRel, w === v → Set
  Within b (srel (σrel _))  = ⊤
  Within b (srel (srel (ax r _))) = arity r ≤ b
  Within b (cong↑ a)       = Within b a
  Within b (comm₁ _ _)     = ⊤
  Within b (comm₂ _ _)     = ⊤
  Within b (comm₃ _ _)     = ⊤
  Within b (ω↑=ω _)        = ⊤

  -- The other axioms of arity at most b (C_{•,b} \ {ρ}, Definition 24).
  Keep : Rule → ℕ → Select (n VRel,_===_)
  Keep ρ b a = Without ρ a × Within b a

  Within-mono : ∀ {b b'} → b ≤ b' → (a : n VRel, w === v) →
                Within b a → Within b' a
  Within-mono b≤b' (srel (σrel _))  _ = tt
  Within-mono b≤b' (srel (srel (ax r _))) p = ≤-trans p b≤b'
  Within-mono b≤b' (cong↑ a)       p = Within-mono b≤b' a p
  Within-mono b≤b' (comm₁ _ _)     _ = tt
  Within-mono b≤b' (comm₂ _ _)     _ = tt
  Within-mono b≤b' (comm₃ _ _)     _ = tt
  Within-mono b≤b' (ω↑=ω _)        _ = tt

  -- Remark 14: an instance at width n has arity at most n.
  within : (a : n VRel, w === v) → Within n a
  within (srel (σrel _))  = tt
  within (srel (srel (ax r k))) = m≤m+n (arity r) k
  within (cong↑ a)       = Within-mono (n≤1+n _) a (within a)
  within (comm₁ _ _)     = tt
  within (comm₂ _ _)     = tt
  within (comm₃ _ _)     = tt
  within (ω↑=ω _)        = tt

  -- So a derivation at width n ≤ b from the other axioms is one from
  -- the other axioms of arity at most b.
  truncate : ∀ {ρ b} → n ≤ b →
             let open PB ((n VRel,_===_) ∣ Without ρ) using (_≈_)
                 open PB ((n VRel,_===_) ∣ Keep ρ b) using ()
                   renaming (_≈_ to _≈ₖ_)
             in w ≈ v → w ≈ₖ v
  truncate {n} n≤b =
    ≈-mono (n VRel,_===_) (λ {_} {_} {a} p → p , Within-mono n≤b a (within a))

  ----------------------------------------------------------------------
  -- Independence and minimality (Definitions 23 and 24)

  -- The axiom ρ, at its own arity, is not derivable from the others.
  Independent-axiom : Rule → Set
  Independent-axiom ρ =
    Independent ((arity ρ + 0) VRel,_===_) (Without ρ) (srel (srel (ax ρ 0)))

  -- So is it from the others of arity at most b; for b at least the
  -- arity of ρ, the two say the same (truncate).
  Independent-axiom-upto : ℕ → Rule → Set
  Independent-axiom-upto b ρ =
    Independent ((arity ρ + 0) VRel,_===_) (Keep ρ b) (srel (srel (ax ρ 0)))

  upto⇒independent : ∀ {ρ b} → arity ρ ≤ b →
                     Independent-axiom-upto b ρ → Independent-axiom ρ
  upto⇒independent {ρ} ar≤b ind d =
    ind (truncate (Eq.subst (_≤ _) (Eq.sym (+-identityʳ (arity ρ))) ar≤b) d)

  -- Every axiom is independent.
  Minimal : Set
  Minimal = ∀ ρ → Independent-axiom ρ

  -- Every axiom of arity at most b is independent (of all the others:
  -- by truncate, this is Definition 24's independence relative to the
  -- axioms of arity at most b).
  Minimal-upto : ℕ → Set
  Minimal-upto b = ∀ ρ → arity ρ ≤ b → Independent-axiom ρ
