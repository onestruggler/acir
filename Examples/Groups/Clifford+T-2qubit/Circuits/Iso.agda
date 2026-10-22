------------------------------------------------------------------------
-- Presentations of groups
--
-- On two wires, the circuit presentation (Circuits.Syntactics) and
-- Bian and Selinger's (Generator) present the same group
--
-- ι reads a circuit letter as the paper's letter for that gate on that
-- qubit (wire 0 is qubit 1, wire 1 qubit 0), and κ goes back.  Every
-- rule of either side is a rule, or an instance of (a), of the other
-- — the structural rules of Circuit.Base are the paper's monoidal
-- relations (a), and a one-qubit rule on wire 1 is the paper's
-- relation for qubit 0 — and κ undoes ι up to ω↑=ω, so (ι ʷ) is a
-- group isomorphism of the presented groups.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Circuits.Iso where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)

open import Examples.Groups.Clifford+T-2qubit.Circuits.Syntactics
open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
open import Examples.Groups.Clifford+T-2qubit.CliffordT-Lemmas using (module Clifford+T-Data)

private
  module P = Clifford+T

open P using (Generator ; Rel)

private
  variable
    w v : Circuit 2

  _⊢ᴾ_≈_ : (Γ : Word Generator → Word Generator → Set) → Word Generator → Word Generator → Set
  Γ ⊢ᴾ w ≈ v = PB._≈_ Γ w v

------------------------------------------------------------------------
-- The two translations

-- A letter on wire 1, as a letter of qubit 0.
ιᵗ : Gen 1 → Word Generator
ιᵗ ω-gen      = P.W
ιᵗ H-gen      = P.H0
ιᵗ S-gen      = P.S0
ιᵗ T-gen      = P.T0
ιᵗ (ω-gen ↥)  = P.W

-- A letter on two wires.
ι : Gen 2 → Word Generator
ι ω-gen   = P.W
ι H-gen   = P.H1
ι S-gen   = P.S1
ι T-gen   = P.T1
ι CZ-gen  = P.CZ
ι (g ↥)   = ιᵗ g

κ : Generator → Word (Gen 2)
κ P.W-gen  = ω
κ P.H0-gen = H ↑
κ P.H1-gen = H
κ P.S0-gen = S ↑
κ P.S1-gen = S
κ P.T0-gen = T ↑
κ P.T1-gen = T
κ P.CZ-gen = CZ

ι-↑ : (u : Circuit 1) → (ι ʷ) (u ↑) ≡ (ιᵗ ʷ) u
ι-↑ [ g ]ʷ  = Eq.refl
ι-↑ ε       = Eq.refl
ι-↑ (u • t) = Eq.cong₂ _•_ (ι-↑ u) (ι-↑ t)

------------------------------------------------------------------------
-- The circuit rules hold in the paper's presentation

private
  ιᵗ-ax : ∀ {w v : Circuit 1} → 1 VRel, w === v → Rel ⊢ᴾ (ιᵗ ʷ) w ≈ (ιᵗ ʷ) v
  ιᵗ-ax (srel order-ω)            = PB.axiom P.order-W
  ιᵗ-ax (srel order-H)            = PB.axiom P.order-H0
  ιᵗ-ax (srel order-S)            = PB.axiom P.order-S0
  ιᵗ-ax (srel order-SH)           = PB.axiom P.order-S0H0
  ιᵗ-ax (srel square-T)           = PB.axiom P.square-T0
  ιᵗ-ax (srel order-TX)           = PB.axiom P.lemma-order-T0X0
  ιᵗ-ax (cong↑ (srel order-ω))    = PB.axiom P.order-W
  ιᵗ-ax (comm₁ H-gate ω-gen)      = PB.axiom (P.comm-W P.H0-gen)
  ιᵗ-ax (comm₁ S-gate ω-gen)      = PB.axiom (P.comm-W P.S0-gen)
  ιᵗ-ax (comm₁ T-gate ω-gen)      = PB.axiom (P.comm-W P.T0-gen)
  ιᵗ-ax (ω↑=ω ω-gate)             = PB.refl

ι-ax : 2 VRel, w === v → Rel ⊢ᴾ (ι ʷ) w ≈ (ι ʷ) v
ι-ax (srel order-ω)          = PB.axiom P.order-W
ι-ax (srel order-H)          = PB.axiom P.order-H1
ι-ax (srel order-S)          = PB.axiom P.order-S1
ι-ax (srel order-SH)         = PB.axiom P.order-S1H1
ι-ax (srel order-CZ)         = PB.axiom P.order-CZ
ι-ax (srel comm-S0-CZ)       = PB.axiom P.comm-S0-CZ
ι-ax (srel comm-S1-CZ)       = PB.axiom P.comm-S1-CZ
ι-ax (srel rel-X0-CZ)        = PB.axiom P.rel-X0-CZ
ι-ax (srel rel-X1-CZ)        = PB.axiom P.rel-X1-CZ
ι-ax (srel rel-CZ-H0-CZ)     = PB.axiom P.rel-CZ-H0-CZ
ι-ax (srel rel-CZ-H1-CZ)     = PB.axiom P.rel-CZ-H1-CZ
ι-ax (srel square-T)         = PB.axiom P.square-T1
ι-ax (srel order-TX)         = PB.axiom P.lemma-order-T1X1
ι-ax (srel comm-T0-CZ)       = PB.axiom P.comm-T0-CZ
ι-ax (srel swap-T0)          = PB.axiom P.swap-T0
ι-ax (srel rel-A)            = PB.axiom P.rel-A
ι-ax (srel rel-B)            = PB.axiom P.rel-B
ι-ax (srel rel-C)            = PB.axiom P.rel-C
ι-ax (cong↑ {w = w} {v} r)   =
  Eq.subst₂ (Rel ⊢ᴾ_≈_) (Eq.sym (ι-↑ w)) (Eq.sym (ι-↑ v)) (ιᵗ-ax r)
ι-ax (comm₁ H-gate ω-gen)        = PB.axiom (P.comm-W P.H1-gen)
ι-ax (comm₁ S-gate ω-gen)        = PB.axiom (P.comm-W P.S1-gen)
ι-ax (comm₁ T-gate ω-gen)        = PB.axiom (P.comm-W P.T1-gen)
ι-ax (comm₁ H-gate (ω-gen ↥))    = PB.axiom (P.comm-W P.H1-gen)
ι-ax (comm₁ S-gate (ω-gen ↥))    = PB.axiom (P.comm-W P.S1-gen)
ι-ax (comm₁ T-gate (ω-gen ↥))    = PB.axiom (P.comm-W P.T1-gen)
ι-ax (comm₁ H-gate H-gen)        = PB.axiom P.comm-H0-H1
ι-ax (comm₁ H-gate S-gen)        = PB.axiom P.comm-S0-H1
ι-ax (comm₁ H-gate T-gen)        = PB.axiom P.comm-T0-H1
ι-ax (comm₁ S-gate H-gen)        = PB.axiom P.comm-H0-S1
ι-ax (comm₁ S-gate S-gen)        = PB.axiom P.comm-S0-S1
ι-ax (comm₁ S-gate T-gen)        = PB.axiom P.comm-T0-S1
ι-ax (comm₁ T-gate H-gen)        = PB.axiom P.comm-H0-T1
ι-ax (comm₁ T-gate S-gen)        = PB.axiom P.comm-S0-T1
ι-ax (comm₁ T-gate T-gen)        = PB.axiom P.comm-T0-T1
ι-ax (comm₂ CZ-gate ω-gen)       = PB.axiom (P.comm-W P.CZ-gen)
ι-ax (ω↑=ω ω-gate)               = PB.refl

------------------------------------------------------------------------
-- The paper's relations hold for circuits

κ-ax : ∀ {u t} → Rel u t → 2 ⊢ (κ ʷ) u ≈ (κ ʷ) t
κ-ax (P.comm-W g)        = PB.sym (comm-gate₀-w ω-gate (κ g))
κ-ax P.comm-H0-H1        = PB.axiom (comm₁ H-gate H-gen)
κ-ax P.comm-H0-S1        = PB.axiom (comm₁ S-gate H-gen)
κ-ax P.comm-H0-T1        = PB.axiom (comm₁ T-gate H-gen)
κ-ax P.comm-S0-H1        = PB.axiom (comm₁ H-gate S-gen)
κ-ax P.comm-S0-S1        = PB.axiom (comm₁ S-gate S-gen)
κ-ax P.comm-S0-T1        = PB.axiom (comm₁ T-gate S-gen)
κ-ax P.comm-T0-H1        = PB.axiom (comm₁ H-gate T-gen)
κ-ax P.comm-T0-S1        = PB.axiom (comm₁ S-gate T-gen)
κ-ax P.comm-T0-T1        = PB.axiom (comm₁ T-gate T-gen)
κ-ax P.order-W           = PB.axiom (srel order-ω)
κ-ax P.order-H0          = PB.axiom (cong↑ (srel order-H))
κ-ax P.order-H1          = PB.axiom (srel order-H)
κ-ax P.order-S0          = PB.axiom (cong↑ (srel order-S))
κ-ax P.order-S1          = PB.axiom (srel order-S)
κ-ax P.order-S0H0        = PB.trans (PB.axiom (cong↑ (srel order-SH))) (PB.axiom (ω↑=ω ω-gate))
κ-ax P.order-S1H1        = PB.axiom (srel order-SH)
κ-ax P.order-CZ          = PB.axiom (srel order-CZ)
κ-ax P.comm-S0-CZ        = PB.axiom (srel comm-S0-CZ)
κ-ax P.comm-S1-CZ        = PB.axiom (srel comm-S1-CZ)
κ-ax P.rel-X0-CZ         = PB.axiom (srel rel-X0-CZ)
κ-ax P.rel-X1-CZ         = PB.axiom (srel rel-X1-CZ)
κ-ax P.rel-CZ-H0-CZ      = PB.axiom (srel rel-CZ-H0-CZ)
κ-ax P.rel-CZ-H1-CZ      = PB.axiom (srel rel-CZ-H1-CZ)
κ-ax P.square-T0         = PB.axiom (cong↑ (srel square-T))
κ-ax P.square-T1         = PB.axiom (srel square-T)
κ-ax P.lemma-order-T0X0  = PB.trans (PB.axiom (cong↑ (srel order-TX))) (PB.axiom (ω↑=ω ω-gate))
κ-ax P.lemma-order-T1X1  = PB.axiom (srel order-TX)
κ-ax P.comm-T0-CZ        = PB.axiom (srel comm-T0-CZ)
κ-ax P.swap-T0           = PB.axiom (srel swap-T0)
κ-ax P.rel-A             = PB.axiom (srel rel-A)
κ-ax P.rel-B             = PB.axiom (srel rel-B)
κ-ax P.rel-C             = PB.axiom (srel rel-C)

------------------------------------------------------------------------
-- κ and ι are inverse on letters

ικ : ∀ (x : Generator) → Rel ⊢ᴾ [ x ]ʷ ≈ (ι ʷ) (κ x)
ικ P.W-gen  = PB.refl
ικ P.H0-gen = PB.refl
ικ P.H1-gen = PB.refl
ικ P.S0-gen = PB.refl
ικ P.S1-gen = PB.refl
ικ P.T0-gen = PB.refl
ικ P.T1-gen = PB.refl
ικ P.CZ-gen = PB.refl

κι : ∀ (x : Gen 2) → 2 ⊢ [ x ]ʷ ≈ (κ ʷ) (ι x)
κι ω-gen          = PB.refl
κι H-gen          = PB.refl
κι S-gen          = PB.refl
κι T-gen          = PB.refl
κι CZ-gen         = PB.refl
κι (ω-gen ↥)      = PB.axiom (ω↑=ω ω-gate)
κι (H-gen ↥)      = PB.refl
κι (S-gen ↥)      = PB.refl
κι (T-gen ↥)      = PB.refl
κι ((ω-gen ↥) ↥)  = PB.trans (PB.axiom (cong↑ (ω↑=ω ω-gate))) (PB.axiom (ω↑=ω ω-gate))

------------------------------------------------------------------------
-- So (ι ʷ) is a group isomorphism

private
  module GC = Group-Lemmas (2 VRel,_===_) (grouplike {2})
  module GP = Group-Lemmas Rel Clifford+T-Data.group-like

open import Presentation.Morphism (2 VRel,_===_) Rel using (module GroupMorphism)
open GroupMorphism (grouplike {2}) Clifford+T-Data.group-like using (module StarGroupIsomorphism)

circuits≅paper : GroupMorphisms.IsGroupIsomorphism
                   (Group.rawGroup GC.•-ε-group) (Group.rawGroup GP.•-ε-group) (ι ʷ)
circuits≅paper = StarGroupIsomorphism.isGroupIsomorphism ι κ ι-ax ικ κ-ax κι
