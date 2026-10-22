------------------------------------------------------------------------
-- Presentations of groups
--
-- On three wires, the circuit presentation (Circuits.Syntactics) and
-- Bian and Selinger's (Theorem.CliffordCS) present the same group
--
-- ι reads a circuit letter as the paper's letter for that gate on
-- those qubits (wire 0 is qubit 2, wire 2 qubit 0), and κ goes back.
-- Every rule of either side is a rule, or a structural commutation, of
-- the other.  A rule lifted by cong↑ carries its scalar iI to iI ↑,
-- where the paper writes iI, so κ meets the paper's rules up to the
-- scalars' wires: flat moves every scalar to no wire, and flat-≈ says
-- that changes nothing (ω↑=ω).  So (ι ʷ) is a group isomorphism of the
-- presented groups.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-3qubit.Circuits.Iso where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)

open import Notations using (₁₊)
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)

open import Examples.Groups.Clifford+CS-3qubit.Circuits.Syntactics
open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
open import Examples.Groups.Clifford+CS-3qubit.Presentation using (group-like)

private
  module P = CliffordCS

open P using (Rel) renaming (Gen to PGen)

private
  variable
    n : ℕ
    w v : Circuit 3

  _⊢ᴾ_≈_ : (Γ : Word PGen → Word PGen → Set) → Word PGen → Word PGen → Set
  Γ ⊢ᴾ w ≈ v = PB._≈_ Γ w v

------------------------------------------------------------------------
-- The two translations

-- A letter on wire 2 (qubit 0), on wires 1–2 (qubits 1, 0), and on
-- wires 0–2.
ι₁ : Gen 1 → Word PGen
ι₁ iI-gen       = P.iI
ι₁ S-gen        = P.S0
ι₁ K-gen        = P.K0
ι₁ (iI-gen ↥)   = P.iI

ι₂ : Gen 2 → Word PGen
ι₂ iI-gen  = P.iI
ι₂ S-gen   = P.S1
ι₂ K-gen   = P.K1
ι₂ CS-gen  = P.CS01
ι₂ (g ↥)   = ι₁ g

ι : Gen 3 → Word PGen
ι iI-gen  = P.iI
ι S-gen   = P.S2
ι K-gen   = P.K2
ι CS-gen  = P.CS12
ι (g ↥)   = ι₂ g

κ : PGen → Word (Gen 3)
κ P.iI-gen   = iI
κ P.S0-gen   = S ↑ ↑
κ P.S1-gen   = S ↑
κ P.S2-gen   = S
κ P.K0-gen   = K ↑ ↑
κ P.K1-gen   = K ↑
κ P.K2-gen   = K
κ P.CS01-gen = CS ↑
κ P.CS12-gen = CS

ι-↑ : (u : Circuit 2) → (ι ʷ) (u ↑) ≡ (ι₂ ʷ) u
ι-↑ [ g ]ʷ  = Eq.refl
ι-↑ ε       = Eq.refl
ι-↑ (u • t) = Eq.cong₂ _•_ (ι-↑ u) (ι-↑ t)

ι₂-↑ : (u : Circuit 1) → (ι₂ ʷ) (u ↑) ≡ (ι₁ ʷ) u
ι₂-↑ [ g ]ʷ  = Eq.refl
ι₂-↑ ε       = Eq.refl
ι₂-↑ (u • t) = Eq.cong₂ _•_ (ι₂-↑ u) (ι₂-↑ t)

------------------------------------------------------------------------
-- Scalars on no wire

-- A letter shifted up, with a scalar left where it is.
up : Gen n → Gen (₁₊ n)
up iI-gen   = iI-gen
up S-gen    = S-gen ↥
up K-gen    = K-gen ↥
up CS-gen   = CS-gen ↥
up (g ↥)    = g ↥ ↥

flatg : Gen n → Gen n
flatg iI-gen  = iI-gen
flatg S-gen   = S-gen
flatg K-gen   = K-gen
flatg CS-gen  = CS-gen
flatg (g ↥)   = up (flatg g)

flat : Circuit n → Circuit n
flat = wmap flatg

private
  up-≈ : (g : Gen n) → (₁₊ n) ⊢ [ up g ]ʷ ≈ [ g ↥ ]ʷ
  up-≈ iI-gen = PB.sym (PB.axiom (ω↑=ω iI-gate))
  up-≈ S-gen  = PB.refl
  up-≈ K-gen  = PB.refl
  up-≈ CS-gen = PB.refl
  up-≈ (g ↥)  = PB.refl

  flatg-≈ : (g : Gen n) → n ⊢ [ flatg g ]ʷ ≈ [ g ]ʷ
  flatg-≈ iI-gen = PB.refl
  flatg-≈ S-gen  = PB.refl
  flatg-≈ K-gen  = PB.refl
  flatg-≈ CS-gen = PB.refl
  flatg-≈ (g ↥)  = PB.trans (up-≈ (flatg g)) (lemma-cong↑ _ _ (flatg-≈ g))

flat-≈ : (u : Circuit n) → n ⊢ flat u ≈ u
flat-≈ [ g ]ʷ  = flatg-≈ g
flat-≈ ε       = PB.refl
flat-≈ (u • t) = PB.cong (flat-≈ u) (flat-≈ t)

-- A rule instance, with its scalars on no wire.
by : 3 VRel, w === v → 3 ⊢ flat w ≈ flat v
by {w} {v} r = PB.trans (flat-≈ w) (PB.trans (PB.axiom r) (PB.sym (flat-≈ v)))

------------------------------------------------------------------------
-- The circuit rules hold in the paper's presentation

private
  ι₁-ax : ∀ {w v : Circuit 1} → 1 VRel, w === v → Rel ⊢ᴾ (ι₁ ʷ) w ≈ (ι₁ ʷ) v
  ι₁-ax (srel order-iI)          = PB.axiom P.ax-iI-iI-iI-iI=ε
  ι₁-ax (srel order-S)           = PB.axiom P.ax-S0-S0-S0-S0=ε
  ι₁-ax (srel order-K)           = PB.axiom P.ax-K0-K0=iI-iI-iI
  ι₁-ax (srel order-SK)          = PB.axiom P.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
  ι₁-ax (cong↑ (srel order-iI))  = PB.axiom P.ax-iI-iI-iI-iI=ε
  ι₁-ax (comm₁ S-gate iI-gen)    = PB.axiom P.ax-iI-S0=S0-iI
  ι₁-ax (comm₁ K-gate iI-gen)    = PB.axiom P.ax-iI-K0=K0-iI
  ι₁-ax (ω↑=ω iI-gate)           = PB.refl

  ι₂-ax : ∀ {w v : Circuit 2} → 2 VRel, w === v → Rel ⊢ᴾ (ι₂ ʷ) w ≈ (ι₂ ʷ) v
  ι₂-ax (srel order-iI)        = PB.axiom P.ax-iI-iI-iI-iI=ε
  ι₂-ax (srel order-S)         = PB.axiom P.ax-S1-S1-S1-S1=ε
  ι₂-ax (srel order-K)         = PB.axiom P.ax-K1-K1=iI-iI-iI
  ι₂-ax (srel order-SK)        = PB.axiom P.ax-S1-K1-S1-K1-S1-K1=iI-iI-iI
  ι₂-ax (srel order-CS)        = PB.axiom P.ax-CS01-CS01-CS01-CS01=ε
  ι₂-ax (srel comm-CS-S↑)      = PB.axiom P.ax-CS01-S0=S0-CS01
  ι₂-ax (srel comm-CS-S)       = PB.axiom P.ax-CS01-S1=S1-CS01
  ι₂-ax (srel X↑-CS)           = PB.axiom P.ax-X0-CS01=CS01-CS01-CS01-X0-S1
  ι₂-ax (srel X-CS)            = PB.axiom P.ax-X1-CS01=CS01-CS01-CS01-X1-S0
  ι₂-ax (srel CS-K↑)           = PB.axiom P.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01
  ι₂-ax (srel CS-K)            = PB.axiom P.ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01
  ι₂-ax (cong↑ {w = w} {v} r)  =
    Eq.subst₂ (Rel ⊢ᴾ_≈_) (Eq.sym (ι₂-↑ w)) (Eq.sym (ι₂-↑ v)) (ι₁-ax r)
  ι₂-ax (comm₁ S-gate iI-gen)        = PB.axiom P.ax-iI-S1=S1-iI
  ι₂-ax (comm₁ K-gate iI-gen)        = PB.axiom P.ax-iI-K1=K1-iI
  ι₂-ax (comm₁ S-gate (iI-gen ↥))    = PB.axiom P.ax-iI-S1=S1-iI
  ι₂-ax (comm₁ K-gate (iI-gen ↥))    = PB.axiom P.ax-iI-K1=K1-iI
  ι₂-ax (comm₁ S-gate S-gen)         = PB.sym (PB.axiom P.ax-S1-S0=S0-S1)
  ι₂-ax (comm₁ S-gate K-gen)         = PB.sym (PB.axiom P.ax-S1-K0=K0-S1)
  ι₂-ax (comm₁ K-gate S-gen)         = PB.sym (PB.axiom P.ax-K1-S0=S0-K1)
  ι₂-ax (comm₁ K-gate K-gen)         = PB.sym (PB.axiom P.ax-K1-K0=K0-K1)
  ι₂-ax (comm₂ CS-gate iI-gen)       = PB.axiom P.ax-iI-CS01=CS01-iI
  ι₂-ax (ω↑=ω iI-gate)               = PB.refl

ι-ax : 3 VRel, w === v → Rel ⊢ᴾ (ι ʷ) w ≈ (ι ʷ) v
ι-ax (srel order-iI)       = PB.axiom P.ax-iI-iI-iI-iI=ε
ι-ax (srel order-S)        = PB.axiom P.ax-S2-S2-S2-S2=ε
ι-ax (srel order-K)        = PB.axiom P.ax-K2-K2=iI-iI-iI
ι-ax (srel order-SK)       = PB.axiom P.ax-S2-K2-S2-K2-S2-K2=iI-iI-iI
ι-ax (srel order-CS)       = PB.axiom P.ax-CS12-CS12-CS12-CS12=ε
ι-ax (srel comm-CS-S↑)     = PB.axiom P.ax-CS12-S1=S1-CS12
ι-ax (srel comm-CS-S)      = PB.axiom P.ax-CS12-S2=S2-CS12
ι-ax (srel X↑-CS)          = PB.axiom P.ax-X1-CS12=CS12-CS12-CS12-X1-S2
ι-ax (srel X-CS)           = PB.axiom P.ax-X2-CS12=CS12-CS12-CS12-X2-S1
ι-ax (srel CS-K↑)          = PB.axiom P.ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12
ι-ax (srel CS-K)           = PB.axiom P.ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12
ι-ax (srel comm-CS-CS)     = PB.axiom P.ax-CS12-CS01=CS01-CS12
ι-ax (srel rel-CX-CS)      = PB.axiom P.ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12
ι-ax (srel rel-CX-CS²)     = PB.axiom P.ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12
ι-ax (srel rel-CS-CX)      = PB.axiom P.ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21
ι-ax (srel rel-CS-K)       = PB.axiom P.ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12
ι-ax (srel rel-CS-K³)      = PB.axiom P.ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1
ι-ax (cong↑ {w = w} {v} r) =
  Eq.subst₂ (Rel ⊢ᴾ_≈_) (Eq.sym (ι-↑ w)) (Eq.sym (ι-↑ v)) (ι₂-ax r)
ι-ax (comm₁ S-gate iI-gen)          = PB.axiom P.ax-iI-S2=S2-iI
ι-ax (comm₁ K-gate iI-gen)          = PB.axiom P.ax-iI-K2=K2-iI
ι-ax (comm₁ S-gate (iI-gen ↥))      = PB.axiom P.ax-iI-S2=S2-iI
ι-ax (comm₁ K-gate (iI-gen ↥))      = PB.axiom P.ax-iI-K2=K2-iI
ι-ax (comm₁ S-gate ((iI-gen ↥) ↥))  = PB.axiom P.ax-iI-S2=S2-iI
ι-ax (comm₁ K-gate ((iI-gen ↥) ↥))  = PB.axiom P.ax-iI-K2=K2-iI
ι-ax (comm₁ S-gate S-gen)           = PB.sym (PB.axiom P.ax-S2-S1=S1-S2)
ι-ax (comm₁ S-gate K-gen)           = PB.sym (PB.axiom P.ax-S2-K1=K1-S2)
ι-ax (comm₁ K-gate S-gen)           = PB.sym (PB.axiom P.ax-K2-S1=S1-K2)
ι-ax (comm₁ K-gate K-gen)           = PB.sym (PB.axiom P.ax-K2-K1=K1-K2)
ι-ax (comm₁ S-gate CS-gen)          = PB.axiom P.ax-CS01-S2=S2-CS01
ι-ax (comm₁ K-gate CS-gen)          = PB.axiom P.ax-CS01-K2=K2-CS01
ι-ax (comm₁ S-gate (S-gen ↥))       = PB.sym (PB.axiom P.ax-S2-S0=S0-S2)
ι-ax (comm₁ S-gate (K-gen ↥))       = PB.sym (PB.axiom P.ax-S2-K0=K0-S2)
ι-ax (comm₁ K-gate (S-gen ↥))       = PB.sym (PB.axiom P.ax-K2-S0=S0-K2)
ι-ax (comm₁ K-gate (K-gen ↥))       = PB.sym (PB.axiom P.ax-K2-K0=K0-K2)
ι-ax (comm₂ CS-gate iI-gen)         = PB.axiom P.ax-iI-CS12=CS12-iI
ι-ax (comm₂ CS-gate (iI-gen ↥))     = PB.axiom P.ax-iI-CS12=CS12-iI
ι-ax (comm₂ CS-gate S-gen)          = PB.sym (PB.axiom P.ax-CS12-S0=S0-CS12)
ι-ax (comm₂ CS-gate K-gen)          = PB.sym (PB.axiom P.ax-CS12-K0=K0-CS12)
ι-ax (ω↑=ω iI-gate)                 = PB.refl

------------------------------------------------------------------------
-- The paper's relations hold for circuits

private
  -- A circuit rule on wires 1–2, and on wire 2.
  by↑ : ∀ {w v : Circuit 2} → 2 VRel, w === v → 3 ⊢ flat (w ↑) ≈ flat (v ↑)
  by↑ r = by (cong↑ r)

  by↑↑ : ∀ {w v : Circuit 1} → 1 VRel, w === v → 3 ⊢ flat (w ↑ ↑) ≈ flat (v ↑ ↑)
  by↑↑ r = by (cong↑ (cong↑ r))

  -- A structural commutation, the other way round.
  bys : 3 VRel, w === v → 3 ⊢ flat v ≈ flat w
  bys r = PB.sym (by r)

  bys↑ : ∀ {w v : Circuit 2} → 2 VRel, w === v → 3 ⊢ flat (v ↑) ≈ flat (w ↑)
  bys↑ r = PB.sym (by↑ r)

κ-ax : ∀ {u t} → Rel u t → 3 ⊢ (κ ʷ) u ≈ (κ ʷ) t
κ-ax P.ax-iI-iI-iI-iI=ε         = by (srel order-iI)
κ-ax P.ax-iI-S0=S0-iI           = PB.sym (comm-gate₀-w iI-gate (S ↑ ↑))
κ-ax P.ax-iI-S1=S1-iI           = PB.sym (comm-gate₀-w iI-gate (S ↑))
κ-ax P.ax-iI-S2=S2-iI           = PB.sym (comm-gate₀-w iI-gate S)
κ-ax P.ax-iI-K0=K0-iI           = PB.sym (comm-gate₀-w iI-gate (K ↑ ↑))
κ-ax P.ax-iI-K1=K1-iI           = PB.sym (comm-gate₀-w iI-gate (K ↑))
κ-ax P.ax-iI-K2=K2-iI           = PB.sym (comm-gate₀-w iI-gate K)
κ-ax P.ax-iI-CS01=CS01-iI       = PB.sym (comm-gate₀-w iI-gate (CS ↑))
κ-ax P.ax-iI-CS12=CS12-iI       = PB.sym (comm-gate₀-w iI-gate CS)
κ-ax P.ax-S1-S0=S0-S1           = bys↑ (comm₁ S-gate S-gen)
κ-ax P.ax-S2-S0=S0-S2           = bys (comm₁ S-gate (S-gen ↥))
κ-ax P.ax-S2-S1=S1-S2           = bys (comm₁ S-gate S-gen)
κ-ax P.ax-K1-K0=K0-K1           = bys↑ (comm₁ K-gate K-gen)
κ-ax P.ax-K2-K0=K0-K2           = bys (comm₁ K-gate (K-gen ↥))
κ-ax P.ax-K2-K1=K1-K2           = bys (comm₁ K-gate K-gen)
κ-ax P.ax-CS01-S0=S0-CS01       = by↑ (srel comm-CS-S↑)
κ-ax P.ax-CS12-S0=S0-CS12       = bys (comm₂ CS-gate S-gen)
κ-ax P.ax-CS01-S1=S1-CS01       = by↑ (srel comm-CS-S)
κ-ax P.ax-CS12-S1=S1-CS12       = by (srel comm-CS-S↑)
κ-ax P.ax-CS01-S2=S2-CS01       = by (comm₁ S-gate CS-gen)
κ-ax P.ax-CS12-S2=S2-CS12       = by (srel comm-CS-S)
κ-ax P.ax-CS12-CS01=CS01-CS12   = by (srel comm-CS-CS)
κ-ax P.ax-S1-K0=K0-S1           = bys↑ (comm₁ S-gate K-gen)
κ-ax P.ax-S2-K0=K0-S2           = bys (comm₁ S-gate (K-gen ↥))
κ-ax P.ax-S2-K1=K1-S2           = bys (comm₁ S-gate K-gen)
κ-ax P.ax-K1-S0=S0-K1           = bys↑ (comm₁ K-gate S-gen)
κ-ax P.ax-K2-S0=S0-K2           = bys (comm₁ K-gate (S-gen ↥))
κ-ax P.ax-K2-S1=S1-K2           = bys (comm₁ K-gate S-gen)
κ-ax P.ax-CS01-K2=K2-CS01       = by (comm₁ K-gate CS-gen)
κ-ax P.ax-CS12-K0=K0-CS12       = bys (comm₂ CS-gate K-gen)
κ-ax P.ax-S0-S0-S0-S0=ε         = by↑↑ (srel order-S)
κ-ax P.ax-S1-S1-S1-S1=ε         = by↑ (srel order-S)
κ-ax P.ax-S2-S2-S2-S2=ε         = by (srel order-S)
κ-ax P.ax-CS01-CS01-CS01-CS01=ε = by↑ (srel order-CS)
κ-ax P.ax-CS12-CS12-CS12-CS12=ε = by (srel order-CS)
κ-ax P.ax-K0-K0=iI-iI-iI        = by↑↑ (srel order-K)
κ-ax P.ax-K1-K1=iI-iI-iI        = by↑ (srel order-K)
κ-ax P.ax-K2-K2=iI-iI-iI        = by (srel order-K)
κ-ax P.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = by↑↑ (srel order-SK)
κ-ax P.ax-S1-K1-S1-K1-S1-K1=iI-iI-iI = by↑ (srel order-SK)
κ-ax P.ax-S2-K2-S2-K2-S2-K2=iI-iI-iI = by (srel order-SK)
κ-ax P.ax-X0-CS01=CS01-CS01-CS01-X0-S1 = by↑ (srel X↑-CS)
κ-ax P.ax-X1-CS01=CS01-CS01-CS01-X1-S0 = by↑ (srel X-CS)
κ-ax P.ax-X1-CS12=CS12-CS12-CS12-X1-S2 = by (srel X↑-CS)
κ-ax P.ax-X2-CS12=CS12-CS12-CS12-X2-S1 = by (srel X-CS)
κ-ax P.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = by↑ (srel CS-K↑)
κ-ax P.ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01 = by↑ (srel CS-K)
κ-ax P.ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12 = by (srel CS-K↑)
κ-ax P.ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12 = by (srel CS-K)
κ-ax P.ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12 = by (srel rel-CX-CS)
κ-ax P.ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12 = by (srel rel-CX-CS²)
κ-ax P.ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21 = by (srel rel-CS-CX)
κ-ax P.ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12 = by (srel rel-CS-K)
κ-ax P.ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1 = by (srel rel-CS-K³)

------------------------------------------------------------------------
-- κ and ι are inverse on letters

ικ : ∀ (x : PGen) → Rel ⊢ᴾ [ x ]ʷ ≈ (ι ʷ) (κ x)
ικ P.iI-gen   = PB.refl
ικ P.S0-gen   = PB.refl
ικ P.S1-gen   = PB.refl
ικ P.S2-gen   = PB.refl
ικ P.K0-gen   = PB.refl
ικ P.K1-gen   = PB.refl
ικ P.K2-gen   = PB.refl
ικ P.CS01-gen = PB.refl
ικ P.CS12-gen = PB.refl

κι : ∀ (x : Gen 3) → 3 ⊢ [ x ]ʷ ≈ (κ ʷ) (ι x)
κι iI-gen               = PB.refl
κι S-gen                = PB.refl
κι K-gen                = PB.refl
κι CS-gen               = PB.refl
κι (iI-gen ↥)           = PB.sym (flat-≈ [ iI-gen ↥ ]ʷ)
κι (S-gen ↥)            = PB.refl
κι (K-gen ↥)            = PB.refl
κι (CS-gen ↥)           = PB.refl
κι ((iI-gen ↥) ↥)       = PB.sym (flat-≈ [ iI-gen ↥ ↥ ]ʷ)
κι ((S-gen ↥) ↥)        = PB.refl
κι ((K-gen ↥) ↥)        = PB.refl
κι (((iI-gen ↥) ↥) ↥)   = PB.sym (flat-≈ [ iI-gen ↥ ↥ ↥ ]ʷ)

------------------------------------------------------------------------
-- So (ι ʷ) is a group isomorphism

private
  module GC = Group-Lemmas (3 VRel,_===_) (grouplike {3})
  module GP = Group-Lemmas Rel group-like

open import Presentation.Morphism (3 VRel,_===_) Rel using (module GroupMorphism)
open GroupMorphism (grouplike {3}) group-like using (module StarGroupIsomorphism)

circuits≅paper : GroupMorphisms.IsGroupIsomorphism
                   (Group.rawGroup GC.•-ε-group) (Group.rawGroup GP.•-ε-group) (ι ʷ)
circuits≅paper = StarGroupIsomorphism.isGroupIsomorphism ι κ ι-ax ικ κ-ax κι
