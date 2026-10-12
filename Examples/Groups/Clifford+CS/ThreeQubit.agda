------------------------------------------------------------------------
-- Presentations of groups
--
-- Three-qubit completeness, from Bian and Selinger's
--
-- The rules of Syntactics are, up to the structural rules and the
-- spelling of their wires, the relations of Figure 2 of Bian and
-- Selinger, "Generators and relations for 3-qubit Clifford+CS
-- operators" (Clifford+CS-3qubit.Theorem.CliffordCS), and that paper
-- proves them complete for three qubits (Clifford+CS-3qubit.
-- Presentation.complete, from the completeness of the two-level
-- relations proved in Clifford+CS-TwoLevel).  So three-qubit
-- completeness here is the back-and-forth argument with their circuits
-- as the auxiliary language:
--
--   * the decoding d sends each of their nine generators to the gate
--     it names, and respects their relations — each is one of the rules
--     here, lifted a wire or two, or a structural rule (d-wd);
--   * the encoding e sends each generator back, and d (e g) is g with
--     the scalar respelled (d∘e, Canonical);
--   * their words have the matrices of their translations into two-
--     level words, which agree with ours (Bridge, TwoLevelTries), so
--     their completeness applies to words with the same scaled matrix
--     (complete-Y).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.ThreeQubit where

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (Scaled ; _~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Soundness using (sound)
open import Examples.Groups.Clifford+CS.Canonical using (can ; can-≈ ; via-can)
import Examples.Groups.Clifford+CS.BackAndForth as BackAndForth
import Examples.Groups.Clifford+CS.Bridge as Bridge
import Examples.Groups.Clifford+CS.TwoLevelTries as TwoLevelTries

open import Quantum.Synthesis.Matrix using (_·*·_)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (⟦_⟧ᵐ ; ⟦•⟧ᵐ)
import Examples.Groups.Clifford+CS-3qubit.Theorem as BS
import Examples.Groups.Clifford+CS-3qubit.Presentation as BSP

module B = BS.CliffordCS

------------------------------------------------------------------------
-- The decoding and the encoding

d : B.Gen → Circuit 3
d B.S0-gen   = S
d B.S1-gen   = S ↑
d B.S2-gen   = S ↑ ↑
d B.CS01-gen = CS
d B.CS12-gen = CS ↑
d B.iI-gen   = iI
d B.K0-gen   = K
d B.K1-gen   = K ↑
d B.K2-gen   = K ↑ ↑

e : Gen 3 → Word B.Gen
e (gate₀ I-gate)         = B.iI
e (gate₁ S-gate)         = B.S0
e (gate₁ K-gate)         = B.K0
e (gate₂ CS-gate)        = B.CS01
e (gate₀ I-gate ↥)       = B.iI
e (gate₁ S-gate ↥)       = B.S1
e (gate₁ K-gate ↥)       = B.K1
e (gate₂ CS-gate ↥)      = B.CS12
e (gate₀ I-gate ↥ ↥)     = B.iI
e (gate₁ S-gate ↥ ↥)     = B.S2
e (gate₁ K-gate ↥ ↥)     = B.K2
e (gate₀ I-gate ↥ ↥ ↥)   = B.iI

-- The decoding inverts the encoding: d (e g) is the canonical spelling
-- of g.
d∘e : ∀ g → 3 ⊢ [ g ]ʷ ≈ (d ʷ) (e g)
d∘e (gate₀ I-gate)       = can-≈ [ gate₀ I-gate ]ʷ
d∘e (gate₁ S-gate)       = PB.refl
d∘e (gate₁ K-gate)       = PB.refl
d∘e (gate₂ CS-gate)      = PB.refl
d∘e (gate₀ I-gate ↥)     = can-≈ [ gate₀ I-gate ↥ ]ʷ
d∘e (gate₁ S-gate ↥)     = PB.refl
d∘e (gate₁ K-gate ↥)     = PB.refl
d∘e (gate₂ CS-gate ↥)    = PB.refl
d∘e (gate₀ I-gate ↥ ↥)   = can-≈ [ gate₀ I-gate ↥ ↥ ]ʷ
d∘e (gate₁ S-gate ↥ ↥)   = PB.refl
d∘e (gate₁ K-gate ↥ ↥)   = PB.refl
d∘e (gate₀ I-gate ↥ ↥ ↥) = can-≈ [ gate₀ I-gate ↥ ↥ ↥ ]ʷ

------------------------------------------------------------------------
-- The decoding respects Figure 2

private
  ax : ∀ {w v} → 3 VRel, w === v → 3 ⊢ w ≈ v
  ax = PB.axiom

d-wd : ∀ {u t} → B.Rel u t → 3 ⊢ (d ʷ) u ≈ (d ʷ) t
-- The scalar.
d-wd B.ax-iI-iI-iI-iI=ε     = ax (srel order-I)
d-wd B.ax-iI-S0=S0-iI       = PB.sym (comm₀ I-gate S-gen)
d-wd B.ax-iI-S1=S1-iI       = PB.sym (comm₀ I-gate (S-gen ↥))
d-wd B.ax-iI-S2=S2-iI       = PB.sym (comm₀ I-gate (S-gen ↥ ↥))
d-wd B.ax-iI-K0=K0-iI       = PB.sym (comm₀ I-gate K-gen)
d-wd B.ax-iI-K1=K1-iI       = PB.sym (comm₀ I-gate (K-gen ↥))
d-wd B.ax-iI-K2=K2-iI       = PB.sym (comm₀ I-gate (K-gen ↥ ↥))
d-wd B.ax-iI-CS01=CS01-iI   = PB.sym (comm₀ I-gate CS-gen)
d-wd B.ax-iI-CS12=CS12-iI   = PB.sym (comm₀ I-gate (CS-gen ↥))
-- Disjoint wires.
d-wd B.ax-S1-S0=S0-S1       = ax (comm₁ S-gate S-gen)
d-wd B.ax-S2-S0=S0-S2       = ax (comm₁ S-gate (S-gen ↥))
d-wd B.ax-S2-S1=S1-S2       = ax (cong↑ (comm₁ S-gate S-gen))
d-wd B.ax-K1-K0=K0-K1       = ax (comm₁ K-gate K-gen)
d-wd B.ax-K2-K0=K0-K2       = ax (comm₁ K-gate (K-gen ↥))
d-wd B.ax-K2-K1=K1-K2       = ax (cong↑ (comm₁ K-gate K-gen))
d-wd B.ax-CS01-S0=S0-CS01   = ax (srel comm-CS-S₀)
d-wd B.ax-CS12-S0=S0-CS12   = ax (comm₁ S-gate CS-gen)
d-wd B.ax-CS01-S1=S1-CS01   = ax (srel comm-CS-S₁)
d-wd B.ax-CS12-S1=S1-CS12   = ax (cong↑ (srel comm-CS-S₀))
d-wd B.ax-CS01-S2=S2-CS01   = PB.sym (ax (comm₂ CS-gate S-gen))
d-wd B.ax-CS12-S2=S2-CS12   = ax (cong↑ (srel comm-CS-S₁))
d-wd B.ax-CS12-CS01=CS01-CS12 = ax (srel comm-CS↑-CS)
d-wd B.ax-S1-K0=K0-S1       = ax (comm₁ K-gate S-gen)
d-wd B.ax-S2-K0=K0-S2       = ax (comm₁ K-gate (S-gen ↥))
d-wd B.ax-S2-K1=K1-S2       = ax (cong↑ (comm₁ K-gate S-gen))
d-wd B.ax-K1-S0=S0-K1       = ax (comm₁ S-gate K-gen)
d-wd B.ax-K2-S0=S0-K2       = ax (comm₁ S-gate (K-gen ↥))
d-wd B.ax-K2-S1=S1-K2       = ax (cong↑ (comm₁ S-gate K-gen))
d-wd B.ax-CS01-K2=K2-CS01   = PB.sym (ax (comm₂ CS-gate K-gen))
d-wd B.ax-CS12-K0=K0-CS12   = ax (comm₁ K-gate CS-gen)
-- Orders.
d-wd B.ax-S0-S0-S0-S0=ε     = ax (srel order-S)
d-wd B.ax-S1-S1-S1-S1=ε     = ax (cong↑ (srel order-S))
d-wd B.ax-S2-S2-S2-S2=ε     = ax (cong↑ (cong↑ (srel order-S)))
d-wd B.ax-CS01-CS01-CS01-CS01=ε = ax (srel order-CS)
d-wd B.ax-CS12-CS12-CS12-CS12=ε = ax (cong↑ (srel order-CS))
d-wd B.ax-K0-K0=iI-iI-iI    = ax (srel order-K)
d-wd B.ax-K1-K1=iI-iI-iI    = via-can {w = (K • K) ↑} {(iI • iI • iI) ↑} (ax (cong↑ (srel order-K)))
d-wd B.ax-K2-K2=iI-iI-iI    = via-can {w = (K • K) ↑ ↑} {(iI • iI • iI) ↑ ↑} (ax (cong↑ (cong↑ (srel order-K))))
d-wd B.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = ax (srel order-SK)
d-wd B.ax-S1-K1-S1-K1-S1-K1=iI-iI-iI = via-can {w = (S • K • S • K • S • K) ↑} {(iI • iI • iI) ↑} (ax (cong↑ (srel order-SK)))
d-wd B.ax-S2-K2-S2-K2-S2-K2=iI-iI-iI = via-can {w = (S • K • S • K • S • K) ↑ ↑} {(iI • iI • iI) ↑ ↑} (ax (cong↑ (cong↑ (srel order-SK))))
-- X and CS.
d-wd B.ax-X0-CS01=CS01-CS01-CS01-X0-S1 = ax (srel X-CS₀)
d-wd B.ax-X1-CS01=CS01-CS01-CS01-X1-S0 = via-can {w = X ↑ • CS} {CS • CS • CS • X ↑ • S} (ax (srel X-CS₁))
d-wd B.ax-X1-CS12=CS12-CS12-CS12-X1-S2 = via-can {w = (X • CS) ↑} {(CS • CS • CS • X • S ↑) ↑} (ax (cong↑ (srel X-CS₀)))
d-wd B.ax-X2-CS12=CS12-CS12-CS12-X2-S1 = via-can {w = (X ↑ • CS) ↑} {(CS • CS • CS • X ↑ • S) ↑} (ax (cong↑ (srel X-CS₁)))
-- CS and K.
d-wd B.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = ax (srel CS-K₀)
d-wd B.ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01 = ax (srel CS-K₁)
d-wd B.ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12 = ax (cong↑ (srel CS-K₀))
d-wd B.ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12 = ax (cong↑ (srel CS-K₁))
-- Three wires.
d-wd B.ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12 = via-can {w = CX₁₀ • CX₀₁ • CS ↑ • CX₀₁ • CX₁₀} {CX₁₂ • CX₂₁ • CS • CX₂₁ • CX₁₂} (ax (srel rel-266))
d-wd B.ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12 = via-can {w = CX₁₀ • CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CX₁₀} {CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CS ↑ • CS ↑} (ax (srel rel-267))
d-wd B.ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21 = via-can {w = CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁} {CS • CX₂₁ • CS • CS • CS • CX₂₁} (ax (srel rel-268))
d-wd B.ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12 = via-can {w = CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS} {CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑} (ax (srel rel-269))
d-wd B.ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1 =
  via-can {w = CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑}
          {CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS} (ax (srel rel-272))

------------------------------------------------------------------------
-- Their words have the matrices of their two-level translations

-- A generator's matrix, read through the decoding.
⟦_⟧ʸ : B.Gen → Scaled 3
⟦ y ⟧ʸ = ⟦ d y ⟧

module BF = BackAndForth 3 B.Rel ⟦_⟧ʸ
open BF using (⟦_⟧Y)

private
  module T = Bridge.TwoLevel 3
  module TT = TwoLevelTries 3

  -- Each of the nine, compared with its two-level translation.
  gen-~ : ∀ y → ⟦ d y ⟧ ~ T.⟦ BSP.tl y ⟧Y
  gen-~ B.S0-gen   = TT.by-same (d B.S0-gen)   (BSP.tl B.S0-gen)   Eq.refl
  gen-~ B.S1-gen   = TT.by-same (d B.S1-gen)   (BSP.tl B.S1-gen)   Eq.refl
  gen-~ B.S2-gen   = TT.by-same (d B.S2-gen)   (BSP.tl B.S2-gen)   Eq.refl
  gen-~ B.CS01-gen = TT.by-same (d B.CS01-gen) (BSP.tl B.CS01-gen) Eq.refl
  gen-~ B.CS12-gen = TT.by-same (d B.CS12-gen) (BSP.tl B.CS12-gen) Eq.refl
  gen-~ B.iI-gen   = TT.by-same (d B.iI-gen)   (BSP.tl B.iI-gen)   Eq.refl
  gen-~ B.K0-gen   = TT.by-same (d B.K0-gen)   (BSP.tl B.K0-gen)   Eq.refl
  gen-~ B.K1-gen   = TT.by-same (d B.K1-gen)   (BSP.tl B.K1-gen)   Eq.refl
  gen-~ B.K2-gen   = TT.by-same (d B.K2-gen)   (BSP.tl B.K2-gen)   Eq.refl

  gen-Φ : ∀ y → Bridge.Φ ⟦ y ⟧ʸ ≡ ⟦ BSP.tl y ⟧ᵐ
  gen-Φ y = Eq.trans (Bridge.Φ-cong {s = ⟦ d y ⟧} {T.⟦ BSP.tl y ⟧Y} (gen-~ y)) (T.Φ-Y (BSP.tl y))

  Φ-Y : ∀ u → Bridge.Φ ⟦ u ⟧Y ≡ ⟦ (BSP.tl ʷ) u ⟧ᵐ
  Φ-Y [ y ]ʷ  = gen-Φ y
  Φ-Y ε       = Bridge.Φ-ε {3}
  Φ-Y (u • t) = Eq.trans (Bridge.Φ-∙ ⟦ u ⟧Y ⟦ t ⟧Y)
                  (Eq.trans (Eq.cong₂ _·*·_ (Φ-Y u) (Φ-Y t)) (Eq.sym (⟦•⟧ᵐ ((BSP.tl ʷ) u) ((BSP.tl ʷ) t))))

-- Their completeness, for words with the same scaled matrix.
complete-Y : ∀ {u t : Word B.Gen} → ⟦ u ⟧Y ~ ⟦ t ⟧Y → PB._≈_ B.Rel u t
complete-Y {u} {t} eq =
  BSP.complete {u} {t} (Eq.trans (Eq.sym (Φ-Y u))
    (Eq.trans (Bridge.Φ-cong {s = ⟦ u ⟧Y} {⟦ t ⟧Y} eq) (Φ-Y t)))

-- The encoding preserves the semantics: d (e g) is a respelling of g.
e-sem : ∀ g → ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
e-sem (gate₀ I-gate)       = sound (PB.sym (d∘e (gate₀ I-gate)))
e-sem (gate₁ S-gate)       = sound (PB.sym (d∘e (gate₁ S-gate)))
e-sem (gate₁ K-gate)       = sound (PB.sym (d∘e (gate₁ K-gate)))
e-sem (gate₂ CS-gate)      = sound (PB.sym (d∘e (gate₂ CS-gate)))
e-sem (gate₀ I-gate ↥)     = sound (PB.sym (d∘e (gate₀ I-gate ↥)))
e-sem (gate₁ S-gate ↥)     = sound (PB.sym (d∘e (gate₁ S-gate ↥)))
e-sem (gate₁ K-gate ↥)     = sound (PB.sym (d∘e (gate₁ K-gate ↥)))
e-sem (gate₂ CS-gate ↥)    = sound (PB.sym (d∘e (gate₂ CS-gate ↥)))
e-sem (gate₀ I-gate ↥ ↥)   = sound (PB.sym (d∘e (gate₀ I-gate ↥ ↥)))
e-sem (gate₁ S-gate ↥ ↥)   = sound (PB.sym (d∘e (gate₁ S-gate ↥ ↥)))
e-sem (gate₁ K-gate ↥ ↥)   = sound (PB.sym (d∘e (gate₁ K-gate ↥ ↥)))
e-sem (gate₀ I-gate ↥ ↥ ↥) = sound (PB.sym (d∘e (gate₀ I-gate ↥ ↥ ↥)))

------------------------------------------------------------------------
-- Three-qubit completeness

open BF.Complete complete-Y e e-sem d d-wd d∘e public using (complete)
