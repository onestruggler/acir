------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on five wires (Lemma 8.7 at n = 5 and the assembly)
--
-- The back-and-forth argument (BackAndForth) for the five-wire theory
-- with AX, through P′ on thirty-two indices: P′ is complete for its
-- reading (BridgeGray.complete-P), the encoding keeps the semantics
-- (Section8.e-sem), the affine decoding respects the rules of P′ (Five.
-- DWD, Lemma 8.8), and it inverts the encoding (`d∘e₅`, Lemma 8.7).
-- For the last, as in Lemma87.Decodes, it suffices to give for each
-- generator g some word w over P′ that decodes to g: the decoding keeps
-- the semantics (Five.DecSem), so w has g's reading, hence is the
-- encoding of g in P′.  A gate on the wires 0 … 3 decodes from its
-- four-wire encodings on the two halves (Five.Halves.below), S on wire 4
-- and CS on the wires 3 4 — λ¹ of the scalar and of S on wire 3 — from
-- the upper half alone (`above`), and K on wire 4 from K on wire 3
-- moved by the swap of the wires 3 4 (Five.K4).
--
-- Everything is relative to the generated five-wire lemmas (`Inputs`)
-- and completeness on four wires (Four.Complete).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)

module Examples.Groups.Clifford+CS.Five.Complete5 (I : Inputs) (c4 : Complete 4) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Normalization.Reidemeister-Schreier using (module Star-Injective-Simplified)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
  using (Circuit ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; I-gate ; S-gate ; K-gate ; CS-gate ; _↓ᵏ_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.Five.Rules
  using (_XVRel,_===_ ; _⊢ₓ_≈_ ; cong↑ₓ ; ω↑=ωₓ)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Soundness using (soundₓ)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
import Examples.Groups.Clifford+CS.Encoding 1 as E5
import Examples.Groups.Clifford+CS.Section8 1 as S8
open import Examples.Groups.Clifford+CS.BridgeGray 5 using (⟦_⟧PY ; module Complete)

open import Examples.Groups.Clifford+CS.Five.Facts4Inst c4 using (facts4)
open import Examples.Groups.Clifford+CS.Five.Gadget5 I facts4 using (cind)
open import Examples.Groups.Clifford+CS.Five.Dec5 I facts4 cind using (d)
open import Examples.Groups.Clifford+CS.Five.DWD I facts4 c4 cind using (dwd)
open import Examples.Groups.Clifford+CS.Five.DecSem I facts4 cind using (dʷ-sem)
open import Examples.Groups.Clifford+CS.Five.Halves I facts4 c4 cind using (wd ; upw ; below ; above)
open import Examples.Groups.Clifford+CS.Five.K4 I facts4 c4 cind using (wK ; K₄-dec)

open Complete E5.big using (complete-P)

private
  ≡→ : ∀ {u v : Circuit 5} → u ≡ v → u ≈ v
  ≡→ Eq.refl = refl

------------------------------------------------------------------------
-- The decoding respects the congruence of P′

d-≈ : ∀ {u t : Word (GenP 32)} → PB._≈_ (E5.N R,_===_) u t → (d ʷ) u ≈ (d ʷ) t
d-≈ = PP.StarCongruence.fʷ-cong (E5.N R,_===_) (_XVRel,_===_ 5) d dwd

------------------------------------------------------------------------
-- Lemma 8.7 at five wires

-- A word over P′ decoding to a generator decodes as its encoding does.
by-decodes : (g : Gen 5) (w : Word (GenP 32)) → [ g ]ʷ ≈ (d ʷ) w → [ g ]ʷ ≈ (d ʷ) (E5.e g)
by-decodes g w h = trans h (d-≈ (complete-P {w} {E5.e g} same))
  where
  same : ⟦ w ⟧PY ~ ⟦ E5.e g ⟧PY
  same =
    ~-trans {s = ⟦ w ⟧PY} {t = ⟦ (d ʷ) w ⟧} {u = ⟦ E5.e g ⟧PY}
      (~-sym {s = ⟦ (d ʷ) w ⟧} {t = ⟦ w ⟧PY} (dʷ-sem w))
      (~-trans {s = ⟦ (d ʷ) w ⟧} {t = ⟦ [ g ]ʷ ⟧} {u = ⟦ E5.e g ⟧PY}
        (soundₓ (sym h))
        (~-sym {s = ⟦ E5.e g ⟧PY} {t = ⟦ [ g ]ʷ ⟧} (S8.e-sem g)))

private
  -- A gate on the wires 0 … 3.
  low : (g : Gen 5) (h : Gen 4) → [ g ]ʷ ≡ [ h ]ʷ ↓ᵏ 1 → [ g ]ʷ ≈ (d ʷ) (E5.e g)
  low g h p = by-decodes g (wd [ h ]ʷ) (trans (≡→ p) (sym (below [ h ]ʷ)))

  -- The scalar, lifted five times, is the scalar.
  ι↥⁵ : [ gate₀ I-gate ↥ ↥ ↥ ↥ ↥ ]ʷ ≈ [ gate₀ {5} I-gate ]ʷ
  ι↥⁵ =
    trans (PB.axiom (cong↑ₓ (cong↑ₓ (cong↑ₓ (cong↑ₓ (ω↑=ωₓ I-gate))))))
      (trans (PB.axiom (cong↑ₓ (cong↑ₓ (cong↑ₓ (ω↑=ωₓ I-gate)))))
        (trans (PB.axiom (cong↑ₓ (cong↑ₓ (ω↑=ωₓ I-gate))))
          (trans (PB.axiom (cong↑ₓ (ω↑=ωₓ I-gate))) (PB.axiom (ω↑=ωₓ I-gate)))))

d∘e₅ : ∀ (g : Gen 5) → [ g ]ʷ ≈ (d ʷ) (E5.e g)
d∘e₅ g@(gate₀ I-gate)                   = low g (gate₀ I-gate) Eq.refl
d∘e₅ g@(gate₁ S-gate)                   = low g (gate₁ S-gate) Eq.refl
d∘e₅ g@(gate₁ K-gate)                   = low g (gate₁ K-gate) Eq.refl
d∘e₅ g@(gate₂ CS-gate)                  = low g (gate₂ CS-gate) Eq.refl
d∘e₅ g@(gate₀ I-gate ↥)                 = low g (gate₀ I-gate ↥) Eq.refl
d∘e₅ g@(gate₁ S-gate ↥)                 = low g (gate₁ S-gate ↥) Eq.refl
d∘e₅ g@(gate₁ K-gate ↥)                 = low g (gate₁ K-gate ↥) Eq.refl
d∘e₅ g@(gate₂ CS-gate ↥)                = low g (gate₂ CS-gate ↥) Eq.refl
d∘e₅ g@(gate₀ I-gate ↥ ↥)               = low g (gate₀ I-gate ↥ ↥) Eq.refl
d∘e₅ g@(gate₁ S-gate ↥ ↥)               = low g (gate₁ S-gate ↥ ↥) Eq.refl
d∘e₅ g@(gate₁ K-gate ↥ ↥)               = low g (gate₁ K-gate ↥ ↥) Eq.refl
d∘e₅ g@(gate₂ CS-gate ↥ ↥)              = low g (gate₂ CS-gate ↥ ↥) Eq.refl
d∘e₅ g@(gate₀ I-gate ↥ ↥ ↥)             = low g (gate₀ I-gate ↥ ↥ ↥) Eq.refl
d∘e₅ g@(gate₁ S-gate ↥ ↥ ↥)             = low g (gate₁ S-gate ↥ ↥ ↥) Eq.refl
d∘e₅ g@(gate₁ K-gate ↥ ↥ ↥)             = low g (gate₁ K-gate ↥ ↥ ↥) Eq.refl
d∘e₅ g@(gate₂ CS-gate ↥ ↥ ↥)            =
  by-decodes g (upw [ gate₁ S-gate ↥ ↥ ↥ ]ʷ) (sym (above [ gate₁ S-gate ↥ ↥ ↥ ]ʷ))
d∘e₅ g@(gate₀ I-gate ↥ ↥ ↥ ↥)           = low g (gate₀ I-gate ↥ ↥ ↥ ↥) Eq.refl
d∘e₅ g@(gate₁ S-gate ↥ ↥ ↥ ↥)           =
  by-decodes g (upw [ gate₀ I-gate ]ʷ) (sym (above [ gate₀ I-gate ]ʷ))
d∘e₅ g@(gate₁ K-gate ↥ ↥ ↥ ↥)           = by-decodes g wK K₄-dec
d∘e₅ g@(gate₀ I-gate ↥ ↥ ↥ ↥ ↥)         =
  by-decodes g (wd [ gate₀ I-gate ]ʷ) (trans ι↥⁵ (sym (below [ gate₀ I-gate ]ʷ)))

------------------------------------------------------------------------
-- Completeness

private
  eʷ-sem : (w : Circuit 5) → ⟦ (E5.e ʷ) w ⟧PY ~ ⟦ w ⟧
  eʷ-sem [ g ]ʷ  = S8.e-sem g
  eʷ-sem ε       = ~-sym {s = ⟦_⟧ {5} ε} {t = ε∙} (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {5} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
  eʷ-sem (u • v) =
    ~-trans {s = ⟦ (E5.e ʷ) u ⟧PY ∙ ⟦ (E5.e ʷ) v ⟧PY} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} {u = ⟦ u • v ⟧}
      (∙-cong {s = ⟦ (E5.e ʷ) u ⟧PY} {s' = ⟦ u ⟧} {t = ⟦ (E5.e ʷ) v ⟧PY} {t' = ⟦ v ⟧} (eʷ-sem u) (eʷ-sem v))
      (~-sym {s = ⟦ u • v ⟧} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} (hom u v))

  module RS = Star-Injective-Simplified (_XVRel,_===_ 5) (E5.N R,_===_)
  module R  = RS.Reidemeister-Schreier-Simplified E5.e d dwd d∘e₅

-- Two five-wire circuits with the same matrix are equal in the theory
-- with AX.
complete₅ : ∀ {w v : Circuit 5} → ⟦ w ⟧ ~ ⟦ v ⟧ → 5 ⊢ₓ w ≈ v
complete₅ {w} {v} eq =
  R.fʷ-inj (complete-P {(E5.e ʷ) w} {(E5.e ʷ) v}
    (~-trans {s = ⟦ (E5.e ʷ) w ⟧PY} {t = ⟦ w ⟧} {u = ⟦ (E5.e ʷ) v ⟧PY} (eʷ-sem w)
      (~-trans {s = ⟦ w ⟧} {t = ⟦ v ⟧} {u = ⟦ (E5.e ʷ) v ⟧PY} eq
        (~-sym {s = ⟦ (E5.e ʷ) v ⟧PY} {t = ⟦ v ⟧} (eʷ-sem v)))))

-- And the theory is sound.
sound₅ : ∀ {w v : Circuit 5} → 5 ⊢ₓ w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
sound₅ = soundₓ
