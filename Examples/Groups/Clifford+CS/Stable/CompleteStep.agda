------------------------------------------------------------------------
-- Presentations of groups
--
-- The step of the induction on the width, given Lemma 8.7
--
-- Five.Complete5's back-and-forth argument at 5 + m wires in the Stable
-- theory: the encoding into P′ (Encoding, with its semantics Section8.
-- e-sem), completeness of P′ (BridgeGray.Complete, from Theorem410),
-- the decoding of letters `DWDGen.dl` with Lemma 8.8 `DWDGen.dwd` from
-- completeness on 4 + m, and Lemma 8.7 — `[ g ]ʷ ≈ (dl ʷ) (e g)` on
-- 5 + m wires, which cannot go by semantics at its own width — as a
-- hypothesis, give completeness on 5 + m (`complete-step`), by
-- Reidemeister–Schreier.  For Lemma 8.7 it is enough that a gate be the
-- decoding of some word over P′ (`by-decodes`, Five.Complete5's, with
-- DWDGen.dʷ-sem and d-≈).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.CompleteStep
  (c4 : Complete 4) (c₅ : Completeᵧ 5)
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
open import Normalization.Reidemeister-Schreier using (module Star-Injective-Simplified)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; up ; _≟_)
open import Examples.Groups.Clifford+CS.Syntactics using (Gen)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_)
open import Examples.Groups.Clifford+CS.Stable.Soundness using (soundᵧ)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.Section8 as Section8
import Examples.Groups.Clifford+CS.BridgeGray as BridgeGray
import Examples.Groups.Clifford+CS.Stable.DWDGen as DWDGen

private
  module W = DWDGen c4 c₅ f4 f5 tr F

module _ (m : ℕ) where
  private
    module E  = Encoding (suc m)
    module S8 = Section8 (suc m)
    module BG = BridgeGray (₄₊ (suc m))
    n : ℕ
    n = ₄₊ (suc m)

  open BG using (⟦_⟧PY)
  open BG.Complete E.big using (complete-P)

  private
    eʷ-sem : (w : Circuit n) → ⟦ (E.e ʷ) w ⟧PY ~ ⟦ w ⟧
    eʷ-sem [ g ]ʷ  = S8.e-sem g
    eʷ-sem ε       = ~-sym {s = ⟦_⟧ {n} ε} {t = ε∙} (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {n} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
    eʷ-sem (u • v) =
      ~-trans {s = ⟦ (E.e ʷ) u ⟧PY ∙ ⟦ (E.e ʷ) v ⟧PY} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} {u = ⟦ u • v ⟧}
        (∙-cong {s = ⟦ (E.e ʷ) u ⟧PY} {s' = ⟦ u ⟧} {t = ⟦ (E.e ʷ) v ⟧PY} {t' = ⟦ v ⟧} (eʷ-sem u) (eʷ-sem v))
        (~-sym {s = ⟦ u • v ⟧} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} (hom u v))

  -- A gate that is the decoding of some word over P′ is the decoding of
  -- its encoding: the two words have the same reading, so they are
  -- equal in P′.
  by-decodes : Completeᵧ (₄₊ m) → ∀ (g : Gen n) (w : Word (GenP E.N)) →
               n ⊢ᵧ [ g ]ʷ ≈ (W.dl m ʷ) w → n ⊢ᵧ [ g ]ʷ ≈ (W.dl m ʷ) (E.e g)
  by-decodes c g w h = PB.trans h (W.d-≈ m c (complete-P {w} {E.e g} same))
    where
    same : ⟦ w ⟧PY ~ ⟦ E.e g ⟧PY
    same =
      ~-trans {s = ⟦ w ⟧PY} {t = ⟦ (W.dl m ʷ) w ⟧} {u = ⟦ E.e g ⟧PY}
        (~-sym {s = ⟦ (W.dl m ʷ) w ⟧} {t = ⟦ w ⟧PY} (W.dʷ-sem m w))
        (~-trans {s = ⟦ (W.dl m ʷ) w ⟧} {t = ⟦ [ g ]ʷ ⟧} {u = ⟦ E.e g ⟧PY}
          (soundᵧ (PB.sym h))
          (~-sym {s = ⟦ E.e g ⟧PY} {t = ⟦ [ g ]ʷ ⟧} (S8.e-sem g)))

  -- Lemma 8.7 on 5 + m wires.
  D∘E : Set
  D∘E = ∀ (g : Gen n) → n ⊢ᵧ [ g ]ʷ ≈ (W.dl m ʷ) (E.e g)

  -- Completeness on 5 + m wires, from completeness on 4 + m and
  -- Lemma 8.7 on 5 + m.
  complete-step : Completeᵧ (₄₊ m) → D∘E → Completeᵧ n
  complete-step c d∘e {w} {v} eq =
    R.fʷ-inj (complete-P {(E.e ʷ) w} {(E.e ʷ) v}
      (~-trans {s = ⟦ (E.e ʷ) w ⟧PY} {t = ⟦ w ⟧} {u = ⟦ (E.e ʷ) v ⟧PY} (eʷ-sem w)
        (~-trans {s = ⟦ w ⟧} {t = ⟦ v ⟧} {u = ⟦ (E.e ʷ) v ⟧PY} eq
          (~-sym {s = ⟦ (E.e ʷ) v ⟧PY} {t = ⟦ v ⟧} (eʷ-sem v)))))
    where
    module RS = Star-Injective-Simplified (_YVRel,_===_ n) (E.N R,_===_)
    module R  = RS.Reidemeister-Schreier-Simplified E.e (W.dl m) (W.dwd m c) d∘e
