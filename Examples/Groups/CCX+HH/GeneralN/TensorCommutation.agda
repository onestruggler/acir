------------------------------------------------------------------------
-- Presentations of groups
--
-- Disjoint tensor factors commute, transferred through the faithful
-- physical HH-to-H expansion.  No circuit relation is assumed here.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.TensorCommutation where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; _•_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as E
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as P
import Examples.Groups.CCX+H.GeneralN.ActionSemantics as A
import Examples.Groups.CCX+H.GeneralN.ShiftSemantics as Shift
import Examples.Groups.CCX+H.GeneralN.TensorCommutation as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD ; AdjointD)

private
  shift₂ : ∀ {n} (w : Circuit n) → E.embed ((w ↑) ↑) ≡ ((E.embed w H.↑) H.↑)
  shift₂ w = trans (E.embed-shift (w ↑)) (cong (λ z → z H.↑) (E.embed-shift w))

  shift₃ : ∀ {n} (w : Circuit n) → E.embed (((w ↑) ↑) ↑) ≡ (((E.embed w H.↑) H.↑) H.↑)
  shift₃ w = trans (E.embed-shift ((w ↑) ↑)) (cong (λ z → z H.↑) (shift₂ w))

  transfer : ∀ {n} (u v : Circuit n) {a b : H.Circuit n} → E.embed u ≡ a → E.embed v ≡ b →
    P.interpret (a • b) ≡ P.interpret (b • a) → Q.interpret (u • v) ≡ Q.interpret (v • u)
  transfer u v ea eb eq = E.reflect {u = u • v} {v = v • u}
    (trans (cong P.interpret (cong₂ _•_ ea eb))
      (trans eq (sym (cong P.interpret (cong₂ _•_ eb ea)))))

  hcomm₁ : ∀ {n} (w : H.Circuit n) (h : H.Gate 1) →
    P.interpret ((w H.↑) • [ H.gate₁ h ]ʷ) ≡ P.interpret ([ H.gate₁ h ]ʷ • (w H.↑))
  hcomm₁ w h = A.action⇒matrix
    {u = (w H.↑) • [ H.gate₁ h ]ʷ} {w = [ H.gate₁ h ]ʷ • (w H.↑)} (T.comm₁ w h)

  hcomm₂ : ∀ {n} (w : H.Circuit n) (h : H.Gate 2) →
    P.interpret (((w H.↑) H.↑) • [ H.gate₂ h ]ʷ) ≡
      P.interpret ([ H.gate₂ h ]ʷ • ((w H.↑) H.↑))
  hcomm₂ w h = A.action⇒matrix
    {u = ((w H.↑) H.↑) • [ H.gate₂ h ]ʷ} {w = [ H.gate₂ h ]ʷ • ((w H.↑) H.↑)} (T.comm₂ w h)

  hcomm₃ : ∀ {n} (w : H.Circuit n) (h : H.Gate 3) →
    P.interpret ((((w H.↑) H.↑) H.↑) • [ H.gate₃ h ]ʷ) ≡
      P.interpret ([ H.gate₃ h ]ʷ • (((w H.↑) H.↑) H.↑))
  hcomm₃ w h = A.action⇒matrix
    {u = (((w H.↑) H.↑) H.↑) • [ H.gate₃ h ]ʷ}
    {w = [ H.gate₃ h ]ʷ • (((w H.↑) H.↑) H.↑)} (T.comm₃ w h)

  hcomm-HH : ∀ {n} (w : H.Circuit n) →
    P.interpret (((w H.↑) H.↑) • ((H.H H.↑) • H.H)) ≡
    P.interpret (((H.H H.↑) • H.H) • ((w H.↑) H.↑))
  hcomm-HH {n} w = trans (sym (M.·*·-assoc a b c))
    (trans (cong (_·*· c) left)
      (trans (M.·*·-assoc b a c)
        (trans (cong (b ·*·_) right) (sym (M.·*·-assoc b c a)))))
    where
    a = P.interpret ((w H.↑) H.↑)
    b = P.interpret (H.H {n} H.↑)
    c = P.interpret (H.H {suc n})
    left : a ·*· b ≡ b ·*· a
    left = Shift.cong↑
      {u = (w H.↑) • H.H} {w = H.H • (w H.↑)} (hcomm₁ w H.H-gate)
    right : a ·*· c ≡ c ·*· a
    right = hcomm₁ (w H.↑) H.H-gate

comm₁ : ∀ {n} (w : Circuit n) (h : Gate 1) →
  Q.interpret ((w ↑) • [ gate₁ h ]ʷ) ≡ Q.interpret ([ gate₁ h ]ʷ • (w ↑))
comm₁ w X-gate = transfer (w ↑) X (E.embed-shift w) refl (hcomm₁ (E.embed w) H.X-gate)

comm₂ : ∀ {n} (w : Circuit n) (h : Gate 2) →
  Q.interpret (((w ↑) ↑) • [ gate₂ h ]ʷ) ≡ Q.interpret ([ gate₂ h ]ʷ • ((w ↑) ↑))
comm₂ w CX-gate = transfer ((w ↑) ↑) CX (shift₂ w) refl (hcomm₂ (E.embed w) H.CX-gate)
comm₂ w HH-gate = transfer ((w ↑) ↑) HH (shift₂ w) refl (hcomm-HH (E.embed w))

comm₃ : ∀ {n} (w : Circuit n) (h : Gate 3) →
  Q.interpret ((((w ↑) ↑) ↑) • [ gate₃ h ]ʷ) ≡ Q.interpret ([ gate₃ h ]ʷ • (((w ↑) ↑) ↑))
comm₃ w CCX-gate = transfer (((w ↑) ↑) ↑) CCX (shift₃ w) refl (hcomm₃ (E.embed w) H.CCX-gate)
