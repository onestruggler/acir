------------------------------------------------------------------------
-- Presentations of groups
--
-- Adding an idle wire at either end is the independent parallel action
-- on its two Boolean branches, for every circuit and state vector.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.ShiftSemantics where

open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_^_ to _^ℕ_)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as E
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as P
import Examples.Groups.CCX+H.GeneralN.ActionSemantics as A
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Dyadic
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2

private
  module D = Dyadic {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½
  module B = Blocks {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½
  module I = Interchange {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½

gate-correct : ∀ {n} (g : Gen n) v →
  S.gate-action (g ↥) v ≡ D.bottom {n} (S.gate-action g) v
gate-correct {zero} g v with E.classify g
... | inj₁ dg = refl
... | inj₂ ()
gate-correct {suc n} g v with E.classify g
... | inj₁ dg = refl
... | inj₂ p = refl

correct : ∀ {n} (w : Circuit n) v →
  S.action (w ↑) v ≡ D.bottom {n} (S.action w) v
correct [ g ]ʷ = gate-correct g
correct {n} ε v = sym (B.parallel-id (alternating (2 ^ℕ n)) v)
correct {n} (u • w) v = trans (correct u (S.action (w ↑) v))
  (trans (cong (D.bottom {n} (S.action u)) (correct w v))
    (B.parallel-compose (alternating (2 ^ℕ n))
      (S.action u) (S.action u) (S.action w) (S.action w) v))

cong↑ : ∀ {n} {u w : Circuit n} → P.interpret u ≡ P.interpret w →
  P.interpret (u ↑) ≡ P.interpret (w ↑)
cong↑ {n} {u} {w} eq = A.action⇒matrix {u = u ↑} {w = w ↑} λ v →
  trans (correct u v)
    (trans (B.parallel-cong (alternating (2 ^ℕ n))
      (A.matrix⇒action {u = u} {w = w} eq)
      (A.matrix⇒action {u = u} {w = w} eq) v) (sym (correct w v)))

gate-top : ∀ {n} (g : Gen n) v →
  S.gate-action (g ↧) v ≡ D.top {n} (S.gate-action g) v
gate-top (gate₀ ()) v
gate-top (gate₁ X-gate) v = refl
gate-top (gate₁ H-gate) v = refl
gate-top (gate₂ CX-gate) v = refl
gate-top (gate₃ CCX-gate) v = refl
gate-top (_↥ {n} g) v = trans (gate-correct (g ↧) v)
  (trans (B.parallel-cong (alternating (2 ^ℕ suc n)) (gate-top g) (gate-top g) v)
    (trans (sym (I.top-bottom (2 ^ℕ n) (S.gate-action g) v))
      (B.parallel-cong (contiguous (2 ^ℕ suc n))
        (λ z → sym (gate-correct g z)) (λ z → sym (gate-correct g z)) v)))

top-correct : ∀ {n} (w : Circuit n) v →
  S.action (w ⇓) v ≡ D.top {n} (S.action w) v
top-correct [ g ]ʷ = gate-top g
top-correct {n} ε v = sym (B.parallel-id (contiguous (2 ^ℕ n)) v)
top-correct {n} (u • w) v = trans (top-correct u (S.action (w ⇓) v))
  (trans (cong (D.top {n} (S.action u)) (top-correct w v))
    (B.parallel-compose (contiguous (2 ^ℕ n))
      (S.action u) (S.action u) (S.action w) (S.action w) v))

cong⇓ : ∀ {n} {u w : Circuit n} → P.interpret u ≡ P.interpret w →
  P.interpret (u ⇓) ≡ P.interpret (w ⇓)
cong⇓ {n} {u} {w} eq = A.action⇒matrix {u = u ⇓} {w = w ⇓} λ v →
  trans (top-correct u v)
    (trans (B.parallel-cong (contiguous (2 ^ℕ n))
      (A.matrix⇒action {u = u} {w = w} eq)
      (A.matrix⇒action {u = u} {w = w} eq) v) (sym (top-correct w v)))
