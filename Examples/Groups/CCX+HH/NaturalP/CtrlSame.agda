------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled circuits with the same matrix.
--
-- ctrl₁ C acts as C one wire up controlled by wire 0, at every width
-- (`ctrl₁-sem`: CTRL₁ is never degenerate), and ctrl C as C controlled
-- by wire 0 from four wires on (CtrlSem.ctrl-sem).  So both send
-- circuits with the same matrix to circuits with the same matrix
-- (`ctrl-same`, `ctrl₁-same`), and a NaturalP derivation to an
-- equation of matrices (`soundᴾ`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.CtrlSame where

open import Data.Nat.Base using (ℕ ; suc ; _^_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₂₊ ; ₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-cong ; parallel-id ; parallel-compose)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.Natural.Soundness as NS
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; interpret ; τ-≈)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSem using (CTRL₁-sem ; ctrl-sem)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (ctrlA)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics
  using (action⇒matrix ; matrix⇒action)

private
  variable
    n m : ℕ

-- A NaturalP derivation is an equation of matrices.
soundᴾ : ∀ {u v : P.Circuit n} → n P.⊢ u ≈ v → interpret u ≡ interpret v
soundᴾ p = NS.sound (τ-≈ p)

------------------------------------------------------------------------
-- The action of ctrl₁

ctrl₁-sem : (C : P.Circuit m) → ∀ v →
  quantum (τ (ctrl₁ C)) v ≡ ctrlA (2 ^ suc m) (Q.bottom {m} (quantum (τ C))) v
ctrl₁-sem [ g ]ʷ = CTRL₁-sem g
ctrl₁-sem {m} ε v = sym (trans
  (parallel-cong (alternating (2 ^ suc m))
    {f = λ x → x} {f′ = λ x → x}
    {g = Q.bottom {m} (λ x → x)} {g′ = λ x → x}
    (λ _ → refl) (parallel-id (alternating (2 ^ m))) v)
  (parallel-id (alternating (2 ^ suc m)) v))
ctrl₁-sem {m} (u • w) v =
  trans (cong (quantum (τ (ctrl₁ u))) (ctrl₁-sem w v))
  (trans (ctrl₁-sem u (ctrlA (2 ^ suc m) (Q.bottom {m} (quantum (τ w))) v))
  (trans (parallel-compose (alternating (2 ^ suc m))
            (λ x → x) (Q.bottom {m} (quantum (τ u)))
            (λ x → x) (Q.bottom {m} (quantum (τ w))) v)
    (parallel-cong (alternating (2 ^ suc m))
      {f = λ x → x} {f′ = λ x → x}
      {g = λ x → Q.bottom {m} (quantum (τ u)) (Q.bottom {m} (quantum (τ w)) x)}
      {g′ = Q.bottom {m} (λ x → quantum (τ u) (quantum (τ w) x))}
      (λ _ → refl)
      (parallel-compose (alternating (2 ^ m))
        (quantum (τ u)) (quantum (τ u)) (quantum (τ w)) (quantum (τ w))) v)))

------------------------------------------------------------------------
-- The same matrix

ctrl₁-same : (u v : P.Circuit m) → interpret u ≡ interpret v →
  interpret (ctrl₁ u) ≡ interpret (ctrl₁ v)
ctrl₁-same {m} u v e = action⇒matrix {u = τ (ctrl₁ u)} {v = τ (ctrl₁ v)} λ x →
  trans (ctrl₁-sem u x)
  (trans (parallel-cong (alternating (2 ^ suc m))
            {f = λ y → y} {f′ = λ y → y}
            {g = Q.bottom {m} (quantum (τ u))} {g′ = Q.bottom {m} (quantum (τ v))}
            (λ _ → refl)
            (parallel-cong (alternating (2 ^ m))
              {f = quantum (τ u)} {f′ = quantum (τ v)}
              {g = quantum (τ u)} {g′ = quantum (τ v)}
              (matrix⇒action {u = τ u} {v = τ v} e)
              (matrix⇒action {u = τ u} {v = τ v} e)) x)
    (sym (ctrl₁-sem v x)))

ctrl-same : (u v : P.Circuit (₄₊ n)) → interpret u ≡ interpret v →
  interpret (ctrl u) ≡ interpret (ctrl v)
ctrl-same {n} u v e = action⇒matrix {u = τ (ctrl u)} {v = τ (ctrl v)} λ x →
  trans (ctrl-sem u x)
  (trans (parallel-cong (alternating (2 ^ ₄₊ n))
            {f = λ y → y} {f′ = λ y → y}
            {g = quantum (τ u)} {g′ = quantum (τ v)}
            (λ _ → refl) (matrix⇒action {u = τ u} {v = τ v} e) x)
    (sym (ctrl-sem v x)))
