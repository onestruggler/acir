------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits under several controls, as vector operators.
--
-- opΛ s G acts by G on the block of the coordinates whose bottom bits
-- match the pattern s, and by the identity on the others: a black
-- control runs the rest on its odd coordinates, a white one on its even
-- coordinates, and an idle wire on both.  Λ s w acts as opΛ s applied to
-- the action of w (`Λ-sem`), from four wires on.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.LambdaSem where

open import Data.Bool.Base using (true ; false)
open import Data.Maybe.Base using (just ; nothing)
open import Data.Nat.Base using (ℕ ; suc ; _+_ ; _^_ ; _*_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-cong)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; τ-↑)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl ; ctrl⁻)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSem using (ctrl-sem)
open import Examples.Groups.CCX+HH.NaturalP.ColourSem using (ctrl⁻-sem)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Pos ; ctrlᵖ ; Λ)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (Op ; ctrlA)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; quantum-shift)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P

private
  variable
    k c : ℕ

-- One position, as an operator.
opᵖ : Pos → (M : ℕ) → Op M → Op (2 * M)
opᵖ (just true)  M G = ctrlA M G
opᵖ (just false) M G = parallel (alternating M) G (λ x → x)
opᵖ nothing      M G = parallel (alternating M) G G

-- A pattern, as an operator.
opΛ : Vec Pos k → ∀ c → Op (2 ^ ₄₊ c) → Op (2 ^ ₄₊ (k + c))
opΛ []      c G = G
opΛ {suc k} (p ∷ s) c G = opᵖ p (2 ^ ₄₊ (k + c)) (opΛ s c G)

opᵖ-cong : ∀ p M {G G′ : Op M} → (∀ x → G x ≡ G′ x) → ∀ v → opᵖ p M G v ≡ opᵖ p M G′ v
opᵖ-cong (just true)  M e v =
  parallel-cong (alternating M) {f = λ x → x} {f′ = λ x → x} (λ _ → refl) e v
opᵖ-cong (just false) M e v =
  parallel-cong (alternating M) {g = λ x → x} {g′ = λ x → x} e (λ _ → refl) v
opᵖ-cong nothing      M e v = parallel-cong (alternating M) e e v

-- One position, on circuits.
ctrlᵖ-sem : ∀ p (C : P.Circuit (₄₊ c)) → ∀ v →
  quantum (τ (ctrlᵖ p C)) v ≡ opᵖ p (2 ^ ₄₊ c) (quantum (τ C)) v
ctrlᵖ-sem (just true)  C v = ctrl-sem C v
ctrlᵖ-sem (just false) C v = ctrl⁻-sem C v
ctrlᵖ-sem nothing      C v =
  trans (cong (λ u → quantum u v) (τ-↑ C)) (quantum-shift (τ C) v)

Λ-sem : ∀ (s : Vec Pos k) (w : P.Circuit (₄₊ c)) → ∀ v →
  quantum (τ (Λ s w)) v ≡ opΛ s c (quantum (τ w)) v
Λ-sem []      w v = refl
Λ-sem {suc k} {c} (p ∷ s) w v =
  trans (ctrlᵖ-sem p (Λ s w) v)
    (opᵖ-cong p (2 ^ ₄₊ (k + c)) (Λ-sem s w) v)
