------------------------------------------------------------------------
-- Presentations of groups
--
-- The compact rules derive every step of the finite signed-permutation
-- normal form.  This reduces the large finite base table to 105 rules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Compact.Normalization where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
import Data.Bool.Properties as BP
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tail)
open import Relation.Nullary.Decidable using (recompute)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Notations
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (phase ; exchange)
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm as NF
open import Examples.Groups.CCX+HH.ThreeQubit.Compact.Syntactics
open import Examples.Groups.CCX+HH.ThreeQubit.Compact.Diagonal
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Action as Action
import Examples.Groups.Symmetric.Syntactics as Sym
import Examples.Groups.Symmetric.Normalization as SN
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

private
  module R = PB _===_
  module Q = PP _===_
  module SP = PB (Sym._VRel,_===_ 8)

permutation-lift : ∀ {u v} → u SP.≈ v → permutation u ≈ permutation v
permutation-lift = PP.GenCongruence.fʷ-cong (Sym._VRel,_===_ 8) _===_
  (λ g → exchange (NF.position g)) (λ ax → R.axiom (symmetric ax))

private
  position-adjacent : (i : Fin 7) → NF.position (NF.adjacent i) ≡ i
  position-adjacent ₀ = refl
  position-adjacent ₁ = refl
  position-adjacent ₂ = refl
  position-adjacent ₃ = refl
  position-adjacent ₄ = refl
  position-adjacent ₅ = refl
  position-adjacent ₆ = refl

  toggle-correct : ∀ {n} (i : Fin n) s → Diagonal.toggle i s ≡ NF.toggle i s
  toggle-correct zero (a ∷ s) = refl
  toggle-correct (suc i) (a ∷ s) = Eq.cong (a ∷_) (toggle-correct i s)

  xor-false : ∀ a b → a xor b ≡ false → a ≡ b
  xor-false false false _ = refl
  xor-false false true ()
  xor-false true false ()
  xor-false true true _ = refl

  even-tail : ∀ n → NF.signs n ≡ NF.parity (tail (NF.signs n)) ∷ tail (NF.signs n)
  even-tail (NF.state (a ∷ s) p ev) = Eq.cong (_∷ s)
    (xor-false a (NF.parity s) (recompute ((a xor NF.parity s) BP.≟ false) ev))

module _ where
  open SR Q.word-setoid hiding (start)

  cross-word : ∀ i w → X i • (P ʷ) w ≈ (P ʷ) ((conjugate i ʷ) w) • X i
  cross-word i [ j ]ʷ = R.axiom (cross i j)
  cross-word i ε = R.trans R.right-unit (R.sym R.left-unit)
  cross-word i (u • v) = begin
    X i • ((P ʷ) u • (P ʷ) v) ≈⟨ R.sym R.assoc ⟩
    (X i • (P ʷ) u) • (P ʷ) v ≈⟨ R.cong (cross-word i u) R.refl ⟩
    ((P ʷ) ((conjugate i ʷ) u) • X i) • (P ʷ) v ≈⟨ R.assoc ⟩
    (P ʷ) ((conjugate i ʷ) u) • (X i • (P ʷ) v)
      ≈⟨ R.cong R.refl (cross-word i v) ⟩
    (P ʷ) ((conjugate i ʷ) u) • ((P ʷ) ((conjugate i ʷ) v) • X i)
      ≈⟨ R.sym R.assoc ⟩
    (P ʷ) ((conjugate i ʷ) (u • v)) • X i ∎

  phase-insert : ∀ i s → P i • NF.phase-word (λ j → j) s ≈
    NF.phase-word (λ j → j) (NF.toggle i s)
  phase-insert i s = begin
    P i • NF.phase-word (λ j → j) s
      ≈⟨ R.cong R.refl (R.refl' (Eq.sym (section-correct (λ j → j) s))) ⟩
    P i • Diagonal.section (λ j → j) s ≈⟨ Diagonal.insert (λ j → j) i s ⟩
    Diagonal.section (λ j → j) (Diagonal.toggle i s)
      ≈⟨ R.refl' (Eq.trans (section-correct (λ j → j) (Diagonal.toggle i s))
           (Eq.cong (NF.phase-word (λ j → j)) (toggle-correct i s))) ⟩
    NF.phase-word (λ j → j) (NF.toggle i s) ∎

  phase-conjugation : ∀ i s → X i • NF.phase-word (λ j → j) s ≈
    NF.phase-word (λ j → j) (permuted i s) • X i
  phase-conjugation i s = begin
    X i • NF.phase-word (λ j → j) s
      ≈⟨ R.cong R.refl (R.refl' (Eq.sym (plan-correct (λ j → j) s))) ⟩
    X i • (P ʷ) (plan (λ j → j) s) ≈⟨ cross-word i (plan (λ j → j) s) ⟩
    (P ʷ) ((conjugate i ʷ) (plan (λ j → j) s)) • X i
      ≈⟨ R.cong (Diagonal.normalize ((conjugate i ʷ) (plan (λ j → j) s))) R.refl ⟩
    Diagonal.section (λ j → j) (transformed i s) • X i
      ≈⟨ R.cong (R.refl' (Eq.trans
           (Eq.cong (Diagonal.section (λ j → j)) (Action.checked i s))
           (section-correct (λ j → j) (permuted i s)))) R.refl ⟩
    NF.phase-word (λ j → j) (permuted i s) • X i ∎

  signed-conjugation : ∀ i n → X i • NF.phase-word (λ j → j) (tail (NF.signs n)) ≈
    NF.phase-word (λ j → j) (tail (NF.swap i (NF.signs n))) • X i
  signed-conjugation i n = R.trans (phase-conjugation i (tail (NF.signs n)))
    (R.refl' (Eq.cong (λ s → NF.phase-word (λ j → j) (tail (NF.swap i s)) • X i)
      (Eq.sym (even-tail n))))

  permutation-step : ∀ i p → X i • NF.permutation-word p ≈
    NF.permutation-word (SN.nf-of ([ NF.adjacent i ]ʷ • SN.inv-nf p))
  permutation-step i p = R.trans
    (R.cong (R.refl' (Eq.cong X (Eq.sym (position-adjacent i)))) R.refl)
    (permutation-lift (SP.sym (SN.inv-nf∘nf≈id 8
      {w = [ NF.adjacent i ]ʷ • SN.inv-nf p})))

  phase-step : ∀ i n → P i • NF.section n ≈ NF.section (NF.step (phase i) n)
  phase-step i (NF.state (a ∷ s) p ev) =
    R.trans (R.sym R.assoc) (R.cong (phase-insert i s) R.refl)

  exchange-step : ∀ i n → X i • NF.section n ≈ NF.section (NF.step (exchange i) n)
  exchange-step i n@(NF.state s p ev) = begin
    X i • (NF.phase-word (λ j → j) (tail s) • NF.permutation-word p)
      ≈⟨ R.sym R.assoc ⟩
    (X i • NF.phase-word (λ j → j) (tail s)) • NF.permutation-word p
      ≈⟨ R.cong (signed-conjugation i n) R.refl ⟩
    (NF.phase-word (λ j → j) (tail (NF.swap i s)) • X i) • NF.permutation-word p
      ≈⟨ R.assoc ⟩
    NF.phase-word (λ j → j) (tail (NF.swap i s)) • (X i • NF.permutation-word p)
      ≈⟨ R.cong R.refl (permutation-step i p) ⟩
    NF.section (NF.step (exchange i) n) ∎

initial : NF.section NF.I ≈ ε
initial = R.trans R.left-unit (permutation-lift (SN.inv-nf∘nf≈id 8 {w = ε}))

factor : ∀ g n → [ g ]ʷ • NF.section n ≈ NF.section (NF.step g n)
factor (phase i) = phase-step i
factor (exchange i) = exchange-step i
