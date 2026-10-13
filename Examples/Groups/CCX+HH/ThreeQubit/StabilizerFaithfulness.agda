------------------------------------------------------------------------
-- Presentations of groups
--
-- Even signed-permutation normal forms are separated by Table 1.
-- A single vector with eight distinct positive coordinate tags recovers
-- both the eight signs and the underlying permutation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.StabilizerFaithfulness where

open import Data.Bool.Base using (false ; true ; _xor_)
import Data.Bool.Properties as BP
open import Data.Product.Base using (_×_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; _∷_ ; tail ; lookup ; tabulate)
import Data.Vec.Properties as VP
open import Relation.Nullary.Decidable using (recompute)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (_ʷ)
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm as NF
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerAction as Action
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (b)
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerTags using (tag ; signed-tag-injective)
import Examples.Groups.CCX+HH.ThreeQubit.QuarticInvariant as Invariant
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
import Examples.Groups.Symmetric.Syntactics as Sym
import Examples.Groups.Symmetric.Normalization as SN
import Examples.Groups.Symmetric.SubPresentation.Semantics as PS
import Examples.Groups.Symmetric.SubPresentation.UniqueNormalForm as Unique
import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Presentation.Base as PB

private
  module U = NFU (Sym._VRel,_===_ 8) (SN.NF 8) (PS.Endo-setoid 8) PS.⟦_⟧

  vec-ext : ∀ {A : Set} {n} {u v : Vec A n} →
    (∀ i → lookup u i ≡ lookup v i) → u ≡ v
  vec-ext {u = u} {v} eq = Eq.trans (Eq.sym (VP.tabulate∘lookup u))
    (Eq.trans (VP.tabulate-cong eq) (VP.tabulate∘lookup v))

  xor-false : ∀ a b → a xor b ≡ false → a ≡ b
  xor-false false false _ = refl
  xor-false false true ()
  xor-false true false ()
  xor-false true true _ = refl

  even-tail : ∀ n → NF.signs n ≡ NF.parity (tail (NF.signs n)) ∷ tail (NF.signs n)
  even-tail (NF.state (a ∷ s) p ev) = Eq.cong (_∷ s)
    (xor-false a (NF.parity s) (recompute ((a xor NF.parity s) BP.≟ false) ev))

  phase-image : ∀ n z →
    S.actVʷ ((b ʷ) (NF.phase-word (λ i → i) (tail (NF.signs n)))) z ≡
    Action.apply (NF.signs n) z
  phase-image n z = Eq.trans (Action.phases (tail (NF.signs n)) z)
    (Eq.cong (λ s → Action.apply s z) (Eq.sym (even-tail n)))

section-action : ∀ n (v : Vec D 8) i →
  lookup (S.actVʷ ((b ʷ) (NF.section n)) v) i ≡
  Action.neg (lookup (NF.signs n) i)
    (lookup v (PS.⟦ SN.inv-nf (NF.permutation n) ⟧ i))
section-action n v i = Eq.trans
  (Eq.cong (λ z → lookup z i)
    (phase-image n (S.actVʷ ((b ʷ) (NF.permutation-word (NF.permutation n))) v)))
  (Eq.trans (VP.lookup-zipWith Action.neg i (NF.signs n)
    (S.actVʷ ((b ʷ) (NF.permutation-word (NF.permutation n))) v))
    (Eq.cong (Action.neg (lookup (NF.signs n) i))
      (Action.permutation-action (SN.inv-nf (NF.permutation n)) v i)))

private
  tagged : ∀ n i →
    lookup (S.actVʷ ((b ʷ) (NF.section n)) (tabulate tag)) i ≡
    Action.neg (lookup (NF.signs n) i) (tag (PS.⟦ SN.inv-nf (NF.permutation n) ⟧ i))
  tagged n i = Eq.trans (section-action n (tabulate tag) i)
    (Eq.cong (Action.neg (lookup (NF.signs n) i))
      (VP.lookup∘tabulate tag (PS.⟦ SN.inv-nf (NF.permutation n) ⟧ i)))

separate : ∀ {n m} → PB._≈_ (T._===_ {8})
  ((b ʷ) (NF.section n)) ((b ʷ) (NF.section m)) → n ≡ m
separate {n@(NF.state s p es)} {m@(NF.state t q et)} eq =
  NF.state-cong
    {ep = recompute (NF.parity s BP.≟ false) es}
    {eq = recompute (NF.parity t BP.≟ false) et}
    (vec-ext λ i → proj₁ (entries i))
    (U.UniqueNormalForm.unique (Unique.unique-nf 8) (λ i → proj₂ (entries i)))
  where
  entries : ∀ i → (lookup s i ≡ lookup t i) ×
    (PS.⟦ SN.inv-nf p ⟧ i ≡ PS.⟦ SN.inv-nf q ⟧ i)
  entries i = signed-tag-injective (lookup s i) (lookup t i)
    (PS.⟦ SN.inv-nf p ⟧ i) (PS.⟦ SN.inv-nf q ⟧ i)
    (Eq.trans (Eq.sym (tagged n i))
      (Eq.trans (Eq.cong (λ z → lookup z i) (Invariant.actV-cong eq (tabulate tag)))
        (tagged m i)))
