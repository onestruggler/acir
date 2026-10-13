------------------------------------------------------------------------
-- Presentations of groups
--
-- Route a physical pair of ordered K blocks to any disjoint pair.
-- Two unused target levels absorb the parity of the routing; all
-- physical circuits keep the original width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+H.GeneralN.KPairRouting (n : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; splitAt ; join)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (_≤_ ; s≤s ; z≤n)
import Data.Nat.Properties as NP
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Vec.Base using (tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; _•_)
open import Notations
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; mono ; injective)
import Examples.Groups.CCX+HH.GeneralN.PartialRouting as Routing
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx-cong ; idx-bits)
open import Examples.Groups.CCX+H.GeneralN.SpareLevels using (eight-spares ; module TwoSpares)
import Examples.Groups.CCX+H.GeneralN.PhysicalConjugation as Conjugate

width = 4 + n
Level = Fin (2 ^ width)

private
  emb-inj : ∀ {k} (e : Emb k (2 ^ width)) {i j} → ι e i ≡ ι e j → i ≡ j
  emb-inj e {i} {j} eq with i FP.≟ j
  ... | yes ij = ij
  ... | no ij = ⊥-elim (injective e ij eq)

  ten≤dimension : 10 ≤ 2 ^ width
  ten≤dimension = NP.≤-trans
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
    (NP.^-monoʳ-≤ 2 {4} {4 + n} (NP.m≤m+n 4 n))

  K-cong : ∀ {a b c d a′ b′ c′ d′ : Level}
    .(ab : a < b) .(bc : b < c) .(cd : c < d)
    .(ab′ : a′ < b′) .(bc′ : b′ < c′) .(cd′ : c′ < d′) →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ →
    T.K a b c d ab bc cd ≡ T.K a′ b′ c′ d′ ab′ bc′ cd′
  K-cong ab bc cd ab′ bc′ cd′ refl refl refl refl = refl

record DisjointBlocks : Set where
  field
    first second : Emb 4 (2 ^ width)
    apart : ∀ i j → ι first i ≢ ι second j

  levels : Fin 8 → Level
  levels i = [ ι first , ι second ]′ (splitAt 4 i)

  private
    choice-inj : ∀ {i j : Fin 4 ⊎ Fin 4} →
      [ ι first , ι second ]′ i ≡ [ ι first , ι second ]′ j → i ≡ j
    choice-inj {inj₁ i} {inj₁ j} eq = cong inj₁ (emb-inj first eq)
    choice-inj {inj₂ i} {inj₂ j} eq = cong inj₂ (emb-inj second eq)
    choice-inj {inj₁ i} {inj₂ j} eq = ⊥-elim (apart i j eq)
    choice-inj {inj₂ i} {inj₁ j} eq = ⊥-elim (apart j i (sym eq))

  levels-injective : ∀ {i j} → levels i ≡ levels j → i ≡ j
  levels-injective {i} {j} eq = trans (sym (FP.join-splitAt 4 4 i))
    (trans (cong (join 4 4) (choice-inj {splitAt 4 i} {splitAt 4 j} eq))
      (FP.join-splitAt 4 4 j))

  auxiliary : Word (T.Gen (2 ^ width))
  auxiliary =
    T.K (ι first ₀) (ι first ₁) (ι first ₂) (ι first ₃)
      (mono first (s≤s z≤n)) (mono first (s≤s (s≤s z≤n)))
      (mono first (s≤s (s≤s (s≤s z≤n)))) •
    T.K (ι second ₀) (ι second ₁) (ι second ₂) (ι second ₃)
      (mono second (s≤s z≤n)) (mono second (s≤s (s≤s z≤n)))
      (mono second (s≤s (s≤s (s≤s z≤n))))

module Compile (source : Emb 8 (2 ^ width)) (base : H.Circuit width)
  (base-correct : Q.interpret base ≡ A.⟦
    T.K (ι source ₀) (ι source ₁) (ι source ₂) (ι source ₃)
      (mono source (s≤s z≤n)) (mono source (s≤s (s≤s z≤n)))
      (mono source (s≤s (s≤s (s≤s z≤n)))) •
    T.K (ι source ₄) (ι source ₅) (ι source ₆) (ι source ₇)
      (mono source (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
      (mono source (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
      (mono source (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) ⟧ᵐ)
  (target : DisjointBlocks) where

  private
    module Y = DisjointBlocks target
    module Spare = TwoSpares (eight-spares (tabulate Y.levels) ten≤dimension)
    module R = Routing.Complete n Spare.first Spare.second (FP.<⇒≢ Spare.ordered)
    witness = R.route 8 (ι source) Y.levels (emb-inj source) Y.levels-injective
      (λ i eq → Spare.first-outside i (trans (sym eq) (sym (lookup∘tabulate Y.levels i))))
      (λ i eq → Spare.second-outside i (trans (sym eq) (sym (lookup∘tabulate Y.levels i))))
    module W = Conjugate (R.Route.word witness)

    images : ∀ i → W.forward (ι source i) ≡ Y.levels i
    images i = trans (idx-cong width (R.Route.correct witness i)) (idx-bits width (Y.levels i))

    order : ∀ i j → Y.levels i < Y.levels j →
      W.forward (ι source i) < W.forward (ι source j)
    order i j = subst₂ _<_ (sym (images i)) (sym (images j))

    module K = W.KPair (ι source ₀) (ι source ₁) (ι source ₂) (ι source ₃)
      (ι source ₄) (ι source ₅) (ι source ₆) (ι source ₇)
      (mono source (s≤s z≤n)) (mono source (s≤s (s≤s z≤n)))
      (mono source (s≤s (s≤s (s≤s z≤n))))
      (mono source (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
      (mono source (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
      (mono source (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
      (order ₀ ₁ (mono Y.first (s≤s z≤n)))
      (order ₁ ₂ (mono Y.first (s≤s (s≤s z≤n))))
      (order ₂ ₃ (mono Y.first (s≤s (s≤s (s≤s z≤n)))))
      (order ₄ ₅ (mono Y.second (s≤s z≤n)))
      (order ₅ ₆ (mono Y.second (s≤s (s≤s z≤n))))
      (order ₆ ₇ (mono Y.second (s≤s (s≤s (s≤s z≤n)))))

    word-target : K.target ≡ Y.auxiliary
    word-target = cong₂ _•_
      (K-cong
        (order ₀ ₁ (mono Y.first (s≤s z≤n)))
        (order ₁ ₂ (mono Y.first (s≤s (s≤s z≤n))))
        (order ₂ ₃ (mono Y.first (s≤s (s≤s (s≤s z≤n)))))
        (mono Y.first (s≤s z≤n)) (mono Y.first (s≤s (s≤s z≤n)))
        (mono Y.first (s≤s (s≤s (s≤s z≤n))))
        (images ₀) (images ₁) (images ₂) (images ₃))
      (K-cong
        (order ₄ ₅ (mono Y.second (s≤s z≤n)))
        (order ₅ ₆ (mono Y.second (s≤s (s≤s z≤n))))
        (order ₆ ₇ (mono Y.second (s≤s (s≤s (s≤s z≤n)))))
        (mono Y.second (s≤s z≤n)) (mono Y.second (s≤s (s≤s z≤n)))
        (mono Y.second (s≤s (s≤s (s≤s z≤n))))
        (images ₄) (images ₅) (images ₆) (images ₇))

  circuit : H.Circuit width
  circuit = W.route base

  correct : Q.interpret circuit ≡ A.⟦ Y.auxiliary ⟧ᵐ
  correct = trans (K.correct base base-correct) (cong A.⟦_⟧ᵐ word-target)
