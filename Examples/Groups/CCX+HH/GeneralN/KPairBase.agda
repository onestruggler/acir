------------------------------------------------------------------------
-- Presentations of groups
--
-- Two localized disjoint Hadamard blocks in every width at least four.
-- With S=M0 M4, P=X12 X56 and Q=physical HH, S Q S Q S P is K0123 K4567.
-- The eight-level calculation lifts with identity on every other level.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.KPairBase (n : ℕ) where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Nat.Base using (suc ; _^_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Word.Base using (Word ; _•_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.CCX+HH.GeneralN.LocalEight as L
import Examples.Groups.CCX+HH.GeneralN.DoubleExchange as DE
import Examples.Groups.CCX+H.GeneralN.SignPair as SP
open import Examples.Groups.CCX+HH.GeneralN.PhysicalEquality using (matrix⇒action ; action⇒matrix)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)

width = suc (suc (suc (suc n)))
m = suc n

level : Fin 8 → Fin (2 ^ width)
level = L.level m
increasing : ∀ {i j} → i < j → level i < level j
increasing = L.level-increasing m

private
  s p hsh w target : Word (T.Gen 8)
  s = T.M ₀ • T.M ₄
  p = T.X ₁ ₂ (s≤s (s≤s z≤n)) • T.X ₅ ₆ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
  hsh = E.HH-block 1 • s • E.HH-block 1
  w = s • hsh • s • p
  target = T.K ₀ ₁ ₂ ₃ (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) •
    T.K ₄ ₅ ₆ ₇ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

  opaque
    unfolding A.actV A.set₁ A.set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

    base : A.⟦ w ⟧ᵐ ≡ A.⟦ target ⟧ᵐ
    base = refl

  module Sign = SP n
  module Pair = DE.Pair n (level ₁) (level ₂) (level ₅) (level ₆)
    (increasing (s≤s (s≤s z≤n))) (increasing (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

  s-word : L.localized m s ≡ T.M (level ₀) • T.M (level ₄)
  s-word = trans (L.localized-• m _ _) (cong₂ _•_ (L.localized-M m ₀) (L.localized-M m ₄))
  p-word : L.localized m p ≡ Pair.auxiliary
  p-word = trans (L.localized-• m _ _)
    (cong₂ _•_ (L.localized-X m ₁ ₂ (s≤s (s≤s z≤n)))
      (L.localized-X m ₅ ₆ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

  S = Sign.circuit (level ₀) (level ₄)
  P = Pair.circuit
  HSH = H.HH • S • H.HH

  s-correct : Q.interpret S ≡ A.⟦ L.localized m s ⟧ᵐ
  s-correct = trans (Sign.correct (level ₀) (level ₄)) (cong A.⟦_⟧ᵐ (sym s-word))
  p-correct : Q.interpret P ≡ A.⟦ L.localized m p ⟧ᵐ
  p-correct = trans Pair.correct (cong A.⟦_⟧ᵐ (sym p-word))
  hsh-action : ∀ v → quantum HSH v ≡ A.actVʷ (L.localized m hsh) v
  hsh-action v = trans (cong (Q.hh (suc m))
      (matrix⇒action S (L.localized m s) s-correct (Q.hh (suc m) v)))
    (L.conjugate-word m s hsh refl v)
  hsh-correct : Q.interpret HSH ≡ A.⟦ L.localized m hsh ⟧ᵐ
  hsh-correct = action⇒matrix HSH (L.localized m hsh) hsh-action

  product : ∀ (u v : H.Circuit width) (a b : Word (T.Gen (2 ^ width))) →
    Q.interpret u ≡ A.⟦ a ⟧ᵐ → Q.interpret v ≡ A.⟦ b ⟧ᵐ →
    Q.interpret (u • v) ≡ A.⟦ a • b ⟧ᵐ
  product u v a b eq eq′ = trans (cong₂ _·*·_ eq eq′) (sym (A.⟦•⟧ᵐ a b))

circuit : H.Circuit width
circuit = S • HSH • S • P

auxiliary : Word (T.Gen (2 ^ width))
auxiliary = T.K (level ₀) (level ₁) (level ₂) (level ₃)
    (increasing (s≤s z≤n)) (increasing (s≤s (s≤s z≤n))) (increasing (s≤s (s≤s (s≤s z≤n)))) •
  T.K (level ₄) (level ₅) (level ₆) (level ₇)
    (increasing (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
    (increasing (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    (increasing (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

private
  w-word : L.localized m w ≡ L.localized m s • L.localized m hsh • L.localized m s • L.localized m p
  w-word = trans (L.localized-• m s (hsh • s • p))
    (cong (L.localized m s •_) (trans (L.localized-• m hsh (s • p))
      (cong (L.localized m hsh •_) (L.localized-• m s p))))
  target-word : L.localized m target ≡ auxiliary
  target-word = trans (L.localized-• m _ _)
    (cong₂ _•_ (L.localized-K m ₀ ₁ ₂ ₃ (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))))
      (L.localized-K m ₄ ₅ ₆ ₇ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
        (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
        (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

  localized-base : A.⟦ L.localized m w ⟧ᵐ ≡ A.⟦ L.localized m target ⟧ᵐ
  localized-base = A.same-matrix (L.localized m w) (L.localized m target) λ v →
    trans (L.local-action m w v)
      (trans (L.local-cong m (A.same-action w target base) v) (sym (L.local-action m target v)))

correct : Q.interpret circuit ≡ A.⟦ auxiliary ⟧ᵐ
correct = trans
  (product S (HSH • S • P) (L.localized m s) (L.localized m hsh • L.localized m s • L.localized m p) s-correct
    (product HSH (S • P) (L.localized m hsh) (L.localized m s • L.localized m p) hsh-correct
      (product S P (L.localized m s) (L.localized m p) s-correct p-correct)))
  (trans (cong A.⟦_⟧ᵐ (sym w-word)) (trans localized-base (cong A.⟦_⟧ᵐ target-word)))
