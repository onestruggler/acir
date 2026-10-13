------------------------------------------------------------------------
-- Presentations of groups
--
-- A borrowed-bit commutator, with no assumption on the borrowed input.
-- The control predicates P and Q inspect neither the target nor the
-- borrowed wire.  A toggles the borrowed bit by P; B toggles the target
-- by borrowed AND Q.  A B A B toggles the target by P AND Q and restores
-- every other wire.  Equality is pointwise, so no extensionality axiom
-- is needed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Examples.Groups.CCX+HH.GeneralN.BorrowedBit
  (Wire : Set) (_≟_ : DecidableEquality Wire) where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_ ; _∧_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl ; cong ; cong₂ ; sym ; trans)
open import Relation.Nullary.Decidable using (Dec ; yes ; no)

State : Set
State = Wire → Bool

infix 4 _≈s_
_≈s_ : State → State → Set
s ≈s u = ∀ i → s i ≡ u i

toggle : Wire → Bool → State → State
toggle t p s i with i ≟ t
... | yes _ = s i xor p
... | no _ = s i

toggle-at : ∀ t p s → toggle t p s t ≡ s t xor p
toggle-at t p s with t ≟ t
... | yes _ = refl
... | no t≢t = ⊥-elim (t≢t refl)

toggle-other : ∀ {i t} → i ≢ t → ∀ p s → toggle t p s i ≡ s i
toggle-other {i} {t} i≢t p s with i ≟ t
... | yes i≡t = ⊥-elim (i≢t i≡t)
... | no _ = refl

toggle-cong : ∀ t p {s u} → s ≈s u → toggle t p s ≈s toggle t p u
toggle-cong t p eq i with i ≟ t
... | yes _ = cong (_xor p) (eq i)
... | no _ = eq i

private
  xor-invol : ∀ a b → (a xor b) xor b ≡ a
  xor-invol false false = refl
  xor-invol false true = refl
  xor-invol true false = refl
  xor-invol true true = refl

  borrow-xor : ∀ t r p q →
    (t xor (r ∧ q)) xor ((r xor p) ∧ q) ≡ t xor (p ∧ q)
  borrow-xor false false false false = refl
  borrow-xor false false false true = refl
  borrow-xor false false true false = refl
  borrow-xor false false true true = refl
  borrow-xor false true false false = refl
  borrow-xor false true false true = refl
  borrow-xor false true true false = refl
  borrow-xor false true true true = refl
  borrow-xor true false false false = refl
  borrow-xor true false false true = refl
  borrow-xor true false true false = refl
  borrow-xor true false true true = refl
  borrow-xor true true false false = refl
  borrow-xor true true false true = refl
  borrow-xor true true true false = refl
  borrow-xor true true true true = refl

module _ (target spare : Wire) (different : target ≢ spare) where

  private
    reverse-different : spare ≢ target
    reverse-different eq = different (sym eq)

  -- Once the control values have been fixed, the four updates cancel
  -- on the borrowed wire and combine on the target.
  four-toggles : ∀ s p q →
    toggle spare p
      (toggle target ((s spare xor p) ∧ q)
        (toggle spare p (toggle target (s spare ∧ q) s)))
    ≈s toggle target (p ∧ q) s
  four-toggles s p q i = select (i ≟ target) (i ≟ spare)
    where
    open Eq.≡-Reasoning
    α = s spare ∧ q
    β = (s spare xor p) ∧ q
    u₁ = toggle target α s
    u₂ = toggle spare p u₁
    u₃ = toggle target β u₂
    u₄ = toggle spare p u₃

    Goal : Wire → Set
    Goal j = u₄ j ≡ toggle target (p ∧ q) s j

    at-target : Goal target
    at-target = begin
      u₄ target                 ≡⟨ toggle-other different p u₃ ⟩
      u₃ target                 ≡⟨ toggle-at target β u₂ ⟩
      u₂ target xor β           ≡⟨ cong (_xor β) (toggle-other different p u₁) ⟩
      u₁ target xor β           ≡⟨ cong (_xor β) (toggle-at target α s) ⟩
      (s target xor α) xor β    ≡⟨ borrow-xor (s target) (s spare) p q ⟩
      s target xor (p ∧ q)      ≡⟨ sym (toggle-at target (p ∧ q) s) ⟩
      toggle target (p ∧ q) s target ∎

    at-spare : Goal spare
    at-spare = begin
      u₄ spare                  ≡⟨ toggle-at spare p u₃ ⟩
      u₃ spare xor p            ≡⟨ cong (_xor p) (toggle-other reverse-different β u₂) ⟩
      u₂ spare xor p            ≡⟨ cong (_xor p) (toggle-at spare p u₁) ⟩
      (u₁ spare xor p) xor p   ≡⟨ xor-invol (u₁ spare) p ⟩
      u₁ spare                  ≡⟨ toggle-other reverse-different α s ⟩
      s spare                   ≡⟨ sym (toggle-other reverse-different (p ∧ q) s) ⟩
      toggle target (p ∧ q) s spare ∎

    at-other : i ≢ target → i ≢ spare → Goal i
    at-other it ir = begin
      u₄ i                      ≡⟨ toggle-other ir p u₃ ⟩
      u₃ i                      ≡⟨ toggle-other it β u₂ ⟩
      u₂ i                      ≡⟨ toggle-other ir p u₁ ⟩
      u₁ i                      ≡⟨ toggle-other it α s ⟩
      s i                       ≡⟨ sym (toggle-other it (p ∧ q) s) ⟩
      toggle target (p ∧ q) s i ∎

    select : Dec (i ≡ target) → Dec (i ≡ spare) → Goal i
    select (yes it) _ = Eq.subst Goal (sym it) at-target
    select (no _) (yes ir) = Eq.subst Goal (sym ir) at-spare
    select (no it) (no ir) = at-other it ir

  module Controls
    (P Q : State → Bool)
    (P-target : ∀ b s → P (toggle target b s) ≡ P s)
    (P-spare : ∀ b s → P (toggle spare b s) ≡ P s)
    (Q-target : ∀ b s → Q (toggle target b s) ≡ Q s)
    (Q-spare : ∀ b s → Q (toggle spare b s) ≡ Q s)
    where

    A B : State → State
    A s = toggle spare (P s) s
    B s = toggle target (s spare ∧ Q s) s

    borrowed-bit : ∀ s → A (B (A (B s))) ≈s toggle target (P s ∧ Q s) s
    borrowed-bit s i = trans (normal i) (four-toggles s (P s) (Q s) i)
      where
      s₁ = B s
      s₂ = A s₁
      s₃ = B s₂
      p = P s
      q = Q s
      β = (s spare xor p) ∧ q

      p₁ : P s₁ ≡ p
      p₁ = P-target (s spare ∧ Q s) s

      p₃ : P s₃ ≡ p
      p₃ = trans (P-target (s₂ spare ∧ Q s₂) s₂)
        (trans (P-spare (P s₁) s₁) p₁)

      q₂ : Q s₂ ≡ q
      q₂ = trans (Q-spare (P s₁) s₁) (Q-target (s spare ∧ Q s) s)

      r₂ : s₂ spare ≡ s spare xor p
      r₂ = trans (toggle-at spare (P s₁) s₁)
        (cong₂ _xor_ (toggle-other reverse-different (s spare ∧ Q s) s) p₁)

      b₂ : s₂ spare ∧ Q s₂ ≡ β
      b₂ = cong₂ _∧_ r₂ q₂

      n₂ : s₂ ≈s toggle spare p s₁
      n₂ j = cong (λ b → toggle spare b s₁ j) p₁

      n₃ : s₃ ≈s toggle target β (toggle spare p s₁)
      n₃ j = trans (cong (λ b → toggle target b s₂ j) b₂)
                    (toggle-cong target β n₂ j)

      normal : A s₃ ≈s toggle spare p (toggle target β (toggle spare p s₁))
      normal j = trans (cong (λ b → toggle spare b s₃ j) p₃)
                       (toggle-cong spare p n₃ j)
