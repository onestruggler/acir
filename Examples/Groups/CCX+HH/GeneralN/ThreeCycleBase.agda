------------------------------------------------------------------------
-- Presentations of groups
--
-- A single localized three-cycle at every width at least four.
-- A toggles wire0 with controls1,3,tail and borrows2; B toggles wire1
-- with controls0,2,tail and borrows3.  A B A B cycles exactly three
-- assignments and fixes every other one.  All work bits are restored.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.ThreeCycleBase (n : ℕ) where

open import Data.Bool.Base using (Bool ; false ; true ; _∧_ ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_ ; suc-injective)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (Vec ; tabulate)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using (_•_)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.GeneralN.Placement as Placement
import Examples.Groups.CCX+HH.GeneralN.FiniteControls as Finite
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (cons-cong)

module P = Placement (suc n)
module F = Finite (Fin P.width) _≟_
open P using (width)

private
  a-index b-index : Fin (suc (suc n)) → Fin width
  a-index zero = suc zero
  a-index (suc zero) = suc (suc (suc zero))
  a-index (suc (suc i)) = suc (suc (suc (suc i)))
  b-index zero = zero
  b-index (suc zero) = suc (suc zero)
  b-index (suc (suc i)) = suc (suc (suc (suc i)))

  a-injective : ∀ {i j} → a-index i ≡ a-index j → i ≡ j
  a-injective {zero} {zero} eq = refl
  a-injective {zero} {suc zero} ()
  a-injective {zero} {suc (suc j)} ()
  a-injective {suc zero} {zero} ()
  a-injective {suc zero} {suc zero} eq = refl
  a-injective {suc zero} {suc (suc j)} ()
  a-injective {suc (suc i)} {zero} ()
  a-injective {suc (suc i)} {suc zero} ()
  a-injective {suc (suc i)} {suc (suc j)} eq =
    cong suc (cong suc (suc-injective (suc-injective (suc-injective (suc-injective eq)))))

  b-injective : ∀ {i j} → b-index i ≡ b-index j → i ≡ j
  b-injective {zero} {zero} eq = refl
  b-injective {zero} {suc zero} ()
  b-injective {zero} {suc (suc j)} ()
  b-injective {suc zero} {zero} ()
  b-injective {suc zero} {suc zero} eq = refl
  b-injective {suc zero} {suc (suc j)} ()
  b-injective {suc (suc i)} {zero} ()
  b-injective {suc (suc i)} {suc zero} ()
  b-injective {suc (suc i)} {suc (suc j)} eq =
    cong suc (cong suc (suc-injective (suc-injective (suc-injective (suc-injective eq)))))

  a-target : ∀ i → zero ≢ a-index i
  a-target zero ()
  a-target (suc zero) ()
  a-target (suc (suc i)) ()
  a-spare : ∀ i → suc (suc zero) ≢ a-index i
  a-spare zero ()
  a-spare (suc zero) ()
  a-spare (suc (suc i)) ()
  b-target : ∀ i → suc zero ≢ b-index i
  b-target zero ()
  b-target (suc zero) ()
  b-target (suc (suc i)) ()
  b-spare : ∀ i → suc (suc (suc zero)) ≢ b-index i
  b-spare zero ()
  b-spare (suc zero) ()
  b-spare (suc (suc i)) ()

  a-controls = tabulate a-index
  b-controls = tabulate b-index

  a-valid : P.N.Valid a-controls zero (suc (suc zero))
  a-valid = record
    { target≢spare = λ ()
    ; target-fresh = F.fresh-tabulate _ a-index zero a-target
    ; spare-fresh = F.fresh-tabulate _ a-index (suc (suc zero)) a-spare
    ; distinct = F.distinct-tabulate _ a-index a-injective
    }
  b-valid : P.N.Valid b-controls (suc zero) (suc (suc (suc zero)))
  b-valid = record
    { target≢spare = λ ()
    ; target-fresh = F.fresh-tabulate _ b-index (suc zero) b-target
    ; spare-fresh = F.fresh-tabulate _ b-index (suc (suc (suc zero))) b-spare
    ; distinct = F.distinct-tabulate _ b-index b-injective
    }

A B : C.Circuit width
A = P.controlled _ a-controls zero (suc (suc zero))
B = P.controlled _ b-controls (suc zero) (suc (suc (suc zero)))

word : C.Circuit width
word = A • B • A • B

data Four : Set where
  four : Bool → Bool → Bool → Bool → Four

state : Four → C.State n → C.State width
state (four a b c d) t = cons a (cons b (cons c (cons d t)))

private
  tail₄ : C.State width → C.State n
  tail₄ s i = s (suc (suc (suc (suc i))))
  first₄ : C.State width → Four
  first₄ s = four (s zero) (s (suc zero)) (s (suc (suc zero))) (s (suc (suc (suc zero))))
  state-view : ∀ s → state (first₄ s) (tail₄ s) C.≈s s
  state-view s zero = refl
  state-view s (suc zero) = refl
  state-view s (suc (suc zero)) = refl
  state-view s (suc (suc (suc zero))) = refl
  state-view s (suc (suc (suc (suc i)))) = refl

  state-cong : ∀ v {s t} → s C.≈s t → state v s C.≈s state v t
  state-cong (four a b c d) eq = cons-cong refl (cons-cong refl (cons-cong refl (cons-cong refl eq)))

  af bf : Bool → Four → Four
  af r (four a b c d) = four (a xor (b ∧ (d ∧ r))) b c d
  bf r (four a b c d) = four a (b xor (a ∧ (c ∧ r))) c d

  step : Bool → Four → Four
  step false v = v
  step true (four a b false d) = four a b false d
  step true (four a b true false) = four a b true false
  step true (four false false true true) = four false false true true
  step true (four false true true true) = four true false true true
  step true (four true false true true) = four true true true true
  step true (four true true true true) = four false true true true

  table : ∀ r v → af r (bf r (af r (bf r v))) ≡ step r v
  -- The 32 Boolean cases are below; no matrix-size bound is involved.
  table false (four false false false false) = refl
  table false (four false false false true) = refl
  table false (four false false true false) = refl
  table false (four false false true true) = refl
  table false (four false true false false) = refl
  table false (four false true false true) = refl
  table false (four false true true false) = refl
  table false (four false true true true) = refl
  table false (four true false false false) = refl
  table false (four true false false true) = refl
  table false (four true false true false) = refl
  table false (four true false true true) = refl
  table false (four true true false false) = refl
  table false (four true true false true) = refl
  table false (four true true true false) = refl
  table false (four true true true true) = refl
  table true (four false false false false) = refl
  table true (four false false false true) = refl
  table true (four false false true false) = refl
  table true (four false false true true) = refl
  table true (four false true false false) = refl
  table true (four false true false true) = refl
  table true (four false true true false) = refl
  table true (four false true true true) = refl
  table true (four true false false false) = refl
  table true (four true false false true) = refl
  table true (four true false true false) = refl
  table true (four true false true true) = refl
  table true (four true true false false) = refl
  table true (four true true false true) = refl
  table true (four true true true false) = refl
  table true (four true true true true) = refl

  a-local : ∀ v t → C.act A (state v t) C.≈s state (af (F.all n t) v) t
  a-local (four a b c d) t zero = trans
    (P.controlled-correct _ a-controls zero (suc (suc zero)) a-valid (state (four a b c d) t) zero)
    (cong (λ p → P.B.toggle zero p (state (four a b c d) t) zero)
      (F.controls-tabulate _ a-index (state (four a b c d) t)))
  a-local (four a b c d) t (suc i) = trans
    (P.controlled-correct _ a-controls zero (suc (suc zero)) a-valid (state (four a b c d) t) (suc i))
    (cong (λ p → P.B.toggle zero p (state (four a b c d) t) (suc i))
      (F.controls-tabulate _ a-index (state (four a b c d) t)))

  b-local : ∀ v t → C.act B (state v t) C.≈s state (bf (F.all n t) v) t
  b-local (four a b c d) t zero = trans
    (P.controlled-correct _ b-controls (suc zero) (suc (suc (suc zero))) b-valid (state (four a b c d) t) zero)
    (cong (λ p → P.B.toggle (suc zero) p (state (four a b c d) t) zero)
      (F.controls-tabulate _ b-index (state (four a b c d) t)))
  b-local (four a b c d) t (suc zero) = trans
    (P.controlled-correct _ b-controls (suc zero) (suc (suc (suc zero))) b-valid (state (four a b c d) t) (suc zero))
    (cong (λ p → P.B.toggle (suc zero) p (state (four a b c d) t) (suc zero))
      (F.controls-tabulate _ b-index (state (four a b c d) t)))
  b-local (four a b c d) t (suc (suc i)) = trans
    (P.controlled-correct _ b-controls (suc zero) (suc (suc (suc zero))) b-valid (state (four a b c d) t) (suc (suc i)))
    (cong (λ p → P.B.toggle (suc zero) p (state (four a b c d) t) (suc (suc i)))
      (F.controls-tabulate _ b-index (state (four a b c d) t)))

  local : ∀ v t → C.act word (state v t) C.≈s state (step (F.all n t) v) t
  local v t i = trans (C.act-cong A third i)
    (trans (a-local v₃ t i) (cong (λ q → state q t i) (table r v)))
    where
    r = F.all n t
    v₁ = bf r v
    v₂ = af r v₁
    v₃ = bf r v₂
    second : C.act A (C.act B (state v t)) C.≈s state v₂ t
    second j = trans (C.act-cong A (b-local v t) j) (a-local v₁ t j)
    third : C.act B (C.act A (C.act B (state v t))) C.≈s state v₃ t
    third j = trans (C.act-cong B second j) (b-local v₂ t j)

point₁ point₂ point₃ : C.State width
point₁ = state (four true false true true) (λ _ → true)
point₂ = state (four true true true true) (λ _ → true)
point₃ = state (four false true true true) (λ _ → true)

first : C.act word point₁ C.≈s point₂
first i = trans (local (four true false true true) (λ _ → true) i)
  (cong (λ r → state (step r (four true false true true)) (λ _ → true) i) (F.all-ones n))

second : C.act word point₂ C.≈s point₃
second i = trans (local (four true true true true) (λ _ → true) i)
  (cong (λ r → state (step r (four true true true true)) (λ _ → true) i) (F.all-ones n))

third : C.act word point₃ C.≈s point₁
third i = trans (local (four false true true true) (λ _ → true) i)
  (cong (λ r → state (step r (four false true true true)) (λ _ → true) i) (F.all-ones n))

private
  inactive : ∀ v t → ¬ (state v t C.≈s point₁) → ¬ (state v t C.≈s point₂) →
    ¬ (state v t C.≈s point₃) → state (step (F.all n t) v) t C.≈s state v t
  inactive v t ne₁ ne₂ ne₃ = choose (F.all n t) refl v ne₁ ne₂ ne₃
    where
    choose : ∀ r → F.all n t ≡ r → ∀ v →
      ¬ (state v t C.≈s point₁) → ¬ (state v t C.≈s point₂) →
      ¬ (state v t C.≈s point₃) → state (step r v) t C.≈s state v t
    choose false eq v ne₁ ne₂ ne₃ i = refl
    choose true eq (four a b false d) ne₁ ne₂ ne₃ i = refl
    choose true eq (four a b true false) ne₁ ne₂ ne₃ i = refl
    choose true eq (four false false true true) ne₁ ne₂ ne₃ i = refl
    choose true eq (four true false true true) ne₁ ne₂ ne₃ i =
      ⊥-elim (ne₁ (state-cong (four true false true true) (F.all-true n t eq)))
    choose true eq (four true true true true) ne₁ ne₂ ne₃ i =
      ⊥-elim (ne₂ (state-cong (four true true true true) (F.all-true n t eq)))
    choose true eq (four false true true true) ne₁ ne₂ ne₃ i =
      ⊥-elim (ne₃ (state-cong (four false true true true) (F.all-true n t eq)))

outside : ∀ s → ¬ (s C.≈s point₁) → ¬ (s C.≈s point₂) → ¬ (s C.≈s point₃) → C.act word s C.≈s s
outside s ne₁ ne₂ ne₃ i = trans (C.act-cong word (λ j → sym (state-view s j)) i)
  (trans (local (first₄ s) (tail₄ s) i)
    (trans (inactive (first₄ s) (tail₄ s)
      (λ eq → ne₁ (λ j → trans (sym (state-view s j)) (eq j)))
      (λ eq → ne₂ (λ j → trans (sym (state-view s j)) (eq j)))
      (λ eq → ne₃ (λ j → trans (sym (state-view s j)) (eq j))) i)
      (state-view s i)))
