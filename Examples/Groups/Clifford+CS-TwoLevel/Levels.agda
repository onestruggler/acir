------------------------------------------------------------------------
-- Presentations of groups
--
-- Levels under the monomial generators X_[a,b] and i_[a], towards the
-- fact that expanding a generator into basic ones does not raise the
-- level (§3.3): X and i permute the entries of a column and multiply
-- them by units, so they keep its least denominator exponent and its
-- number of odd entries.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Levels where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-drop ; count-one)
open import Examples.Groups.Clifford+CS-TwoLevel.Column using (nodd)
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable using (eᶻ ; eᶻ-! ; δᶻ-refl ; δᶻ-≢)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The number of odd entries

-- X swaps two entries.
nodd-X : (a b : Fin n) → a ≢ b → (w : Vec Z n) → nodd (Xᶻ a b w) ≡ nodd w
nodd-X a b a≢b w = by (oddᶻ (w ! a)) (oddᶻ (w ! b)) refl refl
  where
  P Q : Fin _ → Bool
  P x = oddᶻ (w ! x)
  Q x = oddᶻ (Xᶻ a b w ! x)
  Qa : Q a ≡ P b
  Qa = cong oddᶻ (set₂-a a b (w ! b) (w ! a) w)
  Qb : Q b ≡ P a
  Qb = cong oddᶻ (set₂-b a b (w ! b) (w ! a) w a≢b)
  Q≢ : ∀ x → x ≢ a → x ≢ b → Q x ≡ P x
  Q≢ x xa xb = cong oddᶻ (set₂-≢ a b (w ! b) (w ! a) w xa xb)
  -- Both odd: the entries odd in both.
  Both : Fin _ → Bool
  Both x = P x ∧ Q x
  by : (pa pb : Bool) → P a ≡ pa → P b ≡ pb → count Q ≡ count P
  -- Equal parities at a and b: pointwise equal.
  by true true ea eb = count-cong Q P (λ x → same x (x FinP.≟ a) (x FinP.≟ b))
    where
    same : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Q x ≡ P x
    same x (yes refl) _ = trans Qa (trans eb (sym ea))
    same x (no xa) (yes refl) = trans Qb (trans ea (sym eb))
    same x (no xa) (no xb) = Q≢ x xa xb
  by false false ea eb = count-cong Q P (λ x → same x (x FinP.≟ a) (x FinP.≟ b))
    where
    same : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Q x ≡ P x
    same x (yes refl) _ = trans Qa (trans eb (sym ea))
    same x (no xa) (yes refl) = trans Qb (trans ea (sym eb))
    same x (no xa) (no xb) = Q≢ x xa xb
  -- Different parities: both counts exceed that of Both by one.
  by true false ea eb =
    trans (count-drop Q Both b (trans Qb ea) (cong (_∧ Q b) eb) (λ x xb → sym (atQ x xb (x FinP.≟ a))))
          (sym (count-drop P Both a ea (trans (cong (_∧ Q a) ea) (trans Qa eb)) (λ x xa → sym (atP x xa (x FinP.≟ b)))))
    where
    atP : ∀ x → x ≢ a → Dec (x ≡ b) → Both x ≡ P x
    atP x xa (yes refl) = trans (cong (_∧ Q x) eb) (sym eb)
    atP x xa (no xb) = trans (cong (P x ∧_) (Q≢ x xa xb)) (∧-idem (P x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl
    atQ : ∀ x → x ≢ b → Dec (x ≡ a) → Both x ≡ Q x
    atQ x xb (yes refl) = trans (cong (λ c → c ∧ Q x) ea) (refl)
    atQ x xb (no xa) = trans (cong (_∧ Q x) (sym (Q≢ x xa xb))) (∧-idem (Q x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl
  by false true ea eb =
    trans (count-drop Q Both a (trans Qa eb) (trans (cong (_∧ Q a) ea) refl) (λ x xa → sym (atQ x xa (x FinP.≟ b))))
          (sym (count-drop P Both b eb (trans (cong (_∧ Q b) eb) (trans (cong (true ∧_) Qb) ea))
                                    (λ x xb → sym (atP x xb (x FinP.≟ a)))))
    where
    atP : ∀ x → x ≢ b → Dec (x ≡ a) → Both x ≡ P x
    atP x xb (yes refl) = trans (cong (_∧ Q x) ea) (sym ea)
    atP x xb (no xa) = trans (cong (P x ∧_) (Q≢ x xa xb)) (∧-idem (P x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl
    atQ : ∀ x → x ≢ a → Dec (x ≡ b) → Both x ≡ Q x
    atQ x xa (yes refl) = trans (cong (_∧ Q x) eb) refl
    atQ x xa (no xb) = trans (cong (_∧ Q x) (sym (Q≢ x xa xb))) (∧-idem (Q x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl

-- i multiplies an entry by a unit, which keeps its parity.
odd-i : (a : Fin n) (w : Vec Z n) (x : Fin n) → oddᶻ (iᶻ a w ! x) ≡ oddᶻ (w ! x)
odd-i a w x = at (x FinP.≟ a)
  where
  at : Dec (x ≡ a) → oddᶻ (iᶻ a w ! x) ≡ oddᶻ (w ! x)
  at (yes refl) = trans (cong oddᶻ (set₁-a x (ⅈᶻ ZR.* (w ! x)) w)) (oddᶻ-* ⅈᶻ (w ! x))
  at (no xa) = cong oddᶻ (set₁-≢ a (ⅈᶻ ZR.* (w ! a)) w xa)

nodd-i : (a : Fin n) (w : Vec Z n) → nodd (iᶻ a w) ≡ nodd w
nodd-i a w = count-cong (λ x → oddᶻ (iᶻ a w ! x)) (λ x → oddᶻ (w ! x)) (odd-i a w)

-- A standard basis vector has one odd entry.
nodd-e : (c : Fin n) → nodd (eᶻ c) ≡ 1
nodd-e c = count-one (λ x → oddᶻ (eᶻ c ! x)) c
  (trans (cong oddᶻ (trans (eᶻ-! c c) (δᶻ-refl c))) refl)
  (λ x x≢c → trans (cong oddᶻ (trans (eᶻ-! c x) (δᶻ-≢ x≢c))) refl)

------------------------------------------------------------------------
-- The least denominator exponent

private
  Minimal-X : ∀ {k} (a b : Fin n) → a ≢ b → (w : Vec Z n) → Minimal k w → Minimal k (Xᶻ a b w)
  Minimal-X a b a≢b w (inj₁ k0) = inj₁ k0
  Minimal-X a b a≢b w (inj₂ (x , ox)) = inj₂ (at (x FinP.≟ a) (x FinP.≟ b))
    where
    open import Data.Product.Base using (∃)
    at : Dec (x ≡ a) → Dec (x ≡ b) → ∃ λ y → Odd (Xᶻ a b w ! y)
    at (yes refl) _ = b , trans (cong oddᶻ (set₂-b x b (w ! b) (w ! x) w a≢b)) ox
    at (no xa) (yes refl) = a , trans (cong oddᶻ (set₂-a a x (w ! x) (w ! a) w)) ox
    at (no xa) (no xb) = x , trans (cong oddᶻ (set₂-≢ a b (w ! b) (w ! a) w xa xb)) ox

  Minimal-i : ∀ {k} (a : Fin n) (w : Vec Z n) → Minimal k w → Minimal k (iᶻ a w)
  Minimal-i a w (inj₁ k0) = inj₁ k0
  Minimal-i a w (inj₂ (x , ox)) = inj₂ (x , trans (odd-i a w x) ox)

-- X and i keep the exponent, and act on the numerator.
lde-X : (a b : Fin n) .(p : a < b) (v : Vec D n) →
        lde (actV (X-gen a b p) v) ≡ lde v × num (actV (X-gen a b p) v) ≡ Xᶻ a b (num v)
lde-X a b p v = lde-char (lde v) (Xᶻ a b (num v))
  (trans (cong (actV (X-gen a b p)) (lde-eq v)) (actV-X a b p (lde v) (num v)))
  (Minimal-X a b (<⇒≢ p) (num v) (lde-min v))

lde-i : (a : Fin n) (v : Vec D n) →
        lde (actV (i-gen a) v) ≡ lde v × num (actV (i-gen a) v) ≡ iᶻ a (num v)
lde-i a v = lde-char (lde v) (iᶻ a (num v))
  (trans (cong (actV (i-gen a)) (lde-eq v)) (actV-i a (lde v) (num v)))
  (Minimal-i a (num v) (lde-min v))
