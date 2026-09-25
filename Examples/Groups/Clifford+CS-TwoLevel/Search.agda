------------------------------------------------------------------------
-- Presentations of groups
--
-- Searching finite index sets: the first and the last index at which
-- a boolean predicate holds, with specifications, and counting the
-- indices at which it holds.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Search where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The first index satisfying a predicate

first : (Fin n → Bool) → Maybe (Fin n)
first {zero} P = nothing
first {suc n} P with P zero
... | true  = just zero
... | false with first {n} (P ∘ suc)
...   | just x  = just (suc x)
...   | nothing = nothing

first-just : (P : Fin n → Bool) {j : Fin n} → first P ≡ just j →
             P j ≡ true × (∀ x → x < j → P x ≡ false)
first-just {suc n} P eq with P zero in P0
first-just {suc n} P refl | true = P0 , λ x ()
... | false with first {n} (P ∘ suc) in e
first-just {suc n} P refl | false | just x =
  let (Px , below) = first-just (P ∘ suc) e in
  Px , λ { zero _ → P0 ; (suc y) (s≤s y<x) → below y y<x }
first-just {suc n} P () | false | nothing

first-nothing : (P : Fin n → Bool) → first P ≡ nothing → ∀ x → P x ≡ false
first-nothing {suc n} P eq x with P zero in P0
first-nothing {suc n} P () x | true
... | false with first {n} (P ∘ suc) in e
first-nothing {suc n} P () x | false | just _
first-nothing {suc n} P refl zero | false | nothing = P0
first-nothing {suc n} P refl (suc x) | false | nothing = first-nothing (P ∘ suc) e x

-- The first index is characterised by its two properties.
first-char : (P : Fin n → Bool) {j : Fin n} → P j ≡ true → (∀ x → x < j → P x ≡ false) →
             first P ≡ just j
first-char {suc n} P {zero} Pj below with P zero
... | true = refl
... | false = ⊥-elim (true≢false (sym Pj))
  where true≢false : true ≢ false
        true≢false ()
first-char {suc n} P {suc j} Pj below with P zero | below zero (s≤s z≤n)
... | true | b0 = ⊥-elim (true≢false b0)
  where true≢false : true ≢ false
        true≢false ()
... | false | _ rewrite first-char (P ∘ suc) Pj (λ x x<j → below (suc x) (s≤s x<j)) = refl

------------------------------------------------------------------------
-- The last index satisfying a predicate

last : (Fin n → Bool) → Maybe (Fin n)
last {zero} P = nothing
last {suc n} P with last {n} (P ∘ suc)
... | just x  = just (suc x)
... | nothing with P zero
...   | true  = just zero
...   | false = nothing

last-just : (P : Fin n → Bool) {p : Fin n} → last P ≡ just p →
            P p ≡ true × (∀ x → p < x → P x ≡ false)
last-just {suc n} P eq with last {n} (P ∘ suc) in e
last-just {suc n} P refl | just x =
  let (Px , above) = last-just (P ∘ suc) e in
  Px , λ { zero () ; (suc y) (s≤s x<y) → above y x<y }
... | nothing with P zero in P0
last-just {suc n} P refl | nothing | true =
  P0 , λ { zero () ; (suc y) _ → last-nothing (P ∘ suc) e y }
  where
  last-nothing : ∀ {m} (Q : Fin m → Bool) → last Q ≡ nothing → ∀ x → Q x ≡ false
  last-nothing {suc m} Q eq x with last {m} (Q ∘ suc) in e′
  last-nothing {suc m} Q () x | just _
  ... | nothing with Q zero in Q0
  last-nothing {suc m} Q () x | nothing | true
  last-nothing {suc m} Q refl zero | nothing | false = Q0
  last-nothing {suc m} Q refl (suc x) | nothing | false = last-nothing (Q ∘ suc) e′ x
last-just {suc n} P () | nothing | false

last-nothing : (P : Fin n → Bool) → last P ≡ nothing → ∀ x → P x ≡ false
last-nothing {suc n} P eq x with last {n} (P ∘ suc) in e
last-nothing {suc n} P () x | just _
... | nothing with P zero in P0
last-nothing {suc n} P () x | nothing | true
last-nothing {suc n} P refl zero | nothing | false = P0
last-nothing {suc n} P refl (suc x) | nothing | false = last-nothing (P ∘ suc) e x

last-char : (P : Fin n → Bool) {p : Fin n} → P p ≡ true → (∀ x → p < x → P x ≡ false) →
            last P ≡ just p
last-char {suc n} P {zero} Pp above with last {n} (P ∘ suc) in e
... | just x = ⊥-elim (true≢false (trans (sym (proj₁ (last-just (P ∘ suc) e))) (above (suc x) (s≤s z≤n))))
  where true≢false : true ≢ false
        true≢false ()
... | nothing with P zero
...   | true = refl
...   | false = ⊥-elim (true≢false (sym Pp))
  where true≢false : true ≢ false
        true≢false ()
last-char {suc n} P {suc p} Pp above
  rewrite last-char (P ∘ suc) Pp (λ x p<x → above (suc x) (s≤s p<x)) = refl

last-none : (P : Fin n → Bool) → (∀ x → P x ≡ false) → last P ≡ nothing
last-none {zero} P none = refl
last-none {suc n} P none rewrite last-none (P ∘ suc) (none ∘ suc) | none zero = refl

------------------------------------------------------------------------
-- Counting

count : (Fin n → Bool) → ℕ
count {zero} P = 0
count {suc n} P = (if P zero then 1 else 0) ℕ.+ count {n} (P ∘ suc)

count-cong : (P Q : Fin n → Bool) → (∀ x → P x ≡ Q x) → count P ≡ count Q
count-cong {zero} P Q eq = refl
count-cong {suc n} P Q eq rewrite eq zero = cong ((if Q zero then 1 else 0) ℕ.+_) (count-cong (P ∘ suc) (Q ∘ suc) (eq ∘ suc))

-- Turning one index from true to false lowers the count by one.
count-drop : (P Q : Fin n → Bool) (a : Fin n) → P a ≡ true → Q a ≡ false →
             (∀ x → x ≢ a → P x ≡ Q x) → count P ≡ suc (count Q)
count-drop {suc n} P Q zero Pa Qa agree rewrite Pa | Qa =
  cong suc (count-cong (P ∘ suc) (Q ∘ suc) (λ x → agree (suc x) λ ()))
count-drop {suc n} P Q (suc a) Pa Qa agree rewrite agree zero (λ ()) =
  trans (cong ((if Q zero then 1 else 0) ℕ.+_)
              (count-drop (P ∘ suc) (Q ∘ suc) a Pa Qa (λ x x≢a → agree (suc x) (x≢a ∘ FinP.suc-injective))))
        (ℕP.+-suc (if Q zero then 1 else 0) (count (Q ∘ suc)))

-- If P holds somewhere, the count is positive.
count-pos : (P : Fin n → Bool) (a : Fin n) → P a ≡ true → 0 ℕ.< count P
count-pos {suc n} P zero Pa rewrite Pa = s≤s z≤n
count-pos {suc n} P (suc a) Pa = ℕP.≤-trans (count-pos (P ∘ suc) a Pa) (ℕP.m≤n+m _ _)

------------------------------------------------------------------------
-- Eliminators
--
-- Case analyses that do not abstract the goal (unlike with), which
-- matters when the goal mentions heavy terms such as matrices over
-- 𝔻[i]: with-abstraction normalises it.

module _ where
  open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
  open import Relation.Nullary using (Dec ; yes ; no)

  tri-elim : ∀ {A B C X : Set} → Tri A B C → (A → X) → (B → X) → (C → X) → X
  tri-elim (tri< a _ _) f g h = f a
  tri-elim (tri≈ _ b _) f g h = g b
  tri-elim (tri> _ _ c) f g h = h c

  dec-elim : ∀ {A X : Set} → Dec A → (A → X) → (¬ A → X) → X
  dec-elim (yes a) f g = f a
  dec-elim (no ¬a) f g = g ¬a

------------------------------------------------------------------------
-- More counting

count-false : (P : Fin n → Bool) → (∀ x → P x ≡ false) → count P ≡ 0
count-false {zero} P none = refl
count-false {suc n} P none rewrite none zero = count-false (P ∘ suc) (none ∘ suc)

-- A predicate true at exactly one index counts 1.
count-one : (P : Fin n → Bool) (a : Fin n) → P a ≡ true → (∀ x → x ≢ a → P x ≡ false) → count P ≡ 1
count-one {n} P a Pa others =
  trans (count-drop {n} P (λ _ → false) a Pa refl (λ x x≢a → others x x≢a))
        (cong suc (count-false {n} (λ _ → false) (λ _ → refl)))

-- Turning two indices from true to false lowers the count by two.
count-drop₂ : (P Q : Fin n → Bool) (a b : Fin n) → a ≢ b → P a ≡ true → P b ≡ true →
              Q a ≡ false → Q b ≡ false → (∀ x → x ≢ a → x ≢ b → P x ≡ Q x) →
              count P ≡ suc (suc (count Q))
count-drop₂ {n} P Q a b a≢b Pa Pb Qa Qb agree =
  trans (count-drop P R a Pa Ra agreeR) (cong suc (count-drop R Q b Rb Qb agreeQ))
  where
  R : Fin n → Bool
  R x = if does (x FinP.≟ a) then false else P x
    where open import Relation.Nullary.Decidable using (does)
  Ra : R a ≡ false
  Ra = cong (λ d → if d then false else P a) (dec-true (a FinP.≟ a) refl)
    where open import Relation.Nullary.Decidable using (dec-true)
  Rb : R b ≡ true
  Rb = trans (cong (λ d → if d then false else P b) (dec-false (b FinP.≟ a) (a≢b ∘ sym))) Pb
    where open import Relation.Nullary.Decidable using (dec-false)
  agreeR : ∀ x → x ≢ a → P x ≡ R x
  agreeR x x≢a = sym (cong (λ d → if d then false else P x) (dec-false (x FinP.≟ a) x≢a))
    where open import Relation.Nullary.Decidable using (dec-false)
  agreeQ : ∀ x → x ≢ b → R x ≡ Q x
  agreeQ x x≢b = dec-elim (x FinP.≟ a)
    (λ { refl → trans Ra (sym Qa) })
    (λ x≢a → trans (sym (agreeR x x≢a)) (agree x x≢a x≢b))
