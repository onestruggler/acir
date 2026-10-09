------------------------------------------------------------------------
-- Presentations of groups
--
-- Counting indices: splitting a count by a second predicate, finding
-- an index outside given ones, and the counts of predicates that hold
-- at exactly two or three indices.  The pair levels use them on the
-- odd entries of a column and their residue classes (Norm: both
-- classes have evenly many).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Counting where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.Clifford+CS-TwoLevel.Search
  using (count ; count-false ; count-one ; count-drop₂ ; first ; first-just ; first-nothing)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Splitting a count

count-split : (P Q : Fin n → Bool) → count P ≡ count (λ x → P x ∧ Q x) ℕ.+ count (λ x → P x ∧ not (Q x))
count-split {zero} P Q = refl
count-split {suc n} P Q =
  trans (cong ((if P zero then 1 else 0) ℕ.+_) (count-split (P ∘ suc) (Q ∘ suc)))
        (step (P zero) (Q zero) (count (λ x → P (suc x) ∧ Q (suc x))) (count (λ x → P (suc x) ∧ not (Q (suc x)))))
  where
  step : ∀ p q a b → (if p then 1 else 0) ℕ.+ (a ℕ.+ b) ≡
                     ((if p ∧ q then 1 else 0) ℕ.+ a) ℕ.+ ((if p ∧ not q then 1 else 0) ℕ.+ b)
  step true true a b = refl
  step true false a b = sym (ℕP.+-suc a b)
  step false true a b = refl
  step false false a b = refl

------------------------------------------------------------------------
-- An index outside some others

-- Either P holds somewhere E does not, or E holds wherever P does.
search : (P E : Fin n → Bool) → (∃ λ y → P y ≡ true × E y ≡ false) ⊎ (∀ y → P y ≡ true → E y ≡ true)
search P E = at (first (λ x → P x ∧ not (E x))) refl
  where
  split : ∀ {p e} → p ∧ not e ≡ true → p ≡ true × e ≡ false
  split {true} {false} _ = refl , refl
  at : (r : Maybe (Fin _)) → first (λ x → P x ∧ not (E x)) ≡ r →
       (∃ λ y → P y ≡ true × E y ≡ false) ⊎ (∀ y → P y ≡ true → E y ≡ true)
  at (just y) eq = inj₁ (y , split (proj₁ (first-just (λ x → P x ∧ not (E x)) eq)))
  at nothing eq = inj₂ λ y Py → back (P y) (E y) Py (first-nothing (λ x → P x ∧ not (E x)) eq y)
    where
    back : ∀ p e → p ≡ true → p ∧ not e ≡ false → e ≡ true
    back true true _ _ = refl
    back true false _ ()

------------------------------------------------------------------------
-- Exact counts

private
  false-elsewhere : (P : Fin n → Bool) → (S : Fin n → Set) → (∀ y → P y ≡ true → S y) →
                    ∀ x → (S x → ⊥) → P x ≡ false
  false-elsewhere P S inside x out = at (P x) refl
    where
    at : ∀ b → P x ≡ b → P x ≡ false
    at true e = ⊥-elim (out (inside x e))
    at false e = e

-- True at exactly a and b.
count-two : (P : Fin n → Bool) (a b : Fin n) → a ≢ b → P a ≡ true → P b ≡ true →
            (∀ y → P y ≡ true → y ≡ a ⊎ y ≡ b) → count P ≡ 2
count-two {n} P a b a≢b Pa Pb inside =
  trans (count-drop₂ P (λ _ → false) a b a≢b Pa Pb refl refl
           (λ x x≢a x≢b → false-elsewhere P (λ y → y ≡ a ⊎ y ≡ b) inside x
                            λ { (inj₁ e) → x≢a e ; (inj₂ e) → x≢b e }))
        (cong (λ m → 2 ℕ.+ m) (count-false {n} (λ _ → false) (λ _ → refl)))

-- True at exactly a, b and c.
count-three : (P : Fin n → Bool) (a b c : Fin n) → a ≢ b → a ≢ c → b ≢ c →
              P a ≡ true → P b ≡ true → P c ≡ true →
              (∀ y → P y ≡ true → y ≡ a ⊎ y ≡ b ⊎ y ≡ c) → count P ≡ 3
count-three {n} P a b c a≢b a≢c b≢c Pa Pb Pc inside =
  trans (count-drop₂ P R a b a≢b Pa Pb (R≡ a (inj₁ refl)) (R≡ b (inj₂ refl)) agree)
        (cong (λ m → 2 ℕ.+ m) (count-one R c Rc Rout))
  where
  -- P with a and b turned off.
  R : Fin n → Bool
  R x = if eqᵇ x a then false else if eqᵇ x b then false else P x
    where
    open import Relation.Nullary.Decidable using (does)
    import Data.Fin.Properties as FinP
    eqᵇ : Fin n → Fin n → Bool
    eqᵇ x y = does (x FinP.≟ y)
  open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false)
  import Data.Fin.Properties as FinP
  if-f : ∀ {d : Bool} {x y : Bool} → d ≡ false → (if d then x else y) ≡ y
  if-f refl = refl
  if-t : ∀ {d : Bool} {x y : Bool} → d ≡ true → (if d then x else y) ≡ x
  if-t refl = refl
  R≡ : ∀ x → x ≡ a ⊎ x ≡ b → R x ≡ false
  R≡ x (inj₁ refl) = if-t (dec-true (x FinP.≟ x) refl)
  R≡ x (inj₂ refl) = trans (if-f (dec-false (x FinP.≟ a) (λ e → a≢b (sym e)))) (if-t (dec-true (x FinP.≟ x) refl))
  R-off : ∀ x → x ≢ a → x ≢ b → R x ≡ P x
  R-off x x≢a x≢b = trans (if-f (dec-false (x FinP.≟ a) x≢a)) (if-f (dec-false (x FinP.≟ b) x≢b))
  agree : ∀ x → x ≢ a → x ≢ b → P x ≡ R x
  agree x x≢a x≢b = sym (R-off x x≢a x≢b)
  Rc : R c ≡ true
  Rc = trans (R-off c (λ e → a≢c (sym e)) (λ e → b≢c (sym e))) Pc
  Rout : ∀ x → x ≢ c → R x ≡ false
  Rout x x≢c = at (x FinP.≟ a) (x FinP.≟ b)
    where
    open import Relation.Nullary using (Dec ; yes ; no)
    at : Dec (x ≡ a) → Dec (x ≡ b) → R x ≡ false
    at (yes e) _ = R≡ x (inj₁ e)
    at (no _) (yes e) = R≡ x (inj₂ e)
    at (no x≢a) (no x≢b) =
      trans (R-off x x≢a x≢b)
        (false-elsewhere P (λ y → y ≡ a ⊎ y ≡ b ⊎ y ≡ c) inside x
           λ { (inj₁ e) → x≢a e ; (inj₂ (inj₁ e)) → x≢b e ; (inj₂ (inj₂ e)) → x≢c e })
