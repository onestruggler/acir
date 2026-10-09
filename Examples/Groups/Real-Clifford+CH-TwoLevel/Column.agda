------------------------------------------------------------------------
-- Presentations of groups
--
-- The syllables of Algorithm 1, as a function of the data of the
-- pivot column: its index p, its least denominator exponent k and its
-- numerator w ∈ ℤ[√2]ⁿ.  Indices start at 0 here, at 1 in the paper.
--
-- * k = 0: w = (-1)^τ e_m (Norm.lde0), and the syllable is Z_[p] if
--   m = p (then τ = 1), X_[m,p] Z_[m]^τ if m < p;
-- * k > 0: with i₁ the first odd entry of w and i₂ the next one in the
--   same residue class modulo 2, the syllable is H_[0,i₂] if i₁ = 0,
--   H_[0,i₂] X_[0,i₁] otherwise.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Column where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true)

open import Quantum.Synthesis.Ring using (RootTwo)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Odd entries and residue classes

-- The number of odd entries.
nodd : Vec Z n → ℕ
nodd w = count (λ x → oddᶻ (w ! x))

-- Two Booleans agree.
sameᵇ : Bool → Bool → Bool
sameᵇ a b = not (a xor b)

-- The first odd entry.
firstOdd : Vec Z n → Maybe (Fin n)
firstOdd w = first (λ x → oddᶻ (w ! x))

-- The first odd entry after j in the residue class of entry j: for odd
-- entries, the class modulo 2 is that of the √2-coefficient (rbit).
SameAfter : Fin n → Vec Z n → Fin n → Bool
SameAfter j w x = does (j FinP.<? x) ∧ (oddᶻ (w ! x) ∧ sameᵇ (rbit (w ! x)) (rbit (w ! j)))

nextSame : Fin n → Vec Z n → Maybe (Fin n)
nextSame j w = first (SameAfter j w)

------------------------------------------------------------------------
-- The syllables

-- Is a unit -1 (rather than 1)?
negᶻ : Z → Bool
negᶻ (RootTwo -[1+ _ ] _) = true
negᶻ (RootTwo (+ _) _)    = false

-- Z_[a]^τ.
Zτ : Fin n → Bool → Word (Gen n)
Zτ a true  = Zʷ a
Zτ a false = ε

-- k = 0: the unit (-1)^τ at index m.
unitSyl : (p m : Fin n) → Bool → Dec (m < p) → Word (Gen n)
unitSyl p m τ (yes m<p) = X m p m<p • Zτ m τ
unitSyl p m τ (no  _)   = Zτ p τ

-- k > 0: H_[0,i₂], or H_[0,i₂] X_[0,i₁].
pairSyl : (i₁ i₂ : Fin n) → .(i₁ < i₂) → Word (Gen n)
pairSyl zero     i₂ lt = H zero i₂ lt
pairSyl (suc i₁) i₂ lt = H zero i₂ (ℕP.<-trans (ℕ.s≤s ℕ.z≤n) lt) • X zero (suc i₁) (ℕ.s≤s ℕ.z≤n)

private
  unitStep : Fin n → Vec Z n → Maybe (Fin n) → Word (Gen n)
  unitStep p w (just m) = unitSyl p m (negᶻ (w ! m)) (m FinP.<? p)
  unitStep p w nothing  = ε

  pairDec : (i₁ i₂ : Fin n) → Dec (i₁ < i₂) → Word (Gen n)
  pairDec i₁ i₂ (yes lt) = pairSyl i₁ i₂ lt
  pairDec i₁ i₂ (no _)   = ε

  pairStep₂ : Fin n → Maybe (Fin n) → Word (Gen n)
  pairStep₂ i₁ (just i₂) = pairDec i₁ i₂ (i₁ FinP.<? i₂)
  pairStep₂ i₁ nothing   = ε

  pairStep : Vec Z n → Maybe (Fin n) → Word (Gen n)
  pairStep w (just i₁) = pairStep₂ i₁ (nextSame i₁ w)
  pairStep w nothing   = ε

sylData : Fin n → ℕ → Vec Z n → Word (Gen n)
sylData p zero    w = unitStep p w (firstOdd w)
sylData p (suc k) w = pairStep w (firstOdd w)

-- The syllable, from the facts that determine it.
sylData-unit< : ∀ {p m : Fin n} (w : Vec Z n) → firstOdd w ≡ just m → (m<p : m < p) →
                sylData p 0 w ≡ X m p m<p • Zτ m (negᶻ (w ! m))
sylData-unit< {p = p} {m} w fo m<p rewrite fo with m FinP.<? p
... | yes _ = refl
... | no ¬m<p = ⊥-elim (¬m<p m<p)

sylData-unit≡ : ∀ {p : Fin n} (w : Vec Z n) → firstOdd w ≡ just p →
                sylData p 0 w ≡ Zτ p (negᶻ (w ! p))
sylData-unit≡ {p = p} w fo rewrite fo with p FinP.<? p
... | yes p<p = ⊥-elim (FinP.<-irrefl refl p<p)
... | no _ = refl

sylData-pair : ∀ {p i₁ i₂ : Fin n} k (w : Vec Z n) → firstOdd w ≡ just i₁ → nextSame i₁ w ≡ just i₂ →
               (lt : i₁ < i₂) → sylData p (suc k) w ≡ pairSyl i₁ i₂ lt
sylData-pair {i₁ = i₁} {i₂} k w fo nx lt rewrite fo | nx with i₁ FinP.<? i₂
... | yes _ = refl
... | no ¬lt = ⊥-elim (¬lt lt)

------------------------------------------------------------------------
-- Characterising the chosen entries

firstOdd-char : ∀ (w : Vec Z n) {j} → Odd (w ! j) → (∀ x → x < j → Even (w ! x)) → firstOdd w ≡ just j
firstOdd-char w oj below = first-char (λ x → oddᶻ (w ! x)) oj below

firstOdd-spec : ∀ (w : Vec Z n) {j} → firstOdd w ≡ just j → Odd (w ! j) × (∀ x → x < j → Even (w ! x))
firstOdd-spec w eq = first-just (λ x → oddᶻ (w ! x)) eq

firstOdd-nothing : ∀ (w : Vec Z n) → firstOdd w ≡ nothing → ∀ x → Even (w ! x)
firstOdd-nothing w eq = first-nothing (λ x → oddᶻ (w ! x)) eq

-- x is odd and in the class of j.
Same : Vec Z n → Fin n → Fin n → Set
Same w j x = Odd (w ! x) × rbit (w ! x) ≡ rbit (w ! j)

private
  sameᵇ-true : ∀ a b → sameᵇ a b ≡ true → a ≡ b
  sameᵇ-true true  true  _ = refl
  sameᵇ-true false false _ = refl

  sameᵇ-refl : ∀ a → sameᵇ a a ≡ true
  sameᵇ-refl true  = refl
  sameᵇ-refl false = refl

  ∧-split : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-split {true} {true} _ = refl , refl

  SameAfter-true : ∀ (w : Vec Z n) j x → SameAfter j w x ≡ true → j < x × Same w j x
  SameAfter-true w j x eq = aux (j FinP.<? x) eq
    where
    aux : (d : Dec (j < x)) → does d ∧ (oddᶻ (w ! x) ∧ sameᵇ (rbit (w ! x)) (rbit (w ! j))) ≡ true →
          j < x × Same w j x
    aux (yes j<x) e = let (o , s) = ∧-split e in j<x , o , sameᵇ-true _ _ s
    aux (no _) ()

  SameAfter-intro : ∀ (w : Vec Z n) j x → j < x → Same w j x → SameAfter j w x ≡ true
  SameAfter-intro w j x j<x (o , s) =
    trans (cong (_∧ (oddᶻ (w ! x) ∧ sameᵇ (rbit (w ! x)) (rbit (w ! j)))) (dec-true (j FinP.<? x) j<x))
          (trans (cong (λ b → b ∧ sameᵇ (rbit (w ! x)) (rbit (w ! j))) o)
                 (trans (cong (sameᵇ (rbit (w ! x))) (sym s)) (sameᵇ-refl (rbit (w ! x)))))

  SameAfter-false : ∀ (w : Vec Z n) j x → SameAfter j w x ≡ false → j < x → ¬ Same w j x
  SameAfter-false w j x e j<x s = case (trans (sym e) (SameAfter-intro w j x j<x s))
    where
    case : false ≡ true → _
    case ()

nextSame-spec : ∀ (w : Vec Z n) {j ℓ} → nextSame j w ≡ just ℓ →
                j < ℓ × Same w j ℓ × (∀ x → j < x → x < ℓ → ¬ Same w j x)
nextSame-spec w {j} {ℓ} eq with first-just (SameAfter j w) eq
... | Pℓ , below = proj₁ (SameAfter-true w j ℓ Pℓ) , proj₂ (SameAfter-true w j ℓ Pℓ) ,
                   λ x j<x x<ℓ → SameAfter-false w j x (below x x<ℓ) j<x

nextSame-char : ∀ (w : Vec Z n) {j ℓ} → j < ℓ → Same w j ℓ →
                (∀ x → j < x → x < ℓ → ¬ Same w j x) → nextSame j w ≡ just ℓ
nextSame-char w {j} {ℓ} j<ℓ sℓ between = first-char (SameAfter j w) (SameAfter-intro w j ℓ j<ℓ sℓ) below
  where
  below : ∀ x → x < ℓ → SameAfter j w x ≡ false
  below x x<ℓ with SameAfter j w x in e
  ... | false = refl
  ... | true = let (j<x , s) = SameAfter-true w j x e in ⊥-elim (between x j<x x<ℓ s)

nextSame-nothing : ∀ (w : Vec Z n) {j} → nextSame j w ≡ nothing → ∀ x → j < x → ¬ Same w j x
nextSame-nothing w {j} eq x j<x = SameAfter-false w j x (first-nothing (SameAfter j w) eq x) j<x

------------------------------------------------------------------------
-- The syllable depends only on the parities and the odd entries

firstOdd-cong : (w w′ : Vec Z n) → (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → firstOdd w ≡ firstOdd w′
firstOdd-cong w w′ par = first-cong (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (w′ ! x)) par
