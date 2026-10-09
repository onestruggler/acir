------------------------------------------------------------------------
-- Presentations of groups
--
-- The syllables of Algorithm 1, as a function of the data of the
-- pivot column: its index p, its least denominator exponent k and its
-- numerator w ∈ ℤⁿ.  Indices start at 0 here, at 1 in the paper.
--
-- * k = 0: w = (-1)^τ e_m (Norm.lde0), and the syllable is (-1)_[p] if
--   m = p (then τ = 1), X_[m,p] (-1)_[m]^τ if m < p (steps 8–10);
-- * k > 0: with a < b < c < d the first four odd entries of w, the
--   syllable is K_[a,b,c,d] (-1)_[a]^t, where t says that an odd
--   number of wa, wb, wc, wd are ≡ 3 (mod 4).
--
-- For k > 0 this is a variant of steps 13–15, which negate every entry
-- ≡ 3 (mod 4): one sign suffices for an even number of the entries to
-- be ≡ 1 (mod 4), which is what makes K reduce them (Lemma A.2), and
-- it spares the Main Lemma most of its sign cases.  The relations do
-- not depend on the choice of the normal form.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Column where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (_!_ ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Odd entries

-- The number of odd entries.
nodd : Vec ℤ n → ℕ
nodd w = count (λ x → oddℤ (w ! x))

-- The first odd entry.
firstOdd : Vec ℤ n → Maybe (Fin n)
firstOdd w = first (λ x → oddℤ (w ! x))

-- The first odd entry after j.
OddAfter : Fin n → Vec ℤ n → Fin n → Bool
OddAfter j w x = does (j FinP.<? x) ∧ oddℤ (w ! x)

nextOdd : Fin n → Vec ℤ n → Maybe (Fin n)
nextOdd j w = first (OddAfter j w)

------------------------------------------------------------------------
-- Units

Unit1 : ℤ → Set
Unit1 u = u ≡ + 1 ⊎ u ≡ -[1+ 0 ]

unit-odd : ∀ {u} → Unit1 u → Odd u
unit-odd (inj₁ refl) = refl
unit-odd (inj₂ refl) = refl

------------------------------------------------------------------------
-- The syllables

-- Is a unit -1 (rather than 1)?
negℤ : ℤ → Bool
negℤ -[1+ _ ] = true
negℤ (+ _)    = false

-- (-1)_[a]^τ.
Mτ : Fin n → Bool → Word (Gen n)
Mτ a true  = M a
Mτ a false = ε

-- k = 0: the unit (-1)^τ at index m.
unitSyl : (p m : Fin n) → Bool → Dec (m < p) → Word (Gen n)
unitSyl p m t (yes m<p) = X m p m<p • Mτ m t
unitSyl p m t (no  _)   = Mτ p t

-- Does an odd number of the four entries lie in the class 3 (mod 4)?
σ₄ : Vec ℤ n → (a b c d : Fin n) → Bool
σ₄ w a b c d = ((τ (w ! a) xor τ (w ! b)) xor τ (w ! c)) xor τ (w ! d)

-- k > 0: K_[a,b,c,d] with the sign that makes an even number of the
-- entries ≡ 1 (mod 4).
quadSyl : (a b c d : Fin n) → .(a < b) → .(b < c) → .(c < d) → Vec ℤ n → Word (Gen n)
quadSyl a b c d p q r w = K a b c d p q r • Mτ a (σ₄ w a b c d)

private
  unitStep : Fin n → Vec ℤ n → Maybe (Fin n) → Word (Gen n)
  unitStep p w (just m) = unitSyl p m (negℤ (w ! m)) (m FinP.<? p)
  unitStep p w nothing  = ε

  quadDec : (a b c d : Fin n) → Dec (a < b) → Dec (b < c) → Dec (c < d) → Vec ℤ n → Word (Gen n)
  quadDec a b c d (yes p) (yes q) (yes r) w = quadSyl a b c d p q r w
  quadDec a b c d _       _       _       w = ε

  quadStep₄ : Fin n → Fin n → Fin n → Maybe (Fin n) → Vec ℤ n → Word (Gen n)
  quadStep₄ a b c (just d) w = quadDec a b c d (a FinP.<? b) (b FinP.<? c) (c FinP.<? d) w
  quadStep₄ a b c nothing  w = ε

  quadStep₃ : Fin n → Fin n → Maybe (Fin n) → Vec ℤ n → Word (Gen n)
  quadStep₃ a b (just c) w = quadStep₄ a b c (nextOdd c w) w
  quadStep₃ a b nothing  w = ε

  quadStep₂ : Fin n → Maybe (Fin n) → Vec ℤ n → Word (Gen n)
  quadStep₂ a (just b) w = quadStep₃ a b (nextOdd b w) w
  quadStep₂ a nothing  w = ε

  quadStep : Maybe (Fin n) → Vec ℤ n → Word (Gen n)
  quadStep (just a) w = quadStep₂ a (nextOdd a w) w
  quadStep nothing  w = ε

sylData : Fin n → ℕ → Vec ℤ n → Word (Gen n)
sylData p zero    w = unitStep p w (firstOdd w)
sylData p (suc k) w = quadStep (firstOdd w) w

-- The syllable, from the facts that determine it.
sylData-unit< : ∀ {p m : Fin n} (w : Vec ℤ n) → firstOdd w ≡ just m → (m<p : m < p) →
                sylData p 0 w ≡ X m p m<p • Mτ m (negℤ (w ! m))
sylData-unit< {p = p} {m} w fo m<p rewrite fo with m FinP.<? p
... | yes _ = refl
... | no ¬m<p = ⊥-elim (¬m<p m<p)

sylData-unit≡ : ∀ {p : Fin n} (w : Vec ℤ n) → firstOdd w ≡ just p →
                sylData p 0 w ≡ Mτ p (negℤ (w ! p))
sylData-unit≡ {p = p} w fo rewrite fo with p FinP.<? p
... | yes p<p = ⊥-elim (FinP.<-irrefl refl p<p)
... | no _ = refl

sylData-quad : ∀ {p a b c d : Fin n} k (w : Vec ℤ n) →
               firstOdd w ≡ just a → nextOdd a w ≡ just b → nextOdd b w ≡ just c → nextOdd c w ≡ just d →
               (ab : a < b) (bc : b < c) (cd : c < d) → sylData p (suc k) w ≡ quadSyl a b c d ab bc cd w
sylData-quad {a = a} {b} {c} {d} k w fo na nb nc ab bc cd rewrite fo | na | nb | nc
  with a FinP.<? b | b FinP.<? c | c FinP.<? d
... | yes _ | yes _ | yes _ = refl
... | no ¬ab | _ | _ = ⊥-elim (¬ab ab)
... | yes _ | no ¬bc | _ = ⊥-elim (¬bc bc)
... | yes _ | yes _ | no ¬cd = ⊥-elim (¬cd cd)

------------------------------------------------------------------------
-- Characterising the chosen entries

firstOdd-char : ∀ (w : Vec ℤ n) {j} → Odd (w ! j) → (∀ x → x < j → Even (w ! x)) → firstOdd w ≡ just j
firstOdd-char w oj below = first-char (λ x → oddℤ (w ! x)) oj below

firstOdd-spec : ∀ (w : Vec ℤ n) {j} → firstOdd w ≡ just j → Odd (w ! j) × (∀ x → x < j → Even (w ! x))
firstOdd-spec w eq = first-just (λ x → oddℤ (w ! x)) eq

firstOdd-nothing : ∀ (w : Vec ℤ n) → firstOdd w ≡ nothing → ∀ x → Even (w ! x)
firstOdd-nothing w eq = first-nothing (λ x → oddℤ (w ! x)) eq

private
  ∧-split : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-split {true} {true} _ = refl , refl

  OddAfter-true : ∀ (w : Vec ℤ n) j x → OddAfter j w x ≡ true → j < x × Odd (w ! x)
  OddAfter-true w j x eq = aux (j FinP.<? x) eq
    where
    aux : (d : Dec (j < x)) → does d ∧ oddℤ (w ! x) ≡ true → j < x × Odd (w ! x)
    aux (yes j<x) e = j<x , proj₂ (∧-split e)
    aux (no _) ()

  OddAfter-intro : ∀ (w : Vec ℤ n) j x → j < x → Odd (w ! x) → OddAfter j w x ≡ true
  OddAfter-intro w j x j<x o = trans (cong (_∧ oddℤ (w ! x)) (dec-true (j FinP.<? x) j<x)) o

  OddAfter-false : ∀ (w : Vec ℤ n) j x → OddAfter j w x ≡ false → j < x → Even (w ! x)
  OddAfter-false w j x e j<x = aux (oddℤ (w ! x)) refl
    where
    aux : ∀ b → oddℤ (w ! x) ≡ b → Even (w ! x)
    aux false eb = eb
    aux true eb = case (trans (sym e) (OddAfter-intro w j x j<x eb))
      where
      case : false ≡ true → _
      case ()

nextOdd-spec : ∀ (w : Vec ℤ n) {j ℓ} → nextOdd j w ≡ just ℓ →
               j < ℓ × Odd (w ! ℓ) × (∀ x → j < x → x < ℓ → Even (w ! x))
nextOdd-spec w {j} {ℓ} eq with first-just (OddAfter j w) eq
... | Pℓ , below = proj₁ (OddAfter-true w j ℓ Pℓ) , proj₂ (OddAfter-true w j ℓ Pℓ) ,
                   λ x j<x x<ℓ → OddAfter-false w j x (below x x<ℓ) j<x

nextOdd-char : ∀ (w : Vec ℤ n) {j ℓ} → j < ℓ → Odd (w ! ℓ) →
               (∀ x → j < x → x < ℓ → Even (w ! x)) → nextOdd j w ≡ just ℓ
nextOdd-char w {j} {ℓ} j<ℓ oℓ between = first-char (OddAfter j w) (OddAfter-intro w j ℓ j<ℓ oℓ) below
  where
  below : ∀ x → x < ℓ → OddAfter j w x ≡ false
  below x x<ℓ = aux (j FinP.<? x)
    where
    aux : (d : Dec (j < x)) → does d ∧ oddℤ (w ! x) ≡ false
    aux (yes j<x) = trans (cong (λ b → b ∧ oddℤ (w ! x)) refl) (between x j<x x<ℓ)
    aux (no _) = refl

nextOdd-nothing : ∀ (w : Vec ℤ n) {j} → nextOdd j w ≡ nothing → ∀ x → j < x → Even (w ! x)
nextOdd-nothing w {j} eq x j<x = OddAfter-false w j x (first-nothing (OddAfter j w) eq x) j<x

------------------------------------------------------------------------
-- The chosen entries depend only on the parities

firstOdd-cong : (w w′ : Vec ℤ n) → (∀ x → oddℤ (w ! x) ≡ oddℤ (w′ ! x)) → firstOdd w ≡ firstOdd w′
firstOdd-cong w w′ par = first-cong (λ x → oddℤ (w ! x)) (λ x → oddℤ (w′ ! x)) par

nextOdd-cong : (j : Fin n) (w w′ : Vec ℤ n) → (∀ x → oddℤ (w ! x) ≡ oddℤ (w′ ! x)) → nextOdd j w ≡ nextOdd j w′
nextOdd-cong j w w′ par = first-cong (OddAfter j w) (OddAfter j w′) (λ x → cong (does (j FinP.<? x) ∧_) (par x))
