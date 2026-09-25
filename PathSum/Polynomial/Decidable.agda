------------------------------------------------------------------------
-- Presentations of groups
--
-- Deciding statements about polynomials
--
-- A polynomial here is a function on the finitely many monomials in a
-- fixed number of variables (PathSum.Polynomial), so any statement that
-- holds coefficient by coefficient -- a congruence P ≈[ c ] Q, the
-- absence of a variable, an order bound -- is decided by trying every
-- monomial.  This module supplies those deciders, and the two
-- functions that turn a decision into a proof when the polynomials are
-- closed: by-eval takes the congruence as an implicit True argument,
-- which Agda fills in by computing the decision to `yes`, and
-- refute-by-eval does the same for a refutation.
--
-- The side conditions of the general rules of figure 2
-- (PathSum.Reduction.General) are of two kinds.  That y_i does not
-- occur in the quotient (Absent) is coefficient-wise, and decided
-- like the rest (Absent?).  That the quotient is Boolean-valued
-- (BoolValued) is a statement about values, at every Boolean point;
-- it is decided by enumerating the points (BoolValued?), an
-- assignment Fin k → Bool being read off the vector of its values, and
-- the statement respecting pointwise equality of assignments.  The
-- same enumeration decides whether a polynomial is the lift of a
-- Boolean expression, in the sense of section 2 (LiftOf, liftOf?):
-- that it takes the expression's value, 0 or 1, at every point.  By
-- Möbius inversion it then has the lift's coefficients exactly
-- (liftOf⇒≡), so a quotient written as a short literal polynomial is
-- checked to be the paper's lifted Boolean expression without ever
-- computing the lift, whose products are dense double sums.
--
-- The deciders are assembled only from map′, _×?_, _⊎?_ and _→?_,
-- whose Boolean part computes without touching any proof (the `does`
-- field of each is defined from the `does` fields of its parts), so
-- that checking a closed instance costs one integer test per monomial
-- or per point and nothing more.  PathSum.Anywhere.Match, which decides
-- whether some rule applies, carries its own copies of the first four
-- (allSubset?, allMon?, _≈?[_]_ and NoVar?) inside a module
-- parameterised by the precision; they compute the same Booleans.
-- Nothing here is efficient: a polynomial on n + m variables has
-- 2^(n+m) coefficients, and every one of them is inspected; a value
-- is a sum over all of them, taken at each of the 2^(n+m) points.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Decidable where

open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_; 0∣⇒≡0)
open import Data.Integer.Properties using (_≟_; +-inverseʳ; i-j≡0⇒i≡j)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong₂; subst)
open import Relation.Nullary.Decidable using
  (Dec; True; False; map′; _×?_; _⊎?_; _→?_; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Polynomial hiding (subst)
open import PathSum.Polynomial.Properties using (eval-cong; i∣0)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; BExp; ⟦_⟧ᵉ; liftᵉ; eval-liftᵉ; ≈-from-values)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Every subset, every monomial

-- A property of every subset of k elements holds when it holds of the
-- subsets with and without the first element; the Boolean computed is
-- the conjunction of the two halves, and stops at the first `false`.

all-subsets? : ∀ {k} {B : Subset k → Set} →
               (∀ s → Dec (B s)) → Dec (∀ s → B s)
all-subsets? {zero}  {B} B? = map′ to from (B? [])
  where
  to : B [] → ∀ s → B s
  to b [] = b

  from : (∀ s → B s) → B []
  from all = all []
all-subsets? {suc k} {B} B? =
  map′ to from (all-subsets? (λ s → B? (inside ∷ s)) ×?
                all-subsets? (λ s → B? (outside ∷ s)))
  where
  to : (∀ s → B (inside ∷ s)) × (∀ s → B (outside ∷ s)) → ∀ s → B s
  to (bᵢ , bₒ) (inside  ∷ s) = bᵢ s
  to (bᵢ , bₒ) (outside ∷ s) = bₒ s

  from : (∀ s → B s) → (∀ s → B (inside ∷ s)) × (∀ s → B (outside ∷ s))
  from all = (λ s → all (inside ∷ s)) , (λ s → all (outside ∷ s))

-- A monomial is a pair of subsets.

all-monomials? : {B : Mon n m → Set} →
                 (∀ γ → Dec (B γ)) → Dec (∀ γ → B γ)
all-monomials? B? =
  map′ (λ h γ → h (proj₁ γ) (proj₂ γ)) (λ h α β → h (α , β))
       (all-subsets? (λ α → all-subsets? (λ β → B? (α , β))))


------------------------------------------------------------------------
-- Congruences and absent variables

infix 4 _≈?[_]_

_≈?[_]_ : (P : Poly n m) (c : ℤ) (Q : Poly n m) → Dec (P ≈[ c ] Q)
P ≈?[ c ] Q = all-monomials? (λ γ → c ∣? (P γ - Q γ))

-- The implication is decided lazily: a monomial not containing v
-- settles its case without the divisibility test.

NoVar? : (c : ℤ) (v : Var n m) (P : Poly n m) → Dec (NoVar c v P)
NoVar? c v P = all-monomials? (λ γ → (v ∈ᵐ? γ) →? (c ∣? P γ))

-- Exact absence, the side condition of [HH] on its quotient.

Absent? : (v : Var n m) (P : Poly n m) → Dec (Absent v P)
Absent? v P = all-monomials? (λ γ → (v ∈ᵐ? γ) →? (P γ ≟ 0ℤ))


------------------------------------------------------------------------
-- Discharging a congruence by computation

-- For closed polynomials the decision computes to yes or no, and the
-- implicit argument below is then ⊤ or ⊥: Agda fills it in exactly
-- when the congruence holds.  The polynomials are explicit, since they
-- cannot be recovered from the type of the congruence.

by-eval : (P : Poly n m) (c : ℤ) (Q : Poly n m) →
          {True (P ≈?[ c ] Q)} → P ≈[ c ] Q
by-eval P c Q {t} = toWitness {a? = P ≈?[ c ] Q} t

refute-by-eval : (P : Poly n m) (c : ℤ) (Q : Poly n m) →
                 {False (P ≈?[ c ] Q)} → ¬ (P ≈[ c ] Q)
refute-by-eval P c Q {f} = toWitnessFalse {a? = P ≈?[ c ] Q} f


------------------------------------------------------------------------
-- Every assignment

-- The assignments to k variables are the vectors of their values: a
-- property that respects pointwise equality holds of every assignment
-- when it holds of every `lookup v`.

all-assignments? : ∀ {k} {B : (Fin k → Bool) → Set} →
                   (∀ {f g} → (∀ i → f i ≡ g i) → B f → B g) →
                   (∀ f → Dec (B f)) → Dec (∀ f → B f)
all-assignments? resp B? =
  map′ (λ h f → resp (lookup∘tabulate f) (h (tabulate f)))
       (λ h v → h (lookup v))
       (all-subsets? (λ v → B? (lookup v)))

-- Every point (x, y) of the Boolean cube in n + m variables.

all-points? : {B : (Fin n → Bool) → (Fin m → Bool) → Set} →
              (∀ {x x′ y y′} → (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
               B x y → B x′ y′) →
              (∀ x y → Dec (B x y)) → Dec (∀ x y → B x y)
all-points? resp B? =
  all-assignments? (λ x≗ h y → resp x≗ (λ _ → refl) (h y))
    (λ x → all-assignments? (λ y≗ → resp (λ _ → refl) y≗) (B? x))


------------------------------------------------------------------------
-- Boolean-valued polynomials

IsBit? : (z : ℤ) → Dec (IsBit z)
IsBit? z = (z ≟ 0ℤ) ⊎? (z ≟ 1ℤ)

-- The side condition of every general rule on its quotient, decided
-- by evaluating at every point.

BoolValued? : (Q : Poly n m) → Dec (BoolValued Q)
BoolValued? Q =
  all-points? (λ x≗ y≗ → subst IsBit (eval-cong Q x≗ y≗))
              (λ x y → IsBit? (eval Q x y))


------------------------------------------------------------------------
-- The lift of a Boolean expression

-- Q is the lift of e when it takes e's value, as 0 or 1, everywhere.

LiftOf : BExp n m → Poly n m → Set
LiftOf {n} {m} e Q = ∀ (x : Fin n → Bool) (y : Fin m → Bool) →
  eval Q x y ≡ (if ⟦ e ⟧ᵉ x y then 1ℤ else 0ℤ)

liftOf? : (e : BExp n m) (Q : Poly n m) → Dec (LiftOf e Q)
liftOf? e Q = all-points? resp (λ x y → eval Q x y ≟ bit x y)
  where
  bit : (Fin _ → Bool) → (Fin _ → Bool) → ℤ
  bit x y = if ⟦ e ⟧ᵉ x y then 1ℤ else 0ℤ

  resp : ∀ {x x′ y y′} → (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
         eval Q x y ≡ bit x y → eval Q x′ y′ ≡ bit x′ y′
  resp {x} {x′} {y} {y′} x≗ y≗ h = trans (sym (eval-cong Q x≗ y≗))
    (trans h (trans (sym (eval-liftᵉ e x y))
                    (trans (eval-cong (liftᵉ e) x≗ y≗)
                           (eval-liftᵉ e x′ y′))))

-- Values determine coefficients (Möbius inversion at modulus 0): the
-- lift of e is the only polynomial with its values.

liftOf⇒≡ : (e : BExp n m) (Q : Poly n m) → LiftOf e Q →
           ∀ γ → Q γ ≡ liftᵉ e γ
liftOf⇒≡ e Q h γ = i-j≡0⇒i≡j (Q γ) (liftᵉ e γ) (0∣⇒≡0
  (≈-from-values {c = 0ℤ} Q (liftᵉ e) (λ x y →
    subst (0ℤ ∣_)
      (sym (trans (cong₂ _-_ (h x y) (eval-liftᵉ e x y))
                  (+-inverseʳ (if ⟦ e ⟧ᵉ x y then 1ℤ else 0ℤ))))
      i∣0) γ))
