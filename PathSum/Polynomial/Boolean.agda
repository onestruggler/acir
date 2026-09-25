------------------------------------------------------------------------
-- Presentations of groups
--
-- Boolean-valued polynomials and the lifting of Boolean polynomials
--
-- The side condition of every rule of figure 2 in Amy's "Towards
-- Large-scale Functional Verification of Universal Quantum Circuits"
-- (QPL 2018) is that the quotient Q be Boolean-valued.  Here that
-- means {0,1}-valued at every Boolean point: BoolValued Q.  It cannot
-- mean "Boolean up to parity", since [ω]'s reduct -¼Q tells Q from Q+2
-- and [HH] and [Case] substitute Q for a Boolean variable; the rules
-- therefore take the lift of the quotient, with integer coefficients,
-- as data.  In the paper's dyadic setting nothing is lost by that: a
-- polynomial that is {0,1}-valued on the Boolean cube has integer
-- coefficients, Möbius inversion being integral (a remark; here the
-- coefficients are integers by construction).  And two Boolean-valued
-- polynomials with the same parities are equal (lift-unique).  The side
-- condition is semantic, but it has a syntactic form, Q · Q = Q
-- coefficient by coefficient (BoolValued⇔idem), and closure lemmas for
-- the usual constructions.  Substituting a Boolean-valued polynomial
-- for a path variable is evaluating at the assignment updated to its
-- value (eval-substᴾ-bool).
--
-- Section 2 lifts a Boolean polynomial to D[x] by the recursion
-- x^α ↦ x^α, P + Q ↦ P + Q - 2PQ (here _⊕ᴾ_), and lemma 2.5 says the
-- lift takes the polynomial's values modulo 2.  The recursion is on a
-- *presentation* of the polynomial as a sum, and the paper does not
-- argue that the result is independent of it.  Two versions are
-- proved.  For Boolean expressions -- variables, constants, ⊕ and ∧,
-- the form in which the examples' quotients come (x₃ ⊕ x₁x₂ for the
-- Toffoli gate) -- liftᵉ follows the syntax and eval-liftᵉ gives the
-- value exactly.  For a Boolean polynomial stored as a Poly read
-- modulo 2, as the output polynomials of a path-sum are, liftᴮ folds
-- ⊕ᴾ over the monomials with odd coefficient, in the fixed order of the
-- sums over subsets; lemma-2-5 is the paper's statement for it (for
-- every f, with BoolValued-liftᴮ for the values being bits), and
-- lift-unique is the independence the paper leaves implicit: any
-- Boolean-valued lift with the same parities has the same coefficients.
--
-- Möbius inversion (PathSum.Mobius) is the tool throughout: values at
-- every Boolean point determine coefficients, modulo any c
-- (≈-from-values).  It also makes the old, linear [HH] an instance of
-- the general one: the lifting of c ⊕ ⨁S agrees with v + (the lifting
-- of c ⊕ ⨁(S ∖ v)) modulo 2 (liftXor-split-≈), and the latter is free
-- of v (liftXor-Absent).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Boolean where

open import Data.Bool.Base using
  (Bool; true; false; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Fin.Subset.Properties using (x∈⁅y⁆⇒x≡y; ∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣m∣n⇒∣m+n; ∣m⇒∣-m; ∣⇒∣ᵤ; 0∣⇒≡0)
open import Data.Integer.Properties using
  (+-identityˡ; +-inverseʳ; i-j≡0⇒i≡j; i*j≡0⇒i≡0∨j≡0)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using ([]; _∷_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Assign using (_[_≔_])
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Order 0 using (parity)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; _∈ᵐ_; _∖ᵐ_; ⟪_⟫; 0ᴾ; _+ᴾ_; _-ᴾ_; _·ᴾ_;
   κ; μ; _≈[_]_; Σsub; Σmon; satᵐ; eval; liftXor)
open import PathSum.Polynomial.Properties using
  (Σsub-∣; Σsub-+; Σsub-neg; Σmon-∣; Σmon-+; Σmon-neg; eval-ext;
   eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-κ; liftXor-value; liftXor-split;
   liftXor-0; v∉S∖v; valᵛ; i∣0)
open import PathSum.Polynomial.Product using
  (_*ᴾ_; monoᴾ; eval-*ᴾ; eval-monoᴾ; eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Substitution using
  (Absent; Absent-+ᴾ; Absent--ᴾ; Absent-·ᴾ; Absent-*ᴾ; Absent-κ;
   Absent-μ; substᴾ; eval-substᴾ-≔)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Boolean-valued polynomials

IsBit : ℤ → Set
IsBit z = (z ≡ 0ℤ) ⊎ (z ≡ 1ℤ)

-- The rules' side condition on a quotient.

BoolValued : Poly n m → Set
BoolValued {n} {m} Q =
  ∀ (x : Fin n → Bool) (y : Fin m → Bool) → IsBit (eval Q x y)

-- The arithmetic of bits.

IsBit-if : (b : Bool) → IsBit (if b then 1ℤ else 0ℤ)
IsBit-if true  = inj₂ refl
IsBit-if false = inj₁ refl

-- A bit read back as a Boolean.

IsBit-bool : ∀ {z} → IsBit z → Bool
IsBit-bool (inj₁ _) = false
IsBit-bool (inj₂ _) = true

IsBit-bool-if : ∀ {z} (h : IsBit z) → (if IsBit-bool h then 1ℤ else 0ℤ) ≡ z
IsBit-bool-if (inj₁ z≡0) = sym z≡0
IsBit-bool-if (inj₂ z≡1) = sym z≡1

private
  bit-* : ∀ {a b} → IsBit a → IsBit b → IsBit (a * b)
  bit-* (inj₁ refl) (inj₁ refl) = inj₁ refl
  bit-* (inj₁ refl) (inj₂ refl) = inj₁ refl
  bit-* (inj₂ refl) (inj₁ refl) = inj₁ refl
  bit-* (inj₂ refl) (inj₂ refl) = inj₂ refl

  bit-⊕ : ∀ {a b} → IsBit a → IsBit b →
          IsBit ((a + b) - ((+ 2) * (a * b)))
  bit-⊕ (inj₁ refl) (inj₁ refl) = inj₁ refl
  bit-⊕ (inj₁ refl) (inj₂ refl) = inj₂ refl
  bit-⊕ (inj₂ refl) (inj₁ refl) = inj₂ refl
  bit-⊕ (inj₂ refl) (inj₂ refl) = inj₁ refl

  bit-¬ : ∀ {a} → IsBit a → IsBit (1ℤ - a)
  bit-¬ (inj₁ refl) = inj₂ refl
  bit-¬ (inj₂ refl) = inj₁ refl


------------------------------------------------------------------------
-- Closure

BoolValued-κ : (b : Bool) → BoolValued {n} {m} (κ (if b then 1ℤ else 0ℤ))
BoolValued-κ b x y =
  subst IsBit (sym (eval-κ (if b then 1ℤ else 0ℤ) x y)) (IsBit-if b)

BoolValued-0ᴾ : BoolValued (0ᴾ {n} {m})
BoolValued-0ᴾ x y = inj₁ (eval-0ᴾ x y)

BoolValued-monoᴾ : (γ : Mon n m) → BoolValued (monoᴾ γ)
BoolValued-monoᴾ γ x y =
  subst IsBit (sym (eval-monoᴾ γ x y)) (IsBit-if (satᵐ γ x y))

BoolValued-μ : (v : Var n m) → BoolValued (μ v)
BoolValued-μ v x y = subst IsBit (sym (eval-μᴾ v x y)) (IsBit-if (valᵛ v x y))

-- The lifting of a linear form (lemma 2.5 in its linear case, proved in
-- PathSum.Polynomial.Properties).

BoolValued-liftXor : (c : Bool) (S : Mon n m) → BoolValued (liftXor c S)
BoolValued-liftXor c S x y = liftXor-value c S x y

BoolValued-*ᴾ : {A B : Poly n m} →
                BoolValued A → BoolValued B → BoolValued (A *ᴾ B)
BoolValued-*ᴾ {A = A} {B} bA bB x y =
  subst IsBit (sym (eval-*ᴾ A B x y)) (bit-* (bA x y) (bB x y))

-- Exclusive or, the paper's P + Q - 2PQ, and negation.

infixl 6 _⊕ᴾ_

_⊕ᴾ_ : Poly n m → Poly n m → Poly n m
A ⊕ᴾ B = (A +ᴾ B) -ᴾ ((+ 2) ·ᴾ (A *ᴾ B))

¬ᴾ : Poly n m → Poly n m
¬ᴾ A = κ 1ℤ -ᴾ A

eval-⊕ᴾ : (A B : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (A ⊕ᴾ B) x y ≡
          (eval A x y + eval B x y) - ((+ 2) * (eval A x y * eval B x y))
eval-⊕ᴾ A B x y = trans
  (eval-−ᴾ (A +ᴾ B) ((+ 2) ·ᴾ (A *ᴾ B)) x y)
  (cong₂ _-_ (eval-+ᴾ A B x y)
             (trans (eval-·ᴾ (+ 2) (A *ᴾ B) x y)
                    (cong ((+ 2) *_) (eval-*ᴾ A B x y))))

eval-¬ᴾ : (A : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (¬ᴾ A) x y ≡ 1ℤ - eval A x y
eval-¬ᴾ A x y = trans (eval-−ᴾ (κ 1ℤ) A x y)
  (cong (_- eval A x y) (eval-κ 1ℤ x y))

BoolValued-⊕ᴾ : {A B : Poly n m} →
                BoolValued A → BoolValued B → BoolValued (A ⊕ᴾ B)
BoolValued-⊕ᴾ {A = A} {B} bA bB x y =
  subst IsBit (sym (eval-⊕ᴾ A B x y)) (bit-⊕ (bA x y) (bB x y))

BoolValued-¬ᴾ : {A : Poly n m} → BoolValued A → BoolValued (¬ᴾ A)
BoolValued-¬ᴾ {A = A} bA x y =
  subst IsBit (sym (eval-¬ᴾ A x y)) (bit-¬ (bA x y))

-- Absence of a variable survives them too.

Absent-⊕ᴾ : {v : Var n m} {A B : Poly n m} →
            Absent v A → Absent v B → Absent v (A ⊕ᴾ B)
Absent-⊕ᴾ {v = v} {A} {B} absA absB =
  Absent--ᴾ {v = v} {A = A +ᴾ B} {B = (+ 2) ·ᴾ (A *ᴾ B)}
    (Absent-+ᴾ {v = v} {A = A} {B = B} absA absB)
    (Absent-·ᴾ (+ 2) {v = v} {A = A *ᴾ B}
      (Absent-*ᴾ {v = v} {A = A} {B = B} absA absB))

Absent-¬ᴾ : {v : Var n m} {A : Poly n m} → Absent v A → Absent v (¬ᴾ A)
Absent-¬ᴾ {v = v} {A} absA =
  Absent--ᴾ {v = v} {A = κ 1ℤ} {B = A} (Absent-κ 1ℤ v) absA

-- Substituting a Boolean-valued polynomial for a path variable is
-- evaluating at the assignment updated to its value there.

eval-substᴾ-bool : (P : Poly n m) (j : Fin m) (L : Poly n m)
                   (bL : BoolValued L)
                   (x : Fin n → Bool) (y : Fin m → Bool) →
                   eval (substᴾ P y[ j ] L) x y ≡
                   eval P x (y [ j ≔ IsBit-bool (bL x y) ])
eval-substᴾ-bool P j L bL x y =
  eval-substᴾ-≔ P j L x y (IsBit-bool (bL x y)) (IsBit-bool-if (bL x y))


------------------------------------------------------------------------
-- The syntactic form of the side condition

-- A polynomial is Boolean-valued exactly when it is idempotent,
-- coefficient by coefficient: q ∈ {0,1} iff q² = q, and Möbius
-- inversion at c = 0 turns "every value of Q·Q - Q is 0" into "every
-- coefficient is".

private
  eval-idem : (Q : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
              eval ((Q *ᴾ Q) -ᴾ Q) x y ≡ (eval Q x y * eval Q x y) - eval Q x y
  eval-idem Q x y = trans (eval-−ᴾ (Q *ᴾ Q) Q x y)
    (cong (_- eval Q x y) (eval-*ᴾ Q Q x y))

  bit-idem : ∀ {q} → IsBit q → 0ℤ ∣ ((q * q) - q)
  bit-idem (inj₁ refl) = i∣0
  bit-idem (inj₂ refl) = i∣0

  factor : ∀ q → q * (q - 1ℤ) ≡ (q * q) - q
  factor = solve 1 (λ q → q :* (q :- con 1ℤ) := (q :* q) :- q) refl

  idem-bit : ∀ q → (q * q) - q ≡ 0ℤ → IsBit q
  idem-bit q eq with i*j≡0⇒i≡0∨j≡0 q (trans (factor q) eq)
  ... | inj₁ q≡0   = inj₁ q≡0
  ... | inj₂ q-1≡0 = inj₂ (i-j≡0⇒i≡j q 1ℤ q-1≡0)

BoolValued⇔idem : (Q : Poly n m) →
                  BoolValued Q ⇔ (∀ γ → ((Q *ᴾ Q) -ᴾ Q) γ ≡ 0ℤ)
BoolValued⇔idem Q = mk⇔ to from
  where
  to : BoolValued Q → ∀ γ → ((Q *ᴾ Q) -ᴾ Q) γ ≡ 0ℤ
  to bQ γ = 0∣⇒≡0 (values⇒coefficientsᵐ 0ℤ ((Q *ᴾ Q) -ᴾ Q)
    (λ x y → subst (0ℤ ∣_) (sym (eval-idem Q x y)) (bit-idem (bQ x y))) γ)

  from : (∀ γ → ((Q *ᴾ Q) -ᴾ Q) γ ≡ 0ℤ) → BoolValued Q
  from h x y = idem-bit (eval Q x y) (trans (sym (eval-idem Q x y))
    (trans (eval-ext ((Q *ᴾ Q) -ᴾ Q) 0ᴾ h x y) (eval-0ᴾ x y)))


------------------------------------------------------------------------
-- Boolean expressions and their lifting

infixl 6 _⊕ᵉ_
infixl 7 _∧ᵉ_

data BExp (n m : ℕ) : Set where
  var  : Var n m → BExp n m
  lit  : Bool → BExp n m
  _⊕ᵉ_ : BExp n m → BExp n m → BExp n m
  _∧ᵉ_ : BExp n m → BExp n m → BExp n m

⟦_⟧ᵉ : BExp n m → (Fin n → Bool) → (Fin m → Bool) → Bool
⟦ var v     ⟧ᵉ x y = valᵛ v x y
⟦ lit b     ⟧ᵉ x y = b
⟦ e₁ ⊕ᵉ e₂ ⟧ᵉ x y = ⟦ e₁ ⟧ᵉ x y xor ⟦ e₂ ⟧ᵉ x y
⟦ e₁ ∧ᵉ e₂ ⟧ᵉ x y = ⟦ e₁ ⟧ᵉ x y ∧ ⟦ e₂ ⟧ᵉ x y

-- The paper's recursion: a variable is its monomial, ⊕ is P + Q - 2PQ,
-- and ∧ (a product of Boolean polynomials) is the product.

liftᵉ : BExp n m → Poly n m
liftᵉ (var v)    = μ v
liftᵉ (lit b)    = κ (if b then 1ℤ else 0ℤ)
liftᵉ (e₁ ⊕ᵉ e₂) = liftᵉ e₁ ⊕ᴾ liftᵉ e₂
liftᵉ (e₁ ∧ᵉ e₂) = liftᵉ e₁ *ᴾ liftᵉ e₂

private
  xor-bit : ∀ a b →
    (((if a then 1ℤ else 0ℤ) + (if b then 1ℤ else 0ℤ)) -
     ((+ 2) * ((if a then 1ℤ else 0ℤ) * (if b then 1ℤ else 0ℤ)))) ≡
    (if (a xor b) then 1ℤ else 0ℤ)
  xor-bit true  true  = refl
  xor-bit true  false = refl
  xor-bit false true  = refl
  xor-bit false false = refl

  ∧-bit : ∀ a b →
    ((if a then 1ℤ else 0ℤ) * (if b then 1ℤ else 0ℤ)) ≡
    (if (a ∧ b) then 1ℤ else 0ℤ)
  ∧-bit true  true  = refl
  ∧-bit true  false = refl
  ∧-bit false true  = refl
  ∧-bit false false = refl

-- Lemma 2.5 for Boolean expressions, exactly: the lift takes the value
-- of the expression, as 0 or 1.

eval-liftᵉ : (e : BExp n m) (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (liftᵉ e) x y ≡ (if ⟦ e ⟧ᵉ x y then 1ℤ else 0ℤ)
eval-liftᵉ (var v)    x y = eval-μᴾ v x y
eval-liftᵉ (lit b)    x y = eval-κ (if b then 1ℤ else 0ℤ) x y
eval-liftᵉ (e₁ ⊕ᵉ e₂) x y = trans
  (eval-⊕ᴾ (liftᵉ e₁) (liftᵉ e₂) x y)
  (trans (cong₂ (λ a b → (a + b) - ((+ 2) * (a * b)))
                (eval-liftᵉ e₁ x y) (eval-liftᵉ e₂ x y))
         (xor-bit (⟦ e₁ ⟧ᵉ x y) (⟦ e₂ ⟧ᵉ x y)))
eval-liftᵉ (e₁ ∧ᵉ e₂) x y = trans
  (eval-*ᴾ (liftᵉ e₁) (liftᵉ e₂) x y)
  (trans (cong₂ _*_ (eval-liftᵉ e₁ x y) (eval-liftᵉ e₂ x y))
         (∧-bit (⟦ e₁ ⟧ᵉ x y) (⟦ e₂ ⟧ᵉ x y)))

BoolValued-liftᵉ : (e : BExp n m) → BoolValued (liftᵉ e)
BoolValued-liftᵉ e x y =
  subst IsBit (sym (eval-liftᵉ e x y)) (IsBit-if (⟦ e ⟧ᵉ x y))

-- A variable not occurring in an expression is absent from its lift:
-- the side condition "y_i does not appear in Q" of [HH], checked on
-- the syntax.

_∉ᵉ_ : Var n m → BExp n m → Set
v ∉ᵉ var u      = v ≢ u
v ∉ᵉ lit b      = ⊤
v ∉ᵉ (e₁ ⊕ᵉ e₂) = (v ∉ᵉ e₁) × (v ∉ᵉ e₂)
v ∉ᵉ (e₁ ∧ᵉ e₂) = (v ∉ᵉ e₁) × (v ∉ᵉ e₂)

∈⟪⟫⇒≡ : (v u : Var n m) → v ∈ᵐ ⟪ u ⟫ → v ≡ u
∈⟪⟫⇒≡ x[ i ] x[ j ] i∈ = cong x[_] (x∈⁅y⁆⇒x≡y j i∈)
∈⟪⟫⇒≡ x[ i ] y[ j ] i∈ = contradiction i∈ ∉⊥
∈⟪⟫⇒≡ y[ i ] x[ j ] i∈ = contradiction i∈ ∉⊥
∈⟪⟫⇒≡ y[ i ] y[ j ] i∈ = cong y[_] (x∈⁅y⁆⇒x≡y j i∈)

Absent-liftᵉ : (v : Var n m) (e : BExp n m) → v ∉ᵉ e → Absent v (liftᵉ e)
Absent-liftᵉ v (var u)    v≢u = Absent-μ u v (λ v∈ → v≢u (∈⟪⟫⇒≡ v u v∈))
Absent-liftᵉ v (lit b)    _   = Absent-κ (if b then 1ℤ else 0ℤ) v
Absent-liftᵉ v (e₁ ⊕ᵉ e₂) (h₁ , h₂) =
  Absent-⊕ᴾ {v = v} {A = liftᵉ e₁} {B = liftᵉ e₂}
    (Absent-liftᵉ v e₁ h₁) (Absent-liftᵉ v e₂ h₂)
Absent-liftᵉ v (e₁ ∧ᵉ e₂) (h₁ , h₂) =
  Absent-*ᴾ {v = v} {A = liftᵉ e₁} {B = liftᵉ e₂}
    (Absent-liftᵉ v e₁ h₁) (Absent-liftᵉ v e₂ h₂)


------------------------------------------------------------------------
-- Values determine coefficients

-- Möbius inversion modulo c, stated as a congruence of polynomials.

≈-from-values : ∀ {c : ℤ} (P Q : Poly n m) →
                (∀ (x : Fin n → Bool) (y : Fin m → Bool) →
                 c ∣ (eval P x y - eval Q x y)) →
                P ≈[ c ] Q
≈-from-values {c = c} P Q h = values⇒coefficientsᵐ c (P -ᴾ Q)
  (λ x y → subst (c ∣_) (sym (eval-−ᴾ P Q x y)) (h x y))

-- Two bits of the same parity are equal.

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  2∤-1 : ¬ ((+ 2) ∣ (- 1ℤ))
  2∤-1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  bits-equal : ∀ {a b} → IsBit a → IsBit b → (+ 2) ∣ (a - b) →
               0ℤ ∣ (a - b)
  bits-equal (inj₁ refl) (inj₁ refl) _ = i∣0
  bits-equal (inj₁ refl) (inj₂ refl) h = contradiction h 2∤-1
  bits-equal (inj₂ refl) (inj₁ refl) h = contradiction h 2∤1
  bits-equal (inj₂ refl) (inj₂ refl) _ = i∣0

-- So the Boolean-valued lift of a parity function is unique, coefficient
-- by coefficient: whatever decomposition a lifting follows, the result
-- is the same polynomial.

lift-unique : (P Q : Poly n m) → BoolValued P → BoolValued Q →
              (∀ (x : Fin n → Bool) (y : Fin m → Bool) →
                 (+ 2) ∣ (eval P x y - eval Q x y)) →
              ∀ γ → P γ ≡ Q γ
lift-unique P Q bP bQ h γ = i-j≡0⇒i≡j (P γ) (Q γ) (0∣⇒≡0
  (≈-from-values {c = 0ℤ} P Q (λ x y → bits-equal (bP x y) (bQ x y) (h x y)) γ))


------------------------------------------------------------------------
-- The linear [HH] as an instance of the general one

-- [HH] with the linear quotient c ⊕ ⨁S (v ∈ S) matches y₀ against
-- ½ · liftXor c S; the general rule wants ½ · (v + Q) with Q free of v.
-- They agree modulo 2 with Q the lifting on S ∖ v: the values are
-- q + b(1 - 2q) and b + q, which differ by 2bq.

liftXor-split-≈ : (c : Bool) (S : Mon n m) (v : Var n m) → v ∈ᵐ S →
                  liftXor c S ≈[ + 2 ] (μ v +ᴾ liftXor c (S ∖ᵐ v))
liftXor-split-≈ c S v v∈S =
  ≈-from-values (liftXor c S) (μ v +ᴾ liftXor c (S ∖ᵐ v)) λ x y →
    let b = if valᵛ v x y then 1ℤ else 0ℤ
        q = eval (liftXor c (S ∖ᵐ v)) x y
    in divides (- (b * q)) (trans
         (cong₂ _-_ (liftXor-split c S v v∈S x y)
           (trans (eval-+ᴾ (μ v) (liftXor c (S ∖ᵐ v)) x y)
                  (cong (_+ q) (eval-μᴾ v x y))))
         (shape b q))
  where
  shape : ∀ b q → (q + (b * (1ℤ - ((+ 2) * q)))) - (b + q) ≡
                  (- (b * q)) * (+ 2)
  shape = solve 2 (λ b q →
    (q :+ (b :* (con 1ℤ :- (con (+ 2) :* q)))) :- (b :+ q) :=
    (:- (b :* q)) :* con (+ 2)) refl

liftXor-Absent : (c : Bool) (S : Mon n m) (v : Var n m) →
                 Absent v (liftXor c (S ∖ᵐ v))
liftXor-Absent c S v γ v∈γ = liftXor-0 c (S ∖ᵐ v) γ v v∈γ (v∉S∖v S v)


------------------------------------------------------------------------
-- Lifting a Boolean polynomial read modulo 2

-- ⊕ folded over all subsets, in the order of Σsub, and over all
-- monomials, in the order of Σmon.

⨁sub : ∀ {j} → (Subset j → Poly n m) → Poly n m
⨁sub {j = zero}  F = F []
⨁sub {j = suc j} F =
  ⨁sub (λ s → F (inside ∷ s)) ⊕ᴾ ⨁sub (λ s → F (outside ∷ s))

⨁mon : (Mon n m → Poly n m) → Poly n m
⨁mon F = ⨁sub (λ α → ⨁sub (λ β → F (α , β)))

-- The lift of f: the ⊕ of the monomials whose coefficient in f is odd.

liftᴮ : Poly n m → Poly n m
liftᴮ f = ⨁mon (λ γ → if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ)

-- A fold of Boolean-valued polynomials is Boolean-valued.

BoolValued-⨁sub : ∀ {j} (F : Subset j → Poly n m) →
                  (∀ s → BoolValued (F s)) → BoolValued (⨁sub F)
BoolValued-⨁sub {j = zero}  F h = h []
BoolValued-⨁sub {j = suc j} F h =
  BoolValued-⊕ᴾ {A = ⨁sub (λ s → F (inside ∷ s))}
                {B = ⨁sub (λ s → F (outside ∷ s))}
    (BoolValued-⨁sub (λ s → F (inside ∷ s)) (λ s → h (inside ∷ s)))
    (BoolValued-⨁sub (λ s → F (outside ∷ s)) (λ s → h (outside ∷ s)))

BoolValued-liftᴮ : (f : Poly n m) → BoolValued (liftᴮ f)
BoolValued-liftᴮ {n} {m} f =
  BoolValued-⨁sub (λ α → ⨁sub (λ β → G (α , β))) (λ α →
    BoolValued-⨁sub (λ β → G (α , β)) (λ β →
      pick (α , β) ⌊ (+ 2) ∣? f (α , β) ⌋))
  where
  G : Mon n m → Poly n m
  G γ = if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ

  pick : ∀ γ b → BoolValued (if b then 0ᴾ else monoᴾ γ)
  pick γ true  = BoolValued-0ᴾ
  pick γ false = BoolValued-monoᴾ γ

-- Congruence modulo d is transitive and summable.

private
  ∣-telescope : ∀ {d} a b e → d ∣ (a - b) → d ∣ (b - e) → d ∣ (a - e)
  ∣-telescope {d} a b e h₁ h₂ =
    subst (d ∣_) (tele a b e) (∣m∣n⇒∣m+n h₁ h₂)
    where
    tele : ∀ a b e → (a - b) + (b - e) ≡ a - e
    tele = solve 3 (λ a b e → (a :- b) :+ (b :- e) := a :- e) refl

  Σsub-≡ : ∀ {d j} (f g : Subset j → ℤ) → (∀ s → d ∣ (f s - g s)) →
           d ∣ (Σsub f - Σsub g)
  Σsub-≡ {d} f g h = subst (d ∣_)
    (trans (Σsub-+ f (λ s → - g s)) (cong (λ z → Σsub f + z) (Σsub-neg g)))
    (Σsub-∣ (λ s → f s - g s) h)

  Σmon-≡ : ∀ {d} (f g : Mon n m → ℤ) → (∀ γ → d ∣ (f γ - g γ)) →
           d ∣ (Σmon f - Σmon g)
  Σmon-≡ {d = d} f g h = subst (d ∣_)
    (trans (Σmon-+ f (λ γ → - g γ)) (cong (λ z → Σmon f + z) (Σmon-neg g)))
    (Σmon-∣ (λ γ → f γ - g γ) h)

-- a ⊕ b ≡ a + b modulo 2, whatever a and b are, so a fold of ⊕ is
-- congruent to the sum.

⨁sub-≡₂ : ∀ {j} (F : Subset j → Poly n m)
          (x : Fin n → Bool) (y : Fin m → Bool) →
          (+ 2) ∣ (eval (⨁sub F) x y - Σsub (λ s → eval (F s) x y))
⨁sub-≡₂ {j = zero}  F x y =
  subst ((+ 2) ∣_) (sym (+-inverseʳ (eval (F []) x y))) i∣0
⨁sub-≡₂ {n} {m} {j = suc j} F x y = subst ((+ 2) ∣_)
  (sym (trans (cong (_- (σ₁ + σ₀)) (eval-⊕ᴾ A₁ A₀ x y))
              (shape a₁ a₀ σ₁ σ₀)))
  (∣m∣n⇒∣m+n (∣m∣n⇒∣m+n (⨁sub-≡₂ F₁ x y) (⨁sub-≡₂ F₀ x y))
             (divides (- (a₁ * a₀)) refl))
  where
  F₁ F₀ : Subset j → Poly n m
  F₁ u = F (inside ∷ u)
  F₀ u = F (outside ∷ u)

  A₁ A₀ : Poly n m
  A₁ = ⨁sub F₁
  A₀ = ⨁sub F₀

  a₁ a₀ σ₁ σ₀ : ℤ
  a₁ = eval A₁ x y
  a₀ = eval A₀ x y
  σ₁ = Σsub (λ u → eval (F₁ u) x y)
  σ₀ = Σsub (λ u → eval (F₀ u) x y)

  shape : ∀ a b s t →
          ((a + b) - ((+ 2) * (a * b))) - (s + t) ≡
          ((a - s) + (b - t)) + ((- (a * b)) * (+ 2))
  shape = solve 4 (λ a b s t →
    ((a :+ b) :- (con (+ 2) :* (a :* b))) :- (s :+ t) :=
    ((a :- s) :+ (b :- t)) :+ ((:- (a :* b)) :* con (+ 2))) refl

⨁mon-≡₂ : (F : Mon n m → Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          (+ 2) ∣ (eval (⨁mon F) x y - Σmon (λ γ → eval (F γ) x y))
⨁mon-≡₂ F x y = ∣-telescope
  (eval (⨁mon F) x y)
  (Σsub (λ α → eval (⨁sub (λ β → F (α , β))) x y))
  (Σmon (λ γ → eval (F γ) x y))
  (⨁sub-≡₂ (λ α → ⨁sub (λ β → F (α , β))) x y)
  (Σsub-≡ (λ α → eval (⨁sub (λ β → F (α , β))) x y)
          (λ α → Σsub (λ β → eval (F (α , β)) x y))
          (λ α → ⨁sub-≡₂ (λ β → F (α , β)) x y))

-- Term by term: a monomial with odd coefficient contributes its value,
-- 0 or 1, where f contributes the odd coefficient; one with even
-- coefficient contributes nothing, where f contributes an even number.

private
  one-minus-odd : ∀ z → ¬ ((+ 2) ∣ z) → (+ 2) ∣ (1ℤ - z)
  one-minus-odd z ¬2∣z with parity z
  ... | inj₁ (r , z≡) = contradiction (divides r z≡) ¬2∣z
  ... | inj₂ (r , z≡) =
        divides (- r) (trans (cong (λ w → 1ℤ - w) z≡) (calc r))
    where
    calc : ∀ r → 1ℤ - ((r * (+ 2)) + 1ℤ) ≡ (- r) * (+ 2)
    calc = solve 1 (λ r →
      con 1ℤ :- ((r :* con (+ 2)) :+ con 1ℤ) := (:- r) :* con (+ 2)) refl

  even-term : ∀ (s : Bool) {z} → (+ 2) ∣ z →
              (+ 2) ∣ (0ℤ - (if s then z else 0ℤ))
  even-term true  {z} h =
    subst ((+ 2) ∣_) (sym (+-identityˡ (- z))) (∣m⇒∣-m h)
  even-term false     _ = i∣0

  odd-term : ∀ (s : Bool) {z} → ¬ ((+ 2) ∣ z) →
             (+ 2) ∣ ((if s then 1ℤ else 0ℤ) - (if s then z else 0ℤ))
  odd-term true  {z} h = one-minus-odd z h
  odd-term false     _ = i∣0

  term-≡₂ : (f : Poly n m) (γ : Mon n m)
            (x : Fin n → Bool) (y : Fin m → Bool) →
            (+ 2) ∣ (eval (if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ) x y -
                     (if satᵐ γ x y then f γ else 0ℤ))
  term-≡₂ f γ x y = go ((+ 2) ∣? f γ)
    where
    go : (d : Dec ((+ 2) ∣ f γ)) →
         (+ 2) ∣ (eval (if ⌊ d ⌋ then 0ᴾ else monoᴾ γ) x y -
                  (if satᵐ γ x y then f γ else 0ℤ))
    go (yes 2∣f) =
      subst (λ e → (+ 2) ∣ (e - (if satᵐ γ x y then f γ else 0ℤ)))
            (sym (eval-0ᴾ x y)) (even-term (satᵐ γ x y) 2∣f)
    go (no ¬2∣f) =
      subst (λ e → (+ 2) ∣ (e - (if satᵐ γ x y then f γ else 0ℤ)))
            (sym (eval-monoᴾ γ x y)) (odd-term (satᵐ γ x y) ¬2∣f)

-- Lemma 2.5: the lift takes the values of f modulo 2 (and, by
-- BoolValued-liftᴮ, only the values 0 and 1).

lemma-2-5 : (f : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
            (+ 2) ∣ (eval (liftᴮ f) x y - eval f x y)
lemma-2-5 f x y = ∣-telescope
  (eval (liftᴮ f) x y)
  (Σmon (λ γ → eval (if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ) x y))
  (eval f x y)
  (⨁mon-≡₂ (λ γ → if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ) x y)
  (Σmon-≡ (λ γ → eval (if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ) x y)
          (λ γ → if satᵐ γ x y then f γ else 0ℤ)
          (λ γ → term-≡₂ f γ x y))

-- Hence, by Möbius inversion, the lift has f's coefficients modulo 2.

liftᴮ-≈ : (f : Poly n m) → liftᴮ f ≈[ + 2 ] f
liftᴮ-≈ f = ≈-from-values (liftᴮ f) f (lemma-2-5 f)
