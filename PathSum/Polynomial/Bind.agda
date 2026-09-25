------------------------------------------------------------------------
-- Presentations of groups
--
-- Simultaneous substitution of polynomials for variables
--
-- Definition 2.6 of Amy's "Towards Large-scale Functional Verification
-- of Universal Quantum Circuits" (QPL 2018) composes two path-sums by
-- substitution: every input variable x′ᵢ of the second is replaced by
-- the (lifted) output f̄ᵢ of the first, and every path variable y′ⱼ by
-- a fresh path variable.  That is one simultaneous substitution
-- between two variable contexts, bind P σ, which replaces every
-- variable v of P by the polynomial σ v.  A monomial x^α y^β becomes
-- the product of the σ v with v in it (prodᵛ), and bind P σ is the sum
-- of these products weighted by P's coefficients.  PathSum.Polynomial.
-- Substitution's substᴾ replaces one variable only, and inside one
-- context; bind is the general form, and a renaming of variables is
-- the instance at monic σ (rename).
--
-- bind is a dense sum over every monomial of the source and every one
-- of the target, so it is opaque: nothing ever computes a coefficient
-- of it.  Everything about it is reached through its evaluation,
-- eval-bind: when every σ v takes a Boolean value at a point (the
-- value of v at another point x′, y′), bind P σ takes there the value
-- of P at x′, y′.  Nothing else is asked of σ -- in particular it
-- need not be Boolean-valued away from the point of evaluation.
-- Where coefficients matter, Möbius inversion (PathSum.Mobius) brings
-- statements about values back to coefficients: poly-ext says that
-- two polynomials with the same values are equal coefficient by
-- coefficient.
--
-- Lemma 2.5 in exact form is also here, since composition feeds the
-- *lifted* outputs of one path-sum into the other.  PathSum.Polynomial.
-- Boolean lifts a Boolean polynomial f (a Poly read modulo 2) to liftᴮ f
-- and proves the paper's statement, that the lift agrees with f modulo
-- 2 (lemma-2-5), and that it is Boolean-valued (BoolValued-liftᴮ).
-- Together these pin the value down: eval-liftᴮ says it is the bit
-- odd (eval f x y), with odd spelled exactly as PathSum.Denotation
-- reads an output, so that odd (eval (out ξ w) x y) and outBit ξ x y w
-- are the same term.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Bind where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣m∣n⇒∣m+n; ∣m⇒∣-m; ∣⇒∣ᵤ; 0∣⇒≡0)
open import Data.Integer.Properties using
  (*-identityʳ; *-zeroʳ; +-inverseʳ; i-j≡0⇒i≡j)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; _-ᴾ_; κ; μ; Σsub; Σmon; sat; satᵐ; eval)
open import PathSum.Polynomial.Boolean using
  (IsBit; liftᴮ; BoolValued-liftᴮ; lemma-2-5)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ)
open import PathSum.Polynomial.Properties using
  (Σsub-cong; Σsub-swap; Σmon-cong; Σmon-scale; if-pullᵐ; if-scale;
   eval-−ᴾ; eval-κ; valᵛ; i∣0)

open +-*-Solver using (solve; _:+_; _:-_; :-_; _:=_)

private
  variable
    n m k l : ℕ


------------------------------------------------------------------------
-- Exchanging sums over monomials of two contexts

-- PathSum.Polynomial.Properties.Σmon-swap with the two monomial types
-- allowed to differ; Σsub-swap already is.

Σmon-swapʰ : (F : Mon n m → Mon k l → ℤ) →
             Σmon (λ γ → Σmon (λ δ → F γ δ)) ≡
             Σmon (λ δ → Σmon (λ γ → F γ δ))
Σmon-swapʰ F =
  trans (Σsub-cong (λ α →
          Σsub-swap (λ β α′ → Σsub (λ β′ → F (α , β) (α′ , β′)))))
  (trans (Σsub-swap (λ α α′ →
          Σsub (λ β → Σsub (λ β′ → F (α , β) (α′ , β′)))))
  (trans (Σsub-cong (λ α′ → Σsub-cong (λ α →
          Σsub-swap (λ β β′ → F (α , β) (α′ , β′)))))
         (Σsub-cong (λ α′ →
          Σsub-swap (λ α β′ → Σsub (λ β → F (α , β) (α′ , β′)))))))


------------------------------------------------------------------------
-- Products of the substituted polynomials

-- The constant polynomial 1, the empty product.

1ᴾ : Poly n m
1ᴾ = κ 1ℤ

-- ∏_{i ∈ α} σ i.

prodˢ : ∀ {j} → Subset j → (Fin j → Poly n m) → Poly n m
prodˢ []            σ = 1ᴾ
prodˢ (inside  ∷ α) σ = σ zero *ᴾ prodˢ α (λ i → σ (suc i))
prodˢ (outside ∷ α) σ = prodˢ α (λ i → σ (suc i))

-- The image of the monomial x^α y^β: the product of the images of its
-- variables.

prodᵛ : (Var k l → Poly n m) → Mon k l → Poly n m
prodᵛ σ (α , β) = prodˢ α (λ i → σ x[ i ]) *ᴾ prodˢ β (λ j → σ y[ j ])

-- The arithmetic of bits.

private
  bit-∧ : ∀ a b → [ a ]ᶻ * [ b ]ᶻ ≡ [ a ∧ b ]ᶻ
  bit-∧ true  true  = refl
  bit-∧ true  false = refl
  bit-∧ false true  = refl
  bit-∧ false false = refl

  scale-bit : ∀ p b → p * [ b ]ᶻ ≡ (if b then p else 0ℤ)
  scale-bit p true  = *-identityʳ p
  scale-bit p false = *-zeroʳ p

-- Where every factor takes the value of a bit, the product takes the
-- value of their conjunction: a monomial is satisfied exactly when
-- all its variables are.

eval-prodˢ : ∀ {j} (α : Subset j) (σ : Fin j → Poly n m) (f : Fin j → Bool)
             (x : Fin n → Bool) (y : Fin m → Bool) →
             (∀ i → eval (σ i) x y ≡ [ f i ]ᶻ) →
             eval (prodˢ α σ) x y ≡ [ sat α f ]ᶻ
eval-prodˢ []            σ f x y h = eval-κ 1ℤ x y
eval-prodˢ (inside  ∷ α) σ f x y h = trans
  (eval-*ᴾ (σ zero) (prodˢ α (λ i → σ (suc i))) x y)
  (trans (cong₂ _*_ (h zero)
           (eval-prodˢ α (λ i → σ (suc i)) (λ i → f (suc i)) x y
                       (λ i → h (suc i))))
         (bit-∧ (f zero) (sat α (λ i → f (suc i)))))
eval-prodˢ (outside ∷ α) σ f x y h =
  eval-prodˢ α (λ i → σ (suc i)) (λ i → f (suc i)) x y (λ i → h (suc i))

eval-prodᵛ : (σ : Var k l → Poly n m) (γ : Mon k l)
             (x : Fin n → Bool) (y : Fin m → Bool)
             (x′ : Fin k → Bool) (y′ : Fin l → Bool) →
             (∀ v → eval (σ v) x y ≡ [ valᵛ v x′ y′ ]ᶻ) →
             eval (prodᵛ σ γ) x y ≡ [ satᵐ γ x′ y′ ]ᶻ
eval-prodᵛ σ (α , β) x y x′ y′ h = trans
  (eval-*ᴾ (prodˢ α (λ i → σ x[ i ])) (prodˢ β (λ j → σ y[ j ])) x y)
  (trans (cong₂ _*_ (eval-prodˢ α (λ i → σ x[ i ]) x′ x y (λ i → h x[ i ]))
                    (eval-prodˢ β (λ j → σ y[ j ]) y′ x y (λ j → h y[ j ])))
         (bit-∧ (sat α x′) (sat β y′)))


------------------------------------------------------------------------
-- Simultaneous substitution

-- bind P σ replaces every variable v of P by σ v: the coefficient of δ
-- collects, over every monomial γ of P, P's coefficient of γ times the
-- coefficient of δ in the image of γ.

opaque
  bind : Poly k l → (Var k l → Poly n m) → Poly n m
  bind P σ δ = Σmon (λ γ → P γ * prodᵛ σ γ δ)

  -- The value of bind P σ at x, y is that of P at x′, y′, as soon as
  -- every σ v takes at x, y the value of v at x′, y′.  The guard is
  -- pushed inside, the two sums exchanged, and what is left is P's
  -- coefficient times the value of the image of each monomial, a bit.

  eval-bind : (P : Poly k l) (σ : Var k l → Poly n m)
              (x : Fin n → Bool) (y : Fin m → Bool)
              (x′ : Fin k → Bool) (y′ : Fin l → Bool) →
              (∀ v → eval (σ v) x y ≡ [ valᵛ v x′ y′ ]ᶻ) →
              eval (bind P σ) x y ≡ eval P x′ y′
  eval-bind P σ x y x′ y′ h = trans
    (Σmon-cong (λ δ → sym (if-pullᵐ (satᵐ δ x y) (λ γ → P γ * prodᵛ σ γ δ))))
    (trans (Σmon-swapʰ (λ δ γ → if satᵐ δ x y then P γ * prodᵛ σ γ δ
                                else 0ℤ))
    (trans (Σmon-cong (λ γ → trans
             (Σmon-cong (λ δ → if-scale (satᵐ δ x y) (P γ) (prodᵛ σ γ δ)))
             (Σmon-scale {z = P γ}
               (λ δ → if satᵐ δ x y then prodᵛ σ γ δ else 0ℤ))))
           (Σmon-cong (λ γ → trans
             (cong (P γ *_) (eval-prodᵛ σ γ x y x′ y′ h))
             (scale-bit (P γ) (satᵐ γ x′ y′))))))

-- Renaming variables: the substitution by monic polynomials.

rename : (Var k l → Var n m) → Poly k l → Poly n m
rename ρ P = bind P (λ v → μ (ρ v))

eval-rename : (ρ : Var k l → Var n m) (P : Poly k l)
              (x : Fin n → Bool) (y : Fin m → Bool) →
              eval (rename ρ P) x y ≡
              eval P (λ i → valᵛ (ρ x[ i ]) x y) (λ j → valᵛ (ρ y[ j ]) x y)
eval-rename ρ P x y =
  eval-bind P (λ v → μ (ρ v)) x y
    (λ i → valᵛ (ρ x[ i ]) x y) (λ j → valᵛ (ρ y[ j ]) x y) monic
  where
  monic : ∀ v → eval (μ (ρ v)) x y ≡
                [ valᵛ v (λ i → valᵛ (ρ x[ i ]) x y)
                         (λ j → valᵛ (ρ y[ j ]) x y) ]ᶻ
  monic x[ i ] = eval-μᴾ (ρ x[ i ]) x y
  monic y[ j ] = eval-μᴾ (ρ y[ j ]) x y


------------------------------------------------------------------------
-- Values determine coefficients

-- Möbius uniqueness at c = 0: polynomials taking the same value at
-- every Boolean point have the same coefficients.

poly-ext : (P Q : Poly n m) →
           (∀ (x : Fin n → Bool) (y : Fin m → Bool) →
              eval P x y ≡ eval Q x y) →
           ∀ γ → P γ ≡ Q γ
poly-ext P Q h γ = i-j≡0⇒i≡j (P γ) (Q γ) (0∣⇒≡0
  (values⇒coefficientsᵐ 0ℤ (P -ᴾ Q)
    (λ x y → subst (0ℤ ∣_) (sym (diff x y)) i∣0) γ))
  where
  diff : ∀ x y → eval (P -ᴾ Q) x y ≡ 0ℤ
  diff x y = trans (eval-−ᴾ P Q x y)
    (trans (cong (_- eval Q x y) (h x y)) (+-inverseʳ (eval Q x y)))


------------------------------------------------------------------------
-- Lemma 2.5 in exact form

-- The parity of an integer, spelled exactly as PathSum.Denotation
-- reads an output polynomial, so that outBit ξ x y w is, by
-- definition, odd (eval (out ξ w) x y).

odd : ℤ → Bool
odd z = not ⌊ (+ 2) ∣? z ⌋

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  -- d ∣ a - b together with d dividing one of a and b gives the other.

  ∣-fwd : ∀ {d} a b → d ∣ (a - b) → d ∣ a → d ∣ b
  ∣-fwd {d} a b h ha =
    subst (d ∣_) (shape a b) (∣m∣n⇒∣m+n ha (∣m⇒∣-m h))
    where
    shape : ∀ a b → a + (- (a - b)) ≡ b
    shape = solve 2 (λ a b → a :+ (:- (a :- b)) := b) refl

  ∣-back : ∀ {d} a b → d ∣ (a - b) → d ∣ b → d ∣ a
  ∣-back {d} a b h hb = subst (d ∣_) (shape a b) (∣m∣n⇒∣m+n h hb)
    where
    shape : ∀ a b → (a - b) + b ≡ a
    shape = solve 2 (λ a b → (a :- b) :+ b := a) refl

  -- A bit congruent to b modulo 2 is b's parity.

  bit-parity : ∀ {a b} → IsBit a → (+ 2) ∣ (a - b) →
               (d : Dec ((+ 2) ∣ b)) → a ≡ [ not ⌊ d ⌋ ]ᶻ
  bit-parity (inj₁ refl) h (yes _)    = refl
  bit-parity (inj₁ refl) h (no ¬2∣b)  =
    contradiction (∣-fwd 0ℤ _ h i∣0) ¬2∣b
  bit-parity (inj₂ refl) h (yes 2∣b)  =
    contradiction (∣-back 1ℤ _ h 2∣b) 2∤1
  bit-parity (inj₂ refl) h (no _)     = refl

-- The lift of any Boolean polynomial f takes exactly the value of f
-- modulo 2, as 0 or 1.

eval-liftᴮ : (f : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (liftᴮ f) x y ≡ [ odd (eval f x y) ]ᶻ
eval-liftᴮ f x y = bit-parity (BoolValued-liftᴮ f x y) (lemma-2-5 f x y)
                              ((+ 2) ∣? eval f x y)
