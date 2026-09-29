------------------------------------------------------------------------
-- Presentations of groups
--
-- Coefficients modulo 2^M, and the coefficients of a lifted linear
-- form, in the cost model (for Amy, QPL 2018, lemma 2.13)
--
-- A phase coefficient is the numerator over 2^M of a dyadic number,
-- kept modulo 2^M because e^(2πi P) reads P only modulo 1: an element
-- of Fin (2^M), as in PathSum.Size.Sparse, whose residue and coeff
-- convert from and to ℤ.  Adding, multiplying, negating, testing for 0
-- and comparing such numbers are the cost model's primitive steps on
-- "numbers below 2^M": one step each.
--
-- Stated here:
--
--  * congruence modulo 2^M on ℤ (_≡ᴹ_), and that residue is the
--    function it quotients by (coeff-residue, residue-coeff,
--    residue-≡ᴹ): every correctness proof about the sparse algorithms
--    is a congruence modulo 2^M;
--  * the operations _+ᶠ_, _*ᶠ_, -ᶠ_ and the tests isZero and _==ᶠ_, and
--    what they compute modulo 2^M;
--  * (-2)^k modulo 2^M, by k doublings (negpowᶜ);
--  * the coefficient a · λ(c, δ) of the submonomial δ in a times the
--    lifting of c ⊕ ⨁S -- the paper's (-2)^(|δ|-1) of lemma 2.13, with
--    1 ⊕ P = 1 - P for c, and c itself at δ = 1 -- computed from the
--    degree of δ alone (ltermᶜ).  Its value is PathSum.Size.Terms.lterm,
--    so that module's liftTerms, and all it proves, is what the sparse
--    substitution of PathSum.Cost.Subst computes.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Coeff (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective; toℕ<n)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _^_ to _^ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣m⇒∣-m; ∣n⇒∣m*n; ∣⇒∣ᵤ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _^_; _≤_; _<_; _≡ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Cost
open import PathSum.Cost.Monomial using
  (emptyᵐᶜ; value-emptyᵐᶜ; cost-emptyᵐᶜ; degᵐᶜ; value-degᵐᶜ; cost-degᵐᶜ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Mon; ∥_∥; 1ᵐ; _≟ᵐ_; sgn; negpow)
open import PathSum.Polynomial.Properties using (⌊≟ᵐ1ᵐ⌋; i∣0; emptyᵐ)
open import PathSum.Size.Sparse M using (coeff; residue; residue-∣)
open import PathSum.Size.Terms M using
  (residue-unique; residue-cong; lcoeff; lterm)

import Data.Fin.Subset.Properties as Subset
import Data.Integer.Properties as ℤP
import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Properties as ℕ
import Data.Nat.Solver as ℕSolver
open +-*-Solver using (solve; _:+_; _:-_; :-_; _:*_; con; _:=_)

private
  variable
    n m : ℕ
    a b c a′ b′ : ℤ


------------------------------------------------------------------------
-- Congruence modulo 2^M

-- a ≡ᴹ b says that 2^M divides a - b.  It is a record, not a
-- definition, so that a and b can be inferred from it.

infix 4 _≡ᴹ_

record _≡ᴹ_ (a b : ℤ) : Set where
  constructor modᴹ
  field
    ∣diff : pow M ∣ (a -ℤ b)

open _≡ᴹ_ public

≡ᴹ-reflexive : a ≡ b → a ≡ᴹ b
≡ᴹ-reflexive {a} refl = modᴹ (subst (pow M ∣_) (sym (ℤP.+-inverseʳ a)) i∣0)

≡ᴹ-refl : a ≡ᴹ a
≡ᴹ-refl = ≡ᴹ-reflexive refl

≡ᴹ-sym : a ≡ᴹ b → b ≡ᴹ a
≡ᴹ-sym {a} {b} (modᴹ h) = modᴹ (subst (pow M ∣_) (flip a b) (∣m⇒∣-m h))
  where
  flip : ∀ p q → - (p -ℤ q) ≡ q -ℤ p
  flip = solve 2 (λ p q → :- (p :- q) := q :- p) refl

≡ᴹ-trans : a ≡ᴹ b → b ≡ᴹ c → a ≡ᴹ c
≡ᴹ-trans {a} {b} {c} (modᴹ h₁) (modᴹ h₂) =
  modᴹ (subst (pow M ∣_) (telescope a b c) (∣m∣n⇒∣m+n h₁ h₂))
  where
  telescope : ∀ p q r → (p -ℤ q) +ℤ (q -ℤ r) ≡ p -ℤ r
  telescope = solve 3 (λ p q r → (p :- q) :+ (q :- r) := p :- r) refl

+-≡ᴹ : a ≡ᴹ a′ → b ≡ᴹ b′ → (a +ℤ b) ≡ᴹ (a′ +ℤ b′)
+-≡ᴹ {a} {a′} {b} {b′} (modᴹ h₁) (modᴹ h₂) =
  modᴹ (subst (pow M ∣_) (shuffle a a′ b b′) (∣m∣n⇒∣m+n h₁ h₂))
  where
  shuffle : ∀ p p′ q q′ → (p -ℤ p′) +ℤ (q -ℤ q′) ≡ (p +ℤ q) -ℤ (p′ +ℤ q′)
  shuffle = solve 4 (λ p p′ q q′ →
    (p :- p′) :+ (q :- q′) := (p :+ q) :- (p′ :+ q′)) refl

*-≡ᴹ : ∀ z → a ≡ᴹ b → (z *ℤ a) ≡ᴹ (z *ℤ b)
*-≡ᴹ {a} {b} z (modᴹ h) = modᴹ (subst (pow M ∣_) (distrib z a b) (∣n⇒∣m*n z h))
  where
  distrib : ∀ z p q → z *ℤ (p -ℤ q) ≡ (z *ℤ p) -ℤ (z *ℤ q)
  distrib = solve 3 (λ z p q → z :* (p :- q) := (z :* p) :- (z :* q)) refl

neg-≡ᴹ : a ≡ᴹ b → (- a) ≡ᴹ (- b)
neg-≡ᴹ {a} {b} (modᴹ h) = modᴹ (subst (pow M ∣_) (distrib a b) (∣m⇒∣-m h))
  where
  distrib : ∀ p q → - (p -ℤ q) ≡ (- p) -ℤ (- q)
  distrib = solve 2 (λ p q → :- (p :- q) := (:- p) :- (:- q)) refl

-- A multiple of 2^M is congruent to 0.

≡ᴹ-0 : pow M ∣ a → a ≡ᴹ 0ℤ
≡ᴹ-0 {a} h = modᴹ (subst (pow M ∣_) (sym (ℤP.+-identityʳ a)) h)

0-≡ᴹ : a ≡ᴹ 0ℤ → pow M ∣ a
0-≡ᴹ {a} (modᴹ h) = subst (pow M ∣_) (ℤP.+-identityʳ a) h


------------------------------------------------------------------------
-- Coefficients

Coeff : Set
Coeff = Fin (2 ^ M)

-- The residue of an integer is congruent to it, and it is the only
-- coefficient that is.

coeff-residue : ∀ z → coeff (residue z) ≡ᴹ z
coeff-residue z = ≡ᴹ-sym (modᴹ (residue-∣ z))

residue-coeff : (r : Coeff) → residue (coeff r) ≡ r
residue-coeff r = residue-unique (coeff r) r (∣diff (≡ᴹ-refl {coeff r}))

residue-≡ᴹ : a ≡ᴹ b → residue a ≡ residue b
residue-≡ᴹ {a} {b} (modᴹ h) = residue-cong a b h

≡ᴹ-residue : residue a ≡ residue b → a ≡ᴹ b
≡ᴹ-residue {a} {b} eq = ≡ᴹ-trans (≡ᴹ-sym (coeff-residue a))
  (≡ᴹ-trans (≡ᴹ-reflexive (cong coeff eq)) (coeff-residue b))

-- The coefficient 0.

private
  0<2^M : 0 < 2 ^ M
  0<2^M = ℕ.m^n>0 2 M

0ᶠ : Coeff
0ᶠ = fromℕ< 0<2^M

coeff-0ᶠ : coeff 0ᶠ ≡ 0ℤ
coeff-0ᶠ = cong +_ (toℕ-fromℕ< 0<2^M)

residue-0 : residue 0ℤ ≡ 0ᶠ
residue-0 = residue-unique 0ℤ 0ᶠ (∣diff (≡ᴹ-reflexive (sym coeff-0ᶠ)))

-- The arithmetic, modulo 2^M.

infixl 6 _+ᶠ_
infixl 7 _*ᶠ_

_+ᶠ_ : Coeff → Coeff → Coeff
r +ᶠ s = residue (coeff r +ℤ coeff s)

_*ᶠ_ : Coeff → Coeff → Coeff
r *ᶠ s = residue (coeff r *ℤ coeff s)

-ᶠ_ : Coeff → Coeff
-ᶠ r = residue (- coeff r)

+ᶠ-≡ᴹ : (r s : Coeff) → coeff (r +ᶠ s) ≡ᴹ coeff r +ℤ coeff s
+ᶠ-≡ᴹ r s = coeff-residue (coeff r +ℤ coeff s)

*ᶠ-≡ᴹ : (r s : Coeff) → coeff (r *ᶠ s) ≡ᴹ coeff r *ℤ coeff s
*ᶠ-≡ᴹ r s = coeff-residue (coeff r *ℤ coeff s)

-ᶠ-≡ᴹ : (r : Coeff) → coeff (-ᶠ r) ≡ᴹ - coeff r
-ᶠ-≡ᴹ r = coeff-residue (- coeff r)

-- The tests.

isZero : Coeff → Bool
isZero r = toℕ r ≡ᵇ 0

infix 4 _==ᶠ_

_==ᶠ_ : Coeff → Coeff → Bool
r ==ᶠ s = toℕ r ≡ᵇ toℕ s

private
  ≡ᵇ-true : ∀ {x y} → (x ≡ᵇ y) ≡ true → x ≡ y
  ≡ᵇ-true {x} {y} eq = ℕ.≡ᵇ⇒≡ x y (subst T (sym eq) tt)

isZero-true : (r : Coeff) → isZero r ≡ true → coeff r ≡ 0ℤ
isZero-true r eq = cong +_ (≡ᵇ-true eq)

-- A nonzero coefficient is not 0 modulo 2^M: it lies strictly between
-- 0 and 2^M.

isZero-false : (r : Coeff) → isZero r ≡ false → ¬ (pow M ∣ coeff r)
isZero-false r eq d with toℕ r | toℕ<n r
isZero-false r () d | zero  | _
isZero-false r eq d | suc t | lt =
  ℕ.<-irrefl refl (ℕ.≤-trans lt (ℕDiv.∣⇒≤ (∣⇒∣ᵤ d)))

==ᶠ-true : (r s : Coeff) → (r ==ᶠ s) ≡ true → r ≡ s
==ᶠ-true r s eq = toℕ-injective (≡ᵇ-true eq)

-- The operations and the tests are single steps.

addᶠᶜ mulᶠᶜ : Coeff → Coeff → Cost Coeff
addᶠᶜ r s = step (r +ᶠ s)
mulᶠᶜ r s = step (r *ᶠ s)

negᶠᶜ : Coeff → Cost Coeff
negᶠᶜ r = step (-ᶠ r)

isZeroᶜ : Coeff → Cost Bool
isZeroᶜ r = step (isZero r)

eqᶠᶜ : Coeff → Coeff → Cost Bool
eqᶠᶜ r s = step (r ==ᶠ s)


------------------------------------------------------------------------
-- Powers of -2

-- (-2)^k modulo 2^M, by k doublings with a change of sign.

negpowᶜ : ℕ → Cost Coeff
negpowᶜ zero    = step (residue 1ℤ)
negpowᶜ (suc k) = do
  p ← negpowᶜ k
  step (residue ((- (+ 2)) *ℤ coeff p))


private
  negpow-suc : ∀ k → negpow (suc k) ≡ (- (+ 2)) *ℤ negpow k
  negpow-suc k = trans
    (cong ((-1ℤ *ℤ ((- 1ℤ) ^ℤ k)) *ℤ_) (ℤP.pos-* 2 (2 ^ k)))
    (shuffle ((- 1ℤ) ^ℤ k) (+ (2 ^ k)))
    where
    shuffle : ∀ s t → (-1ℤ *ℤ s) *ℤ ((+ 2) *ℤ t) ≡ (- (+ 2)) *ℤ (s *ℤ t)
    shuffle = solve 2 (λ s t → (con -1ℤ :* s) :* (con (+ 2) :* t) :=
                               (:- con (+ 2)) :* (s :* t)) refl

value-negpowᶜ : ∀ k → value (negpowᶜ k) ≡ residue (negpow k)
value-negpowᶜ zero    = refl
value-negpowᶜ (suc k) = residue-≡ᴹ (≡ᴹ-trans
  (*-≡ᴹ (- (+ 2)) (≡ᴹ-trans (≡ᴹ-reflexive (cong coeff (value-negpowᶜ k)))
                            (coeff-residue (negpow k))))
  (≡ᴹ-reflexive (sym (negpow-suc k))))

cost-negpowᶜ : ∀ k → cost (negpowᶜ k) ≤ suc k
cost-negpowᶜ zero    = s≤s z≤n
cost-negpowᶜ (suc k) = ℕ.≤-trans
  (ℕ.≤-reflexive (ℕ.+-comm (cost (negpowᶜ k)) 1))
  (s≤s (cost-negpowᶜ k))


------------------------------------------------------------------------
-- The coefficients of a lifted linear form

-- r times the coefficient of the submonomial δ in the lifting of
-- c ⊕ ⨁S: r·c at δ = 1, and r·(1 - 2c)(-2)^(|δ|-1) otherwise.  Only
-- the degree of δ is read.

ltermTailᶜ : Coeff → Bool → Mon n m → Cost Coeff
ltermTailᶜ r c δ = do
  s ← degᵐᶜ δ
  p ← negpowᶜ (s ∸ 1)
  q ← (if c then negᶠᶜ p else pure p)
  mulᶠᶜ r q

ltermBranchᶜ : Coeff → Bool → Mon n m → Bool → Cost Coeff
ltermBranchᶜ r c δ e =
  if e then pure (if c then r else 0ᶠ) else ltermTailᶜ r c δ

ltermᶜ : Coeff → Bool → Mon n m → Cost Coeff
ltermᶜ r c δ = emptyᵐᶜ δ >>= ltermBranchᶜ r c δ

-- Its value is PathSum.Size.Terms.lterm.

private
  sgn-≡ᴹ : ∀ (c : Bool) (p : Coeff) {z} → coeff p ≡ᴹ z →
           coeff (value (if c then negᶠᶜ p else pure p)) ≡ᴹ sgn c *ℤ z
  sgn-≡ᴹ true  p {z} h = ≡ᴹ-trans (-ᶠ-≡ᴹ p)
    (≡ᴹ-trans (neg-≡ᴹ h) (≡ᴹ-reflexive (sym (ℤP.-1*i≡-i z))))
  sgn-≡ᴹ false p {z} h = ≡ᴹ-trans h (≡ᴹ-reflexive (sym (ℤP.*-identityˡ z)))

  lterm-empty : (r : Coeff) (c : Bool) →
                (if c then r else 0ᶠ) ≡
                residue (coeff r *ℤ (if c then 1ℤ else 0ℤ))
  lterm-empty r true  = sym (trans (cong residue (ℤP.*-identityʳ (coeff r)))
                                   (residue-coeff r))
  lterm-empty r false = sym (trans (cong residue (ℤP.*-zeroʳ (coeff r)))
                                   residue-0)

  lterm-at : (r : Coeff) (c : Bool) (δ : Mon n m) (b : Bool) →
             ⌊ δ ≟ᵐ 1ᵐ ⌋ ≡ b →
             residue (coeff r *ℤ (if b then (if c then 1ℤ else 0ℤ)
                                  else sgn c *ℤ negpow (∥ δ ∥ ∸ 1))) ≡
             lterm (coeff r) c δ
  lterm-at r c δ b eq = cong (λ b′ → residue (coeff r *ℤ
    (if b′ then (if c then 1ℤ else 0ℤ) else sgn c *ℤ negpow (∥ δ ∥ ∸ 1))))
    (sym eq)

  lterm-by : (r : Coeff) (c : Bool) (δ : Mon n m) → ∀ e → emptyᵐ δ ≡ e →
             value (ltermBranchᶜ r c δ e) ≡ lterm (coeff r) c δ
  lterm-by r c δ true  eq =
    trans (lterm-empty r c) (lterm-at r c δ true (trans (⌊≟ᵐ1ᵐ⌋ δ) eq))
  lterm-by r c δ false eq = trans
    (residue-≡ᴹ (*-≡ᴹ (coeff r) (sgn-≡ᴹ c p
      (≡ᴹ-trans (≡ᴹ-reflexive (cong coeff
        (trans (value-negpowᶜ (value (degᵐᶜ δ) ∸ 1))
               (cong (λ s → residue (negpow (s ∸ 1))) (value-degᵐᶜ δ)))))
        (coeff-residue (negpow (∥ δ ∥ ∸ 1)))))))
    (lterm-at r c δ false (trans (⌊≟ᵐ1ᵐ⌋ δ) eq))
    where
    p = value (negpowᶜ (value (degᵐᶜ δ) ∸ 1))

value-ltermᶜ : (r : Coeff) (c : Bool) (δ : Mon n m) →
               value (ltermᶜ r c δ) ≡ lterm (coeff r) c δ
value-ltermᶜ r c δ = trans
  (cong (λ e → value (ltermBranchᶜ r c δ e)) (value-emptyᵐᶜ δ))
  (lterm-by r c δ (emptyᵐ δ) refl)

-- It costs at most 3 (n + m + 1): the emptiness test and the degree
-- read the monomial, and the power takes at most n + m doublings.

cost-ltermᶜ : (r : Coeff) (c : Bool) (δ : Mon n m) →
              cost (ltermᶜ r c δ) ≤ 3 * suc (n + m)
cost-ltermᶜ {n} {m} r c δ = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-emptyᵐᶜ δ) (branch (value (emptyᵐᶜ δ))))
  (ℕ.≤-reflexive (total (n + m)))
  where
  N = n + m

  deg≤ : value (degᵐᶜ δ) ≤ N
  deg≤ = ℕ.≤-trans (ℕ.≤-reflexive (value-degᵐᶜ δ))
    (ℕ.+-mono-≤ (Subset.∣p∣≤n (proj₁ δ)) (Subset.∣p∣≤n (proj₂ δ)))

  sgn≤ : ∀ (c : Bool) (p : Coeff) →
         cost (if c then negᶠᶜ p else pure p) ≤ 1
  sgn≤ true  p = ℕ.≤-refl
  sgn≤ false p = z≤n

  tail≤ : cost (ltermTailᶜ r c δ) ≤ N + (suc N + (1 + 1))
  tail≤ = ℕ.+-mono-≤ (cost-degᵐᶜ δ) (ℕ.+-mono-≤
    (ℕ.≤-trans (cost-negpowᶜ (value (degᵐᶜ δ) ∸ 1))
               (s≤s (ℕ.≤-trans (ℕ.m∸n≤m (value (degᵐᶜ δ)) 1) deg≤)))
    (ℕ.+-mono-≤ (sgn≤ c _) ℕ.≤-refl))

  branch : ∀ e → cost (ltermBranchᶜ r c δ e) ≤ N + (suc N + (1 + 1))
  branch true  = z≤n
  branch false = tail≤

  total : ∀ N → N + (N + (suc N + (1 + 1))) ≡ 3 * suc N
  total = NS.solve 1 (λ N → N NS.:+ (N NS.:+ ((NS.con 1 NS.:+ N) NS.:+
                              (NS.con 1 NS.:+ NS.con 1))) NS.:=
                            NS.con 3 NS.:* (NS.con 1 NS.:+ N)) refl
    where
    module NS = ℕSolver.+-*-Solver
