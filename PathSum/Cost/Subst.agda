------------------------------------------------------------------------
-- Presentations of groups
--
-- Substituting a lifted linear form for a path variable, on the sparse
-- representation (for Amy, QPL 2018, lemma 2.13 and the rule [HH])
--
-- [HH] replaces a path variable y_i by a Z₂-linear form c ⊕ ⨁S, in the
-- phase and in the outputs: P[y_i ← c ⊕ ⨁S], with the form lifted to
-- a polynomial over D (PathSum.Polynomial.subst).  Densely the
-- substitution is a double sum over all monomials; here it is computed
-- on a sparse phase, term by term.
--
-- A term a · x^γ not containing y_i is kept.  A term a · y_i · x^δ
-- becomes a · x^δ times the lifting of the form, which is, by the
-- expansion of the proof of lemma 2.13,
--
--    c + (1 - 2c) Σ_{∅ ≠ S′ ⊆ S} (-2)^(|S′| - 1) x^S′ ,
--
-- one term per submonomial S′ of S -- 2^|S| of them.  Only those with
-- |S′| ≤ d are written down (expandᵀ, through PathSum.Size.Terms.
-- liftTerms, whose coefficients PathSum.Cost.Coeff.ltermᶜ computes):
-- the others are integers, and vanish modulo 1, as soon as the phase
-- has order at most d -- the coefficient a of a monomial of degree at
-- least 1 is then divisible by 2^(M - d), and (-2)^(|S′| - 1) by 2^d
-- (deg-lift).  That is lemma 2.13's order bound, and it is what keeps
-- the sparse substitution sparse: at most (n + m + 1)^d new terms per
-- old one, where the full expansion would have 2^|S|.  The result is
-- then canonicalised at degree d (substᶜ).
--
-- Proved:
--
--  * expand-≈: under the order bound Ordᵀ d, term by term, the
--    expansion stands for the dense substitution modulo 2^M,
--    coefficient by coefficient.  The proof goes through values:
--    at every Boolean point the expansion takes the value of the
--    phase at the point with y_i set to the value of the form
--    (expand-val) -- which is the value of the dense substitution,
--    PathSum.Polynomial.Substitution.eval-substᴾ-≔ -- and Möbius
--    inversion (PathSum.Polynomial.Boolean.≈-from-values) turns equal
--    values modulo 2^M into equal coefficients modulo 2^M;
--  * substᶜ-≈ and substᶜ-Ordᵀ: after canonicalising, the result still
--    stands for the substitution, and its terms still have order at
--    most d (lemma 2.13, PathSum.Order.subst-Ord≤);
--  * on the outputs, substituting into a form c′ ⊕ ⨁T containing y_i
--    gives the form (c′ ⊕ ⨁(T ∖ y_i)) ⊕ (c ⊕ ⨁S), and the dense
--    substitution into the lifting is, coefficient by coefficient and
--    exactly, the lifting of that form (subst-lift, by values and
--    Möbius at modulus 0: PathSum.Polynomial.Bind.poly-ext);
--  * cost-substᶜ: at most 13 (N + 1)^(d+1) steps per term to expand,
--    N = n + m, and the canonicalisation of the at most L (N + 1)^d
--    terms that result.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Subst (M : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-assoc; xor-comm)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside; ∣_∣)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-trans; *-monoˡ-∣; *-monoʳ-∣)
open import Data.List.Base using
  (List; []; _∷_; _++_; map; length; concat; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _^_; _≤_; _<_; z≤n; s≤s; >-nonZero)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)

open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Cost
open import PathSum.Cost.Canon M using
  (canonᶜ; canonical; value-canonᶜ; canonical-≈; canonical-Ordᵀ; Ordᵀ;
   Ordᵀ⇒Ord≤; cost-canonᶜ)
open import PathSum.Cost.Coeff M using
  (Coeff; _≡ᴹ_; modᴹ; ∣diff; ≡ᴹ-refl; ≡ᴹ-reflexive; ≡ᴹ-sym; ≡ᴹ-trans;
   +-≡ᴹ; ltermᶜ; value-ltermᶜ; cost-ltermᶜ)
open import PathSum.Cost.Monomial using
  (clear; clearᶜ; value-clearᶜ; cost-clearᶜ; unionᵐᶜ; value-unionᵐᶜ;
   cost-unionᵐᶜ; xorᵐᶜ; value-xorᵐᶜ; cost-xorᵐᶜ; subᵐ≤ᶜ; value-subᵐ≤ᶜ;
   cost-subᵐ≤ᶜ)
open import PathSum.CRK.Circuit M using (Deg≤; Ord≤⇒Deg≤)
open import PathSum.Linear using
  (Lin; liftᴸ; valᴸ; par; par-cong; _⊕ᴸ_; _⊕ᵐ_; eval-liftᴸ; eval-liftXor;
   valᴸ-⊕)
open import PathSum.Order M using
  (Ord≤; Ord≤-cong; pow; val; val-mono; pow-∣; pow-+; subst-Ord≤)
open import PathSum.Polynomial using
  (Mon; Poly; y[_]; ∥_∥; _∪ᵐ_; _≈[_]_; _·ᴾ_; liftXor; sat; satᵐ; eval)
  renaming (subst to psubst)
open import PathSum.Polynomial.Bind using (poly-ext)
open import PathSum.Polynomial.Boolean using (≈-from-values)
open import PathSum.Polynomial.Product using (≈-trans)
open import PathSum.Polynomial.Properties using
  (satᵐ-∪; sat-cong; eval-≈; eval-·ᴾ; liftXor-∣)
open import PathSum.Polynomial.Substitution using (eval-substᴾ-≔)
open import PathSum.Size.Monomials using (Σˡ; Σˡ-++; Σˡ-map; Σˡ-cong)
open import PathSum.Size.Sparse M using (Term; coeff; ⟦_⟧ˢ; eval-⟦⟧ˢ)
open import PathSum.Size.Submonomials using (subᵐ≤; length-subᵐ≤)
open import PathSum.Size.Terms M using
  (liftTerms; liftTerms-≈; liftTerms-length≤)

import Data.Fin.Properties as Fin
import Data.Fin.Subset.Properties as Subset
import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import Data.Vec.Properties as Vec

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- The truncated lifting, in the monad

-- The terms of r times the lifting of c ⊕ ⨁S on the submonomials of S
-- of degree at most d: PathSum.Size.Terms.liftTerms, computed.

liftTermsᶜ : Coeff → ℕ → Lin n m → Cost (List (Term n m))
liftTermsᶜ r d (c , (α , β)) = do
  δs ← subᵐ≤ᶜ α β d
  mapᶜ (λ δ → (δ ,_) <$> ltermᶜ r c δ) δs

value-liftTermsᶜ : (r : Coeff) (d : ℕ) (l : Lin n m) →
                   value (liftTermsᶜ r d l) ≡ liftTerms (coeff r) d l
value-liftTermsᶜ r d (c , (α , β)) = trans
  (value-mapᶜ (λ δ → (δ ,_) <$> ltermᶜ r c δ) (value (subᵐ≤ᶜ α β d)))
  (trans (cong (map (λ δ → δ , value (ltermᶜ r c δ))) (value-subᵐ≤ᶜ α β d))
         (List.map-cong (λ δ → cong (δ ,_) (value-ltermᶜ r c δ))
                        (subᵐ≤ α β d)))


------------------------------------------------------------------------
-- The expansion

-- A term multiplied by a monomial.

mulᵀ : Mon n m → Term n m → Term n m
mulᵀ δ (γ , a) = (δ ∪ᵐ γ) , a

mulᶜ : Mon n m → Term n m → Cost (Term n m)
mulᶜ δ (γ , a) = (λ γ′ → γ′ , a) <$> unionᵐᶜ δ γ

value-mulᶜ : (δ : Mon n m) (t : Term n m) → value (mulᶜ δ t) ≡ mulᵀ δ t
value-mulᶜ δ (γ , a) = cong (_, a) (value-unionᵐᶜ δ γ)

-- One term: kept if it does not contain y_i; otherwise y_i is removed
-- and the rest multiplied by the truncated lifting.

expandᵀ : ℕ → Fin m → Lin n m → Term n m → List (Term n m)
expandᵀ d i l ((α , β) , a) =
  if lookup β i then map (mulᵀ (α , clear β i)) (liftTerms (coeff a) d l)
  else ((α , β) , a) ∷ []

expand : ℕ → Fin m → Lin n m → List (Term n m) → List (Term n m)
expand d i l = concatMap (expandᵀ d i l)

-- The programs.

expandInᶜ : ℕ → Fin m → Lin n m → Subset n → Subset m → Coeff →
            Cost (List (Term n m))
expandInᶜ d i l α β a = do
  β′ ← clearᶜ β i
  us ← liftTermsᶜ a d l
  mapᶜ (mulᶜ (α , β′)) us

expandBranchᶜ : ℕ → Fin m → Lin n m → Subset n → Subset m → Coeff →
                Bool → Cost (List (Term n m))
expandBranchᶜ d i l α β a b =
  if b then expandInᶜ d i l α β a else pure (((α , β) , a) ∷ [])

expandᵀᶜ : ℕ → Fin m → Lin n m → Term n m → Cost (List (Term n m))
expandᵀᶜ d i l ((α , β) , a) = lookupᶜ β i >>= expandBranchᶜ d i l α β a

expandᶜ : ℕ → Fin m → Lin n m → List (Term n m) → Cost (List (Term n m))
expandᶜ d i l = concatMapᶜ (expandᵀᶜ d i l)

value-expandInᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (α : Subset n)
                  (β : Subset m) (a : Coeff) →
                  value (expandInᶜ d i l α β a) ≡
                  map (mulᵀ (α , clear β i)) (liftTerms (coeff a) d l)
value-expandInᶜ d i l α β a = trans
  (value-mapᶜ (mulᶜ (α , value (clearᶜ β i))) (value (liftTermsᶜ a d l)))
  (trans (List.map-cong (value-mulᶜ (α , value (clearᶜ β i)))
                        (value (liftTermsᶜ a d l)))
    (cong₂ (λ β′ us → map (mulᵀ (α , β′)) us)
           (value-clearᶜ β i) (value-liftTermsᶜ a d l)))

value-expandᵀᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (t : Term n m) →
                 value (expandᵀᶜ d i l t) ≡ expandᵀ d i l t
value-expandᵀᶜ d i l ((α , β) , a) = trans
  (cong (λ b → value (expandBranchᶜ d i l α β a b)) (value-lookupᶜ β i))
  (branch (lookup β i))
  where
  branch : ∀ b → value (expandBranchᶜ d i l α β a b) ≡
                 (if b then map (mulᵀ (α , clear β i))
                                (liftTerms (coeff a) d l)
                  else ((α , β) , a) ∷ [])
  branch true  = value-expandInᶜ d i l α β a
  branch false = refl

value-expandᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (ts : List (Term n m)) →
                value (expandᶜ d i l ts) ≡ expand d i l ts
value-expandᶜ d i l ts = trans (value-concatMapᶜ (expandᵀᶜ d i l) ts)
  (cong concat (List.map-cong (value-expandᵀᶜ d i l) ts))


------------------------------------------------------------------------
-- Values of lists of terms

-- The value of the sum of a list of terms at a Boolean point.

valˢ : (Fin n → Bool) → (Fin m → Bool) → List (Term n m) → ℤ
valˢ x y ts =
  Σˡ ts (λ t → if satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ)

private
  Σˡ-0 : ∀ {A : Set} (as : List A) → Σˡ as (λ _ → 0ℤ) ≡ 0ℤ
  Σˡ-0 []       = refl
  Σˡ-0 (a ∷ as) = trans (ℤP.+-identityˡ (Σˡ as (λ _ → 0ℤ))) (Σˡ-0 as)

-- Multiplying every term by x^δ multiplies the value by that of x^δ.

valˢ-mul : (δ : Mon n m) (us : List (Term n m)) (x : Fin n → Bool)
           (y : Fin m → Bool) →
           valˢ x y (map (mulᵀ δ) us) ≡
           (if satᵐ δ x y then valˢ x y us else 0ℤ)
valˢ-mul δ us x y = trans
  (Σˡ-map (mulᵀ δ) us
    (λ t → if satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ))
  (by (satᵐ δ x y) refl)
  where
  sat-mul : ∀ s → satᵐ δ x y ≡ s → (t : Term _ _) →
            (if satᵐ (proj₁ (mulᵀ δ t)) x y then coeff (proj₂ t) else 0ℤ) ≡
            (if s ∧ satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ)
  sat-mul s eq (γ , a) = cong (λ b → if b then coeff a else 0ℤ)
    (trans (satᵐ-∪ δ γ x y) (cong (_∧ satᵐ γ x y) eq))

  by : ∀ s → satᵐ δ x y ≡ s →
       Σˡ us (λ t → if satᵐ (proj₁ (mulᵀ δ t)) x y
                    then coeff (proj₂ t) else 0ℤ) ≡
       (if s then valˢ x y us else 0ℤ)
  by true  eq = Σˡ-cong us (sat-mul true eq)
  by false eq = trans (Σˡ-cong us (sat-mul false eq)) (Σˡ-0 us)

-- The truncated lifting, scaled by a coefficient divisible by
-- 2^(M - d), vanishes modulo 1 above degree d.

private
  ≤∸+ : ∀ a b → a ≤ (a ∸ b) + b
  ≤∸+ zero    b       = z≤n
  ≤∸+ (suc a) zero    = ℕ.≤-reflexive (sym (ℕ.+-identityʳ (suc a)))
  ≤∸+ (suc a) (suc b) = ℕ.≤-trans (s≤s (≤∸+ a b))
                                  (ℕ.≤-reflexive (sym (ℕ.+-suc (a ∸ b) b)))

deg-lift : (a : Coeff) (d : ℕ) (l : Lin n m) → pow (M ∸ d) ∣ coeff a →
           Deg≤ d (coeff a ·ᴾ liftᴸ l)
deg-lift a d (c , S) h γ d<γ = ∣-trans (pow-∣ bound)
  (subst (_∣ (coeff a *ℤ liftXor c S γ)) (pow-+ (M ∸ d) (∥ γ ∥ ∸ 1))
    (∣-trans (*-monoˡ-∣ (pow (∥ γ ∥ ∸ 1)) h)
             (*-monoʳ-∣ (coeff a) (liftXor-∣ c S γ))))
  where
  bound : M ≤ (M ∸ d) + (∥ γ ∥ ∸ 1)
  bound = ℕ.≤-trans (≤∸+ M d) (ℕ.+-monoʳ-≤ (M ∸ d) (ℕ.∸-monoˡ-≤ 1 d<γ))

-- So its value is a times the value of the form, modulo 2^M.

lift-val : (a : Coeff) (d : ℕ) (l : Lin n m) → pow (M ∸ d) ∣ coeff a →
           (x : Fin n → Bool) (y : Fin m → Bool) →
           valˢ x y (liftTerms (coeff a) d l) ≡ᴹ coeff a *ℤ [ valᴸ l x y ]ᶻ
lift-val a d l h x y = ≡ᴹ-trans
  (≡ᴹ-reflexive (sym (eval-⟦⟧ˢ (liftTerms (coeff a) d l) x y)))
  (≡ᴹ-trans
    (≡ᴹ-sym (modᴹ (eval-≈ (coeff a ·ᴾ liftᴸ l) ⟦ liftTerms (coeff a) d l ⟧ˢ
      (liftTerms-≈ (coeff a) d l (deg-lift a d l h)) x y)))
    (≡ᴹ-reflexive (trans (eval-·ᴾ (coeff a) (liftᴸ l) x y)
                         (cong (coeff a *ℤ_) (eval-liftᴸ l x y)))))


------------------------------------------------------------------------
-- Satisfaction and parity with one path bit overwritten

private
  ∧-mid : ∀ a b c → a ∧ (b ∧ c) ≡ b ∧ (a ∧ c)
  ∧-mid true  b     c = refl
  ∧-mid false true  c = refl
  ∧-mid false false c = refl

-- Overwriting bit suc i, read past the first bit, is overwriting bit i
-- of the tail (pointwise: Fin's _≟_ at suc is a map′, which isYes does
-- not see through).

≔-suc : (f : Fin (suc k) → Bool) (i : Fin k) (b : Bool) (l : Fin k) →
        (f [ suc i ≔ b ]) (suc l) ≡ ((λ l → f (suc l)) [ i ≔ b ]) l
≔-suc f i b l with l Fin.≟ i
... | yes _ = refl
... | no  _ = refl

sat-≔-in : (β : Subset k) (i : Fin k) (f : Fin k → Bool) (b : Bool) →
           lookup β i ≡ true → sat β (f [ i ≔ b ]) ≡ b ∧ sat (clear β i) f
sat-≔-in (inside  ∷ β) zero    f b eq = refl
sat-≔-in (outside ∷ β) zero    f b ()
sat-≔-in (inside  ∷ β) (suc i) f b eq = trans
  (cong (f zero ∧_) (trans (sat-cong β (≔-suc f i b))
                           (sat-≔-in β i (λ l → f (suc l)) b eq)))
  (∧-mid (f zero) b (sat (clear β i) (λ l → f (suc l))))
sat-≔-in (outside ∷ β) (suc i) f b eq =
  trans (sat-cong β (≔-suc f i b)) (sat-≔-in β i (λ l → f (suc l)) b eq)

sat-≔-out : (β : Subset k) (i : Fin k) (f : Fin k → Bool) (b : Bool) →
            lookup β i ≡ false → sat β (f [ i ≔ b ]) ≡ sat β f
sat-≔-out (inside  ∷ β) zero    f b ()
sat-≔-out (outside ∷ β) zero    f b eq = refl
sat-≔-out (inside  ∷ β) (suc i) f b eq = cong (f zero ∧_)
  (trans (sat-cong β (≔-suc f i b)) (sat-≔-out β i (λ l → f (suc l)) b eq))
sat-≔-out (outside ∷ β) (suc i) f b eq =
  trans (sat-cong β (≔-suc f i b)) (sat-≔-out β i (λ l → f (suc l)) b eq)

par-≔-in : (β : Subset k) (i : Fin k) (f : Fin k → Bool) (b : Bool) →
           lookup β i ≡ true → par β (f [ i ≔ b ]) ≡ par (clear β i) f xor b
par-≔-in (inside  ∷ β) zero    f b eq = xor-comm b (par β (λ l → f (suc l)))
par-≔-in (outside ∷ β) zero    f b ()
par-≔-in (inside  ∷ β) (suc i) f b eq = trans
  (cong (f zero xor_) (trans (par-cong β (≔-suc f i b))
                             (par-≔-in β i (λ l → f (suc l)) b eq)))
  (sym (xor-assoc (f zero) (par (clear β i) (λ l → f (suc l))) b))
par-≔-in (outside ∷ β) (suc i) f b eq =
  trans (par-cong β (≔-suc f i b)) (par-≔-in β i (λ l → f (suc l)) b eq)

par-≔-out : (β : Subset k) (i : Fin k) (f : Fin k → Bool) (b : Bool) →
            lookup β i ≡ false → par β (f [ i ≔ b ]) ≡ par β f
par-≔-out (inside  ∷ β) zero    f b ()
par-≔-out (outside ∷ β) zero    f b eq = refl
par-≔-out (inside  ∷ β) (suc i) f b eq = cong (f zero xor_)
  (trans (par-cong β (≔-suc f i b)) (par-≔-out β i (λ l → f (suc l)) b eq))
par-≔-out (outside ∷ β) (suc i) f b eq =
  trans (par-cong β (≔-suc f i b)) (par-≔-out β i (λ l → f (suc l)) b eq)


------------------------------------------------------------------------
-- The expansion takes the value of the substitution

private
  mix : ∀ (s₁ s₂ b : Bool) (A : ℤ) {X : ℤ} → X ≡ᴹ A *ℤ [ b ]ᶻ →
        (if s₁ ∧ s₂ then X else 0ℤ) ≡ᴹ (if s₁ ∧ (b ∧ s₂) then A else 0ℤ)
  mix true  true  true  A h = ≡ᴹ-trans h (≡ᴹ-reflexive (ℤP.*-identityʳ A))
  mix true  true  false A h = ≡ᴹ-trans h (≡ᴹ-reflexive (ℤP.*-zeroʳ A))
  mix true  false true  A h = ≡ᴹ-refl
  mix true  false false A h = ≡ᴹ-refl
  mix false s₂    b     A h = ≡ᴹ-refl

-- A term's expansion, at a point, is the term at the point with y_i
-- set to the value of the form.

expandᵀ-val : (d : ℕ) (i : Fin m) (l : Lin n m) (t : Term n m)
              (x : Fin n → Bool) (y : Fin m → Bool) →
              (lookup (proj₂ (proj₁ t)) i ≡ true →
               pow (M ∸ d) ∣ coeff (proj₂ t)) →
              valˢ x y (expandᵀ d i l t) ≡ᴹ
              (if satᵐ (proj₁ t) x (y [ i ≔ valᴸ l x y ])
               then coeff (proj₂ t) else 0ℤ)
expandᵀ-val d i l ((α , β) , a) x y h = by (lookup β i) refl
  where
  b = valᴸ l x y

  by : ∀ e → lookup β i ≡ e →
       valˢ x y (if e then map (mulᵀ (α , clear β i))
                               (liftTerms (coeff a) d l)
                 else ((α , β) , a) ∷ []) ≡ᴹ
       (if sat α x ∧ sat β (y [ i ≔ b ]) then coeff a else 0ℤ)
  by true  eq = ≡ᴹ-trans
    (≡ᴹ-reflexive (valˢ-mul (α , clear β i) (liftTerms (coeff a) d l) x y))
    (≡ᴹ-trans (mix (sat α x) (sat (clear β i) y) b (coeff a)
                   (lift-val a d l (h eq) x y))
      (≡ᴹ-reflexive (cong (λ s → if sat α x ∧ s then coeff a else 0ℤ)
                          (sym (sat-≔-in β i y b eq)))))
  by false eq = ≡ᴹ-reflexive (trans
    (ℤP.+-identityʳ (if sat α x ∧ sat β y then coeff a else 0ℤ))
    (cong (λ s → if sat α x ∧ s then coeff a else 0ℤ)
          (sym (sat-≔-out β i y b eq))))

-- The whole list.

expand-val : (d : ℕ) (i : Fin m) (l : Lin n m) (ts : List (Term n m))
             (x : Fin n → Bool) (y : Fin m → Bool) →
             All (λ t → lookup (proj₂ (proj₁ t)) i ≡ true →
                        pow (M ∸ d) ∣ coeff (proj₂ t)) ts →
             valˢ x y (expand d i l ts) ≡ᴹ valˢ x (y [ i ≔ valᴸ l x y ]) ts
expand-val d i l []       x y []       = ≡ᴹ-refl
expand-val d i l (t ∷ ts) x y (h ∷ hs) = ≡ᴹ-trans
  (≡ᴹ-reflexive (Σˡ-++ (expandᵀ d i l t) (expand d i l ts)
    (λ t → if satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ)))
  (+-≡ᴹ (expandᵀ-val d i l t x y h) (expand-val d i l ts x y hs))

-- A term of order at most d containing y_i has degree at least 1, so
-- its coefficient is divisible by 2^(M - d).

private
  lookup-deg : (β : Subset k) (i : Fin k) → lookup β i ≡ true → 1 ≤ ∣ β ∣
  lookup-deg (inside  ∷ β) zero    eq = s≤s z≤n
  lookup-deg (outside ∷ β) zero    ()
  lookup-deg (inside  ∷ β) (suc i) eq = s≤s z≤n
  lookup-deg (outside ∷ β) (suc i) eq = lookup-deg β i eq

Ordᵀ-lead : (d : ℕ) (i : Fin m) (ts : List (Term n m)) → Ordᵀ d ts →
            All (λ t → lookup (proj₂ (proj₁ t)) i ≡ true →
                       pow (M ∸ d) ∣ coeff (proj₂ t)) ts
Ordᵀ-lead d i []                     []       = []
Ordᵀ-lead d i (((α , β) , a) ∷ ts) (h ∷ hs) =
  (λ eq → ∣-trans (pow-∣ (val-mono d (ℕ.≤-trans (lookup-deg β i eq)
                                                (ℕ.m≤n+m ∣ β ∣ ∣ α ∣))))
                  h)
  ∷ Ordᵀ-lead d i ts hs

-- Hence the expansion stands for the dense substitution, modulo 2^M
-- and coefficient by coefficient.

private
  at-subst : (P : Poly n m) (i : Fin m) (c : Bool) (S : Mon n m)
             (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (psubst P y[ i ] c S) x y ≡
             eval P x (y [ i ≔ valᴸ (c , S) x y ])
  at-subst P i c S x y = eval-substᴾ-≔ P i (liftXor c S) x y
    (valᴸ (c , S) x y) (sym (eval-liftXor c S x y))

expand-≈ : (d : ℕ) (i : Fin m) (c : Bool) (S : Mon n m)
           (ts : List (Term n m)) → Ordᵀ d ts →
           psubst ⟦ ts ⟧ˢ y[ i ] c S ≈[ pow M ] ⟦ expand d i (c , S) ts ⟧ˢ
expand-≈ d i c S ts ord =
  ≈-from-values (psubst ⟦ ts ⟧ˢ y[ i ] c S) ⟦ expand d i (c , S) ts ⟧ˢ
    (λ x y → ∣diff (≡ᴹ-trans
      (≡ᴹ-reflexive (trans (at-subst ⟦ ts ⟧ˢ i c S x y)
        (eval-⟦⟧ˢ ts x (y [ i ≔ valᴸ (c , S) x y ]))))
      (≡ᴹ-trans (≡ᴹ-sym (expand-val d i (c , S) ts x y
                                    (Ordᵀ-lead d i ts ord)))
                (≡ᴹ-reflexive (sym (eval-⟦⟧ˢ (expand d i (c , S) ts) x y))))))

-- The dense substitution respects congruence modulo 2^M.

subst-≈ : (i : Fin m) (c : Bool) (S : Mon n m) {P Q : Poly n m} →
          P ≈[ pow M ] Q → psubst P y[ i ] c S ≈[ pow M ] psubst Q y[ i ] c S
subst-≈ i c S {P} {Q} P≈Q =
  ≈-from-values (psubst P y[ i ] c S) (psubst Q y[ i ] c S) (λ x y →
    subst (pow M ∣_)
      (cong₂ _-ℤ_ (sym (at-subst P i c S x y)) (sym (at-subst Q i c S x y)))
      (eval-≈ P Q P≈Q x (y [ i ≔ valᴸ (c , S) x y ])))


------------------------------------------------------------------------
-- Substitution, canonicalised

substᶜ : ℕ → Fin m → Lin n m → List (Term n m) → Cost (List (Term n m))
substᶜ d i l ts = expandᶜ d i l ts >>= canonᶜ d

value-substᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (ts : List (Term n m)) →
               value (substᶜ d i l ts) ≡ canonical d ⟦ expand d i l ts ⟧ˢ
value-substᶜ d i l ts = trans (value-canonᶜ d (value (expandᶜ d i l ts)))
  (cong (λ us → canonical d ⟦ us ⟧ˢ) (value-expandᶜ d i l ts))

-- The expansion has order at most d: lemma 2.13.

expand-Ord≤ : (d : ℕ) (i : Fin m) (c : Bool) (S : Mon n m)
              (ts : List (Term n m)) → Ordᵀ d ts →
              Ord≤ d ⟦ expand d i (c , S) ts ⟧ˢ
expand-Ord≤ d i c S ts ord =
  Ord≤-cong {P = psubst ⟦ ts ⟧ˢ y[ i ] c S} {Q = ⟦ expand d i (c , S) ts ⟧ˢ}
    (expand-≈ d i c S ts ord)
    (subst-Ord≤ ⟦ ts ⟧ˢ y[ i ] c S (Ordᵀ⇒Ord≤ ord))

-- The result stands for the substitution, and keeps the order bound.

substᶜ-≈ : (d : ℕ) (i : Fin m) (c : Bool) (S : Mon n m)
           (ts : List (Term n m)) → Ordᵀ d ts →
           psubst ⟦ ts ⟧ˢ y[ i ] c S ≈[ pow M ]
           ⟦ value (substᶜ d i (c , S) ts) ⟧ˢ
substᶜ-≈ d i c S ts ord =
  ≈-trans {P = psubst ⟦ ts ⟧ˢ y[ i ] c S} {Q = ⟦ expand d i (c , S) ts ⟧ˢ}
          {R = ⟦ value (substᶜ d i (c , S) ts) ⟧ˢ}
    (expand-≈ d i c S ts ord)
    (subst (λ us → ⟦ expand d i (c , S) ts ⟧ˢ ≈[ pow M ] ⟦ us ⟧ˢ)
           (sym (value-substᶜ d i (c , S) ts))
           (canonical-≈ d ⟦ expand d i (c , S) ts ⟧ˢ
             (Ord≤⇒Deg≤ (expand-Ord≤ d i c S ts ord))))

substᶜ-Ordᵀ : (d : ℕ) (i : Fin m) (c : Bool) (S : Mon n m)
              (ts : List (Term n m)) → Ordᵀ d ts →
              Ordᵀ d (value (substᶜ d i (c , S) ts))
substᶜ-Ordᵀ d i c S ts ord =
  subst (Ordᵀ d) (sym (value-substᶜ d i (c , S) ts))
        (canonical-Ordᵀ d ⟦ expand d i (c , S) ts ⟧ˢ
                        (expand-Ord≤ d i c S ts ord))


------------------------------------------------------------------------
-- Substituting into the outputs

-- A form containing y_i gains the substituted form; one not
-- containing it is kept.

substForm : Fin m → Lin n m → Lin n m → Lin n m
substForm i l (c′ , (α , β)) =
  if lookup β i then (c′ , (α , clear β i)) ⊕ᴸ l else (c′ , (α , β))

substFormInᶜ : Fin m → Lin n m → Bool → Subset n → Subset m →
               Cost (Lin n m)
substFormInᶜ i (c , S) c′ α β = do
  β′ ← clearᶜ β i
  T  ← xorᵐᶜ (α , β′) S
  step (c′ xor c , T)

substFormBranchᶜ : Fin m → Lin n m → Bool → Subset n → Subset m → Bool →
                   Cost (Lin n m)
substFormBranchᶜ i l c′ α β b =
  if b then substFormInᶜ i l c′ α β else pure (c′ , (α , β))

substFormᶜ : Fin m → Lin n m → Lin n m → Cost (Lin n m)
substFormᶜ i l (c′ , (α , β)) = lookupᶜ β i >>= substFormBranchᶜ i l c′ α β

substFormsᶜ : Fin m → Lin n m → (Fin n → Lin n m) → Cost (Fin n → Lin n m)
substFormsᶜ i l f = lookup <$> tabulateᶜ (λ w → substFormᶜ i l (f w))

value-substFormᶜ : (i : Fin m) (l l′ : Lin n m) →
                   value (substFormᶜ i l l′) ≡ substForm i l l′
value-substFormᶜ i (c , S) (c′ , (α , β)) = trans
  (cong (λ b → value (substFormBranchᶜ i (c , S) c′ α β b))
        (value-lookupᶜ β i))
  (branch (lookup β i))
  where
  branch : ∀ b → value (substFormBranchᶜ i (c , S) c′ α β b) ≡
                 (if b then (c′ , (α , clear β i)) ⊕ᴸ (c , S)
                  else (c′ , (α , β)))
  branch true  = cong (c′ xor c ,_)
    (trans (value-xorᵐᶜ (α , value (clearᶜ β i)) S)
           (cong (λ β′ → (α , β′) ⊕ᵐ S) (value-clearᶜ β i)))
  branch false = refl

value-substFormsᶜ : (i : Fin m) (l : Lin n m) (f : Fin n → Lin n m)
                    (w : Fin n) →
                    value (substFormsᶜ i l f) w ≡ substForm i l (f w)
value-substFormsᶜ i l f w = trans
  (cong (λ v → lookup v w) (value-tabulateᶜ (λ w → substFormᶜ i l (f w))))
  (trans (Vec.lookup∘tabulate (λ w → value (substFormᶜ i l (f w))) w)
         (value-substFormᶜ i l (f w)))

-- The value of a form with y_i overwritten by the value of another is
-- the value of the substituted form.

valᴸ-substForm : (i : Fin m) (l l′ : Lin n m) (x : Fin n → Bool)
                 (y : Fin m → Bool) →
                 valᴸ l′ x (y [ i ≔ valᴸ l x y ]) ≡ valᴸ (substForm i l l′) x y
valᴸ-substForm i l (c′ , (α , β)) x y = by (lookup β i) refl
  where
  b = valᴸ l x y

  by : ∀ e → lookup β i ≡ e →
       valᴸ (c′ , (α , β)) x (y [ i ≔ b ]) ≡
       valᴸ (if e then (c′ , (α , clear β i)) ⊕ᴸ l else (c′ , (α , β))) x y
  by true  eq = trans
    (cong (λ p → c′ xor (par α x xor p)) (par-≔-in β i y b eq))
    (trans (sym (trans (xor-assoc c′ (par α x xor par (clear β i) y) b)
                  (cong (c′ xor_) (xor-assoc (par α x) (par (clear β i) y) b))))
           (sym (valᴸ-⊕ (c′ , (α , clear β i)) l x y)))
  by false eq = cong (λ p → c′ xor (par α x xor p)) (par-≔-out β i y b eq)

-- So the dense substitution into the lifting of a form is the lifting
-- of the substituted form, coefficient by coefficient.

subst-lift : (i : Fin m) (c : Bool) (S : Mon n m) (l′ : Lin n m) →
             ∀ γ → psubst (liftᴸ l′) y[ i ] c S γ ≡
                   liftᴸ (substForm i (c , S) l′) γ
subst-lift i c S l′ =
  poly-ext (psubst (liftᴸ l′) y[ i ] c S) (liftᴸ (substForm i (c , S) l′))
    (λ x y → trans (at-subst (liftᴸ l′) i c S x y)
      (trans (eval-liftᴸ l′ x (y [ i ≔ valᴸ (c , S) x y ]))
        (trans (cong [_]ᶻ (valᴸ-substForm i (c , S) l′ x y))
               (sym (eval-liftᴸ (substForm i (c , S) l′) x y)))))


------------------------------------------------------------------------
-- Costs

-- Throughout, B = n + m + 1 bounds the number of variables, and B^d
-- the number of submonomials of degree at most d of any monomial.

private
  B^d≥1 : ∀ B d → 1 ≤ suc B ^ d
  B^d≥1 B d = ℕ.m^n>0 (suc B) d

  subᵐ≤-B : (α : Subset n) (β : Subset m) (d : ℕ) →
            length (subᵐ≤ α β d) ≤ suc (n + m) ^ d
  subᵐ≤-B {n} {m} α β d = ℕ.≤-trans (length-subᵐ≤ α β d)
    (ℕ.^-monoˡ-≤ d (s≤s (ℕ.+-mono-≤ (Subset.∣p∣≤n α) (Subset.∣p∣≤n β))))

-- The truncated lifting: the enumeration, and a coefficient per
-- submonomial.

cost-liftTermsᶜ : (r : Coeff) (d : ℕ) (l : Lin n m) →
                  cost (liftTermsᶜ r d l) ≤
                  suc (n + m) ^ d * (6 * suc (n + m) + 4)
cost-liftTermsᶜ {n} {m} r d (c , (α , β)) = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-subᵐ≤ᶜ α β d)
    (cost-mapᶜ (λ δ → (δ ,_) <$> ltermᶜ r c δ) (value (subᵐ≤ᶜ α β d))
               (λ δ → cost-ltermᶜ r c δ)))
  (ℕ.≤-trans (ℕ.≤-reflexive eq) (ℕ.*-monoˡ-≤ (6 * B + 4) (subᵐ≤-B α β d)))
  where
  B = suc (n + m)
  K = length (subᵐ≤ α β d)

  spread : ∀ B K → 3 * suc B * K + K * suc (3 * B) ≡ K * (6 * B + 4)
  spread = solve 2 (λ B K → con 3 :* (con 1 :+ B) :* K :+
                             K :* (con 1 :+ con 3 :* B) :=
                             K :* (con 6 :* B :+ con 4)) refl

  eq : 3 * suc (n + suc m) * K +
       length (value (subᵐ≤ᶜ α β d)) * suc (3 * suc (n + m)) ≡ K * (6 * B + 4)
  eq = trans (cong₂ (λ u v → 3 * suc u * K + v * suc (3 * B))
                    (ℕ.+-suc n m) (cong length (value-subᵐ≤ᶜ α β d)))
             (spread B K)

-- One term.

length-expandᵀ : (d : ℕ) (i : Fin m) (l : Lin n m) (t : Term n m) →
                 length (expandᵀ d i l t) ≤ suc (n + m) ^ d
length-expandᵀ {m} {n} d i l ((α , β) , a) = by (lookup β i)
  where
  by : ∀ e → length (if e then map (mulᵀ (α , clear β i))
                                   (liftTerms (coeff a) d l)
                     else ((α , β) , a) ∷ []) ≤ suc (n + m) ^ d
  by true  = ℕ.≤-trans
    (ℕ.≤-reflexive (List.length-map (mulᵀ (α , clear β i))
                                    (liftTerms (coeff a) d l)))
    (liftTerms-length≤ (coeff a) d l)
  by false = B^d≥1 (n + m) d

private
  -- 2m + (6B + 4)B^d + B·B^d ≤ 13 B·B^d.
  per-term : ∀ {x B P} → x ≤ B → 1 ≤ B → 1 ≤ P →
             x + (x + (P * (6 * B + 4) + P * B)) ≤ 13 * (B * P)
  per-term {x} {B} {P} x≤B 1≤B 1≤P = ℕ.≤-trans
    (ℕ.+-mono-≤ x≤BP (ℕ.+-monoˡ-≤ (P * (6 * B + 4) + P * B) x≤BP))
    (ℕ.≤-trans ℕ.≤-refl
      (ℕ.≤-trans (ℕ.≤-reflexive (e₁ B P))
        (ℕ.≤-trans (ℕ.+-monoʳ-≤ (9 * (B * P)) (ℕ.*-monoʳ-≤ 4 P≤BP))
                   (ℕ.≤-reflexive (e₂ B P)))))
    where
    x≤BP : x ≤ B * P
    x≤BP = ℕ.≤-trans x≤B (ℕ.m≤m*n B P {{>-nonZero 1≤P}})

    P≤BP : P ≤ B * P
    P≤BP = ℕ.m≤n*m P B {{>-nonZero 1≤B}}

    e₁ : ∀ B P → B * P + (B * P + (P * (6 * B + 4) + P * B)) ≡
                 9 * (B * P) + 4 * P
    e₁ = solve 2 (λ B P → B :* P :+ (B :* P :+ (P :* (con 6 :* B :+ con 4)
                            :+ P :* B)) :=
                          con 9 :* (B :* P) :+ con 4 :* P) refl

    e₂ : ∀ B P → 9 * (B * P) + 4 * (B * P) ≡ 13 * (B * P)
    e₂ = solve 2 (λ B P → con 9 :* (B :* P) :+ con 4 :* (B :* P) :=
                          con 13 :* (B :* P)) refl

cost-expandᵀᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (t : Term n m) →
                cost (expandᵀᶜ d i l t) ≤
                13 * (suc (n + m) * suc (n + m) ^ d)
cost-expandᵀᶜ {m} {n} d i l ((α , β) , a) = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-lookupᶜ β i) (branch (value (lookupᶜ β i))))
  (per-term (ℕ.≤-trans (ℕ.m≤n+m m n) (ℕ.n≤1+n (n + m)))
            (s≤s z≤n) (B^d≥1 (n + m) d))
  where
  B = suc (n + m)
  P = B ^ d

  us = value (liftTermsᶜ a d l)

  in≤ : cost (expandInᶜ d i l α β a) ≤ m + (P * (6 * B + 4) + P * B)
  in≤ = ℕ.+-mono-≤ (cost-clearᶜ β i) (ℕ.+-mono-≤ (cost-liftTermsᶜ a d l)
    (ℕ.≤-trans (cost-mapᶜ (mulᶜ (α , value (clearᶜ β i))) us
                 (λ { (γ , _) → cost-unionᵐᶜ (α , value (clearᶜ β i)) γ }))
      (ℕ.*-monoˡ-≤ B (ℕ.≤-trans
        (ℕ.≤-reflexive (cong length (value-liftTermsᶜ a d l)))
        (liftTerms-length≤ (coeff a) d l)))))

  branch : ∀ b → cost (expandBranchᶜ d i l α β a b) ≤
                 m + (P * (6 * B + 4) + P * B)
  branch true  = in≤
  branch false = z≤n

-- A whole list: at most 13 B^(d+1) steps, and B^d new terms, per term.

length-expand : (d : ℕ) (i : Fin m) (l : Lin n m) (ts : List (Term n m)) →
                length (expand d i l ts) ≤ length ts * suc (n + m) ^ d
length-expand d i l ts =
  length-concatMap (expandᵀ d i l) ts (length-expandᵀ d i l)

cost-expandᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (ts : List (Term n m)) →
               cost (expandᶜ d i l ts) ≤
               length ts * suc (13 * (suc (n + m) * suc (n + m) ^ d) +
                                suc (n + m) ^ d)
cost-expandᶜ d i l ts = cost-concatMapᶜ (expandᵀᶜ d i l) ts
  (cost-expandᵀᶜ d i l)
  (λ t → ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-expandᵀᶜ d i l t)))
                   (length-expandᵀ d i l t))

-- Substitution: the expansion, and the canonicalisation of what it
-- produces.

cost-substᶜ : (d : ℕ) (i : Fin m) (l : Lin n m) (ts : List (Term n m)) →
              cost (substᶜ d i l ts) ≤
              length ts * suc (13 * (suc (n + m) * suc (n + m) ^ d) +
                               suc (n + m) ^ d) +
              (length ts * suc (n + m) ^ d + 5) * suc (suc (n + m)) *
              suc (n + m) ^ d
cost-substᶜ {m} {n} d i l ts = ℕ.+-mono-≤ (cost-expandᶜ d i l ts)
  (ℕ.≤-trans (cost-canonᶜ d (value (expandᶜ d i l ts)))
    (ℕ.*-monoˡ-≤ (suc (n + m) ^ d) (ℕ.*-monoˡ-≤ (suc (suc (n + m)))
      (ℕ.+-monoˡ-≤ 5 (ℕ.≤-trans
        (ℕ.≤-reflexive (cong length (value-expandᶜ d i l ts)))
        (length-expand d i l ts))))))

-- The outputs: at most 3B steps per wire.

cost-substFormᶜ : (i : Fin m) (l l′ : Lin n m) →
                  cost (substFormᶜ i l l′) ≤ 3 * suc (n + m)
cost-substFormᶜ {m} {n} i (c , S) (c′ , (α , β)) = ℕ.≤-trans
  (ℕ.+-mono-≤ (ℕ.≤-trans (cost-lookupᶜ β i) m≤B)
              (branch (value (lookupᶜ β i))))
  (ℕ.≤-reflexive (cong (λ z → B + (B + z)) (sym (ℕ.+-identityʳ B))))
  where
  B = suc (n + m)

  m≤B : m ≤ B
  m≤B = ℕ.≤-trans (ℕ.m≤n+m m n) (ℕ.n≤1+n (n + m))

  in≤ : cost (substFormInᶜ i (c , S) c′ α β) ≤ B + B
  in≤ = ℕ.+-mono-≤ (ℕ.≤-trans (cost-clearᶜ β i) m≤B)
    (ℕ.≤-trans (ℕ.+-monoˡ-≤ 1 (cost-xorᵐᶜ (α , value (clearᶜ β i)) S))
               (ℕ.≤-reflexive (ℕ.+-comm (n + m) 1)))

  branch : ∀ b → cost (substFormBranchᶜ i (c , S) c′ α β b) ≤ B + B
  branch true  = in≤
  branch false = z≤n

cost-substFormsᶜ : (i : Fin m) (l : Lin n m) (f : Fin n → Lin n m) →
                   cost (substFormsᶜ i l f) ≤ n * suc (3 * suc (n + m))
cost-substFormsᶜ i l f =
  cost-tabulateᶜ (λ w → substFormᶜ i l (f w)) (λ w → cost-substFormᶜ i l (f w))
