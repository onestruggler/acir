------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical sparse phases, and their cost (for Amy, QPL 2018,
-- corollary 2.15 and proposition 3.2)
--
-- A sparse phase is a list of terms (monomial, coefficient mod 2^M),
-- PathSum.Size.Sparse's Term, standing for the sum ⟦ ts ⟧ˢ.  A list may
-- repeat a monomial, carry a coefficient 0, or carry monomials of any
-- degree.  Its canonical form at degree d has none of these: it is
--
--    canonical d P = the terms (δ , P δ mod 2^M) for the monomials δ of
--                    degree at most d, in the order of
--                    PathSum.Size.Monomials.monomials≤, keeping only
--                    those whose coefficient is not 0 mod 2^M,
--
-- PathSum.Size.Sparse's listing sparse d P with its zero terms dropped.
-- canonᶜ computes it from any list, in the cost model: it enumerates
-- the monomials of degree at most d and reads each one's coefficient
-- off the list, adding up the terms on that monomial (coeffOfᶜ) --
-- which merges equal monomials -- and then drops the coefficients that
-- are 0 mod 2^M.  The monomials of degree above d are dropped by not
-- being enumerated; that is exact precisely when they vanish modulo 1,
-- i.e. when the polynomial has degree at most d modulo 1 (Deg≤, which
-- the order bound Ord≤ of definition 2.11 implies,
-- PathSum.CRK.Circuit.Ord≤⇒Deg≤).  Proved:
--
--  * value-canonᶜ: the program computes canonical d ⟦ ts ⟧ˢ;
--  * canonical-≈: under Deg≤ d, the canonical form stands for the
--    polynomial modulo 2^M, coefficient by coefficient; canonical-at
--    gives its coefficients outright;
--  * canonical-cong: it depends on the polynomial only modulo 2^M, so
--    congruent polynomials have literally the same canonical form --
--    this is what "canonical" means here -- and canonical-idem: a
--    canonical form is its own;
--  * canonical-length: at most as many terms as there are monomials of
--    degree at most d, so at most (n + m + 1)^d; each term of degree at
--    most d (canonical-small) and nonzero (canonical-nonzero);
--  * canonical-Ordᵀ: if the polynomial has order at most d, so does
--    every term of the canonical form (Ordᵀ, the order bound of
--    PathSum.Order read term by term), and conversely a list whose every
--    term has order at most d sums to a polynomial of order at most d
--    (Ordᵀ⇒Ord≤);
--  * cost-canonᶜ: canonicalising a list of L terms in n + m variables
--    costs at most (L + 5)(n + m + 2)(n + m + 1)^d: for each of the at
--    most (n + m + 1)^d monomials, one pass over the list comparing
--    monomials at n + m steps each.
--
-- The cost is not optimal -- a sort would do with fewer comparisons --
-- but it is polynomial for fixed d, which is all that is claimed.  It
-- is counted in the cost model of PathSum.Cost: a cost model, not a
-- machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Canon (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_; T)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-trans; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n)
open import Data.Integer.Solver using () renaming (module +-*-Solver to ℤSolver)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)

open import PathSum.Cost
open import PathSum.Cost.Coeff M
open import PathSum.Cost.Monomial using
  (eqMonᶜ; value-eqMonᶜ; cost-eqMonᶜ; monomials≤ᶜ; value-monomials≤ᶜ;
   cost-monomials≤ᶜ)
open import PathSum.CRK.Circuit M using (Deg≤)
open import PathSum.Order M using (Ord≤; pow; val; val≤M; pow-∣)
open import PathSum.Polynomial using (Mon; Poly; ∥_∥; _≟ᵐ_; _≈[_]_)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Properties using
  (i∣0; ⌊≟ᵐ⌋; ≡ᵐᵇ-sym)
open import PathSum.Size.Monomials using
  (cut; monomials≤; monomials≤-small; length-monomials≤)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; residue; sparse; sparse-at; sparse-≈)
open import PathSum.Size.Terms M using (sparse-cong)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    n m d : ℕ


------------------------------------------------------------------------
-- The coefficient of a monomial in a list of terms

-- One pass over the list, adding up (mod 2^M) the coefficients of the
-- terms on the monomial.

coeffOfᶜ : List (Term n m) → Mon n m → Cost Coeff
coeffOfᶜ []             γ = pure 0ᶠ
coeffOfᶜ ((δ , a) ∷ ts) γ = do
  tick
  e ← eqMonᶜ δ γ
  r ← coeffOfᶜ ts γ
  if e then addᶠᶜ a r else pure r

private
  mono-by : (δ γ : Mon n m) →
            monoᴾ δ γ ≡ (if value (eqMonᶜ δ γ) then 1ℤ else 0ℤ)
  mono-by δ γ = cong (λ b → if b then 1ℤ else 0ℤ)
    (trans (⌊≟ᵐ⌋ γ δ) (trans (≡ᵐᵇ-sym γ δ) (sym (value-eqMonᶜ δ γ))))

  add-by : (a r : Coeff) {z : ℤ} → coeff r ≡ᴹ z → ∀ b →
           coeff (value (if b then addᶠᶜ a r else pure r)) ≡ᴹ
           coeff a *ℤ (if b then 1ℤ else 0ℤ) +ℤ z
  add-by a r {z} h true  = ≡ᴹ-trans (+ᶠ-≡ᴹ a r)
    (+-≡ᴹ (≡ᴹ-reflexive (sym (ℤP.*-identityʳ (coeff a)))) h)
  add-by a r {z} h false = ≡ᴹ-trans h (≡ᴹ-reflexive (sym (trans
    (cong (_+ℤ z) (ℤP.*-zeroʳ (coeff a))) (ℤP.+-identityˡ z))))

-- It is the coefficient of the sum, modulo 2^M.

coeffOfᶜ-≡ᴹ : (ts : List (Term n m)) (γ : Mon n m) →
              coeff (value (coeffOfᶜ ts γ)) ≡ᴹ ⟦ ts ⟧ˢ γ
coeffOfᶜ-≡ᴹ []             γ = ≡ᴹ-reflexive coeff-0ᶠ
coeffOfᶜ-≡ᴹ ((δ , a) ∷ ts) γ = ≡ᴹ-trans
  (add-by a (value (coeffOfᶜ ts γ)) (coeffOfᶜ-≡ᴹ ts γ)
          (value (eqMonᶜ δ γ)))
  (≡ᴹ-reflexive (cong (λ z → coeff a *ℤ z +ℤ ⟦ ts ⟧ˢ γ)
                      (sym (mono-by δ γ))))

value-coeffOfᶜ : (ts : List (Term n m)) (γ : Mon n m) →
                 value (coeffOfᶜ ts γ) ≡ residue (⟦ ts ⟧ˢ γ)
value-coeffOfᶜ ts γ =
  trans (sym (residue-coeff _)) (residue-≡ᴹ (coeffOfᶜ-≡ᴹ ts γ))

-- At most n + m + 2 steps per term.

cost-coeffOfᶜ : (ts : List (Term n m)) (γ : Mon n m) →
                cost (coeffOfᶜ ts γ) ≤ length ts * suc (suc (n + m))
cost-coeffOfᶜ             []             γ = z≤n
cost-coeffOfᶜ {n = n} {m} ((δ , a) ∷ ts) γ = s≤s (ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-eqMonᶜ δ γ)
    (ℕ.+-mono-≤ (cost-coeffOfᶜ ts γ) (add≤ (value (eqMonᶜ δ γ)))))
  (ℕ.≤-reflexive (shift (n + m) (length ts * suc (suc (n + m))))))
  where
  add≤ : ∀ b → cost (if b then addᶠᶜ a (value (coeffOfᶜ ts γ))
                     else pure (value (coeffOfᶜ ts γ))) ≤ 1
  add≤ true  = ℕ.≤-refl
  add≤ false = z≤n

  shift : ∀ N X → N + (X + 1) ≡ suc N + X
  shift = solve 2 (λ N X → N :+ (X :+ con 1) := (con 1 :+ N) :+ X) refl


------------------------------------------------------------------------
-- The canonical form

-- A term is kept when its coefficient is not 0 mod 2^M.

nonzero : Term n m → Bool
nonzero t = not (isZero (proj₂ t))

canonical : ℕ → Poly n m → List (Term n m)
canonical d P = keep nonzero (sparse d P)

-- The program: enumerate, read off, drop the zeros.

canonᶜ : ℕ → List (Term n m) → Cost (List (Term n m))
canonᶜ {n} {m} d ts = do
  δs ← monomials≤ᶜ n m d
  cs ← mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) δs
  keepᶜ (λ t → step (nonzero t)) cs

value-canonᶜ : (d : ℕ) (ts : List (Term n m)) →
               value (canonᶜ d ts) ≡ canonical d ⟦ ts ⟧ˢ
value-canonᶜ {n} {m} d ts = trans
  (value-keepᶜ (λ t → step (nonzero t))
    (value (mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ)
                 (value (monomials≤ᶜ n m d)))))
  (cong (keep nonzero) (trans
    (value-mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) (value (monomials≤ᶜ n m d)))
    (trans (cong (map (λ δ → δ , value (coeffOfᶜ ts δ)))
                 (value-monomials≤ᶜ n m d))
           (List.map-cong (λ δ → cong (δ ,_) (value-coeffOfᶜ ts δ))
                          (monomials≤ n m d)))))


------------------------------------------------------------------------
-- What the canonical form stands for

-- Dropping zero coefficients does not change the sum.

⟦keep-nonzero⟧ : (ts : List (Term n m)) (γ : Mon n m) →
                 ⟦ keep nonzero ts ⟧ˢ γ ≡ ⟦ ts ⟧ˢ γ
⟦keep-nonzero⟧ []             γ = refl
⟦keep-nonzero⟧ ((δ , a) ∷ ts) γ = by (isZero a) refl
  where
  by : ∀ b → isZero a ≡ b →
       ⟦ (if not b then (δ , a) ∷ keep nonzero ts else keep nonzero ts) ⟧ˢ γ
       ≡ coeff a *ℤ monoᴾ δ γ +ℤ ⟦ ts ⟧ˢ γ
  by true  eq = trans (⟦keep-nonzero⟧ ts γ) (sym (trans
    (cong (λ z → z *ℤ monoᴾ δ γ +ℤ ⟦ ts ⟧ˢ γ) (isZero-true a eq))
    (ℤP.+-identityˡ (⟦ ts ⟧ˢ γ))))
  by false eq = cong (coeff a *ℤ monoᴾ δ γ +ℤ_) (⟦keep-nonzero⟧ ts γ)

-- Its coefficients: that of the polynomial, mod 2^M, up to degree d.

canonical-at : (d : ℕ) (P : Poly n m) (γ : Mon n m) →
               ⟦ canonical d P ⟧ˢ γ ≡ cut d ∥ γ ∥ (coeff (residue (P γ)))
canonical-at d P γ = trans (⟦keep-nonzero⟧ (sparse d P) γ) (sparse-at d P γ)

-- Under the degree bound it stands for the polynomial modulo 2^M.

canonical-≈ : (d : ℕ) (P : Poly n m) → Deg≤ d P →
              P ≈[ pow M ] ⟦ canonical d P ⟧ˢ
canonical-≈ d P deg γ =
  subst (λ z → pow M ∣ (P γ -ℤ z)) (sym (⟦keep-nonzero⟧ (sparse d P) γ))
        (sparse-≈ d P deg γ)

-- It depends on the polynomial only modulo 2^M.

canonical-cong : (d : ℕ) {P Q : Poly n m} → P ≈[ pow M ] Q →
                 canonical d P ≡ canonical d Q
canonical-cong d {P} {Q} P≈Q =
  cong (keep nonzero) (sparse-cong d {P = P} {Q = Q} P≈Q)

-- A map agreeing with another on the cells of a list.

map-congᴬ : ∀ {A B : Set} {f g : A → B} {xs : List A} →
            All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
map-congᴬ []         = refl
map-congᴬ (px ∷ pxs) = cong₂ _∷_ px (map-congᴬ pxs)

private
  cut-≤ : ∀ {s d} (z : ℤ) → s ≤ d → cut d s z ≡ z
  cut-≤ {s} {d} z s≤d =
    cong (λ b → if b then z else 0ℤ) (by (s ≤ᵇ d) refl)
    where
    by : ∀ b → (s ≤ᵇ d) ≡ b → b ≡ true
    by true  _  = refl
    by false eq = ⊥-elim (subst T eq (ℕ.≤⇒≤ᵇ s≤d))

-- A canonical form is its own canonical form.

canonical-idem : (d : ℕ) (P : Poly n m) →
                 canonical d ⟦ canonical d P ⟧ˢ ≡ canonical d P
canonical-idem {n} {m} d P = cong (keep nonzero) (map-congᴬ
  (All.map (λ {δ} δ≤d → cong (δ ,_) (trans
     (cong residue (trans (canonical-at d P δ)
                          (cut-≤ (coeff (residue (P δ))) δ≤d)))
     (residue-coeff (residue (P δ)))))
   (monomials≤-small n m d)))

-- So the program's output is canonical.

Canonical : ℕ → List (Term n m) → Set
Canonical d ts = ts ≡ canonical d ⟦ ts ⟧ˢ

canonᶜ-Canonical : (d : ℕ) (ts : List (Term n m)) →
                   Canonical d (value (canonᶜ d ts))
canonᶜ-Canonical d ts = trans (value-canonᶜ d ts) (trans
  (sym (canonical-idem d ⟦ ts ⟧ˢ))
  (cong (λ us → canonical d ⟦ us ⟧ˢ) (sym (value-canonᶜ d ts))))


------------------------------------------------------------------------
-- Its shape

-- At most one term per monomial of degree at most d, so at most
-- (n + m + 1)^d terms.

canonical-length-mon : (d : ℕ) (P : Poly n m) →
                       length (canonical d P) ≤ length (monomials≤ n m d)
canonical-length-mon {n} {m} d P = ℕ.≤-trans
  (keep-length nonzero (sparse d P))
  (ℕ.≤-reflexive (List.length-map (λ δ → δ , residue (P δ))
                                  (monomials≤ n m d)))

canonical-length : (d : ℕ) (P : Poly n m) →
                   length (canonical d P) ≤ suc (n + m) ^ d
canonical-length {n} {m} d P =
  ℕ.≤-trans (canonical-length-mon d P) (length-monomials≤ n m d)

-- Every term has degree at most d, and a coefficient that is not 0.

canonical-small : (d : ℕ) (P : Poly n m) →
                  All (λ t → ∥ proj₁ t ∥ ≤ d) (canonical d P)
canonical-small {n} {m} d P = keep-All nonzero (sparse d P)
  (AllP.map⁺ {f = λ δ → δ , residue (P δ)} (monomials≤-small n m d))

canonical-nonzero : (d : ℕ) (P : Poly n m) →
                    All (λ t → nonzero t ≡ true) (canonical d P)
canonical-nonzero d P = keep-true nonzero (sparse d P)


------------------------------------------------------------------------
-- The order of the terms

-- Every term of the list has order at most d: its coefficient is
-- divisible by 2^(M - (d + 1 - |δ|)), as definition 2.11 asks of the
-- coefficient of a monomial of degree |δ|.

Ordᵀ : ℕ → List (Term n m) → Set
Ordᵀ d ts = All (λ t → pow (val d ∥ proj₁ t ∥) ∣ coeff (proj₂ t)) ts

-- A divisor of the modulus is blind to congruence.

∣-≡ᴹ : ∀ {e a b} → e ≤ M → pow e ∣ a → a ≡ᴹ b → pow e ∣ b
∣-≡ᴹ {e} {a} {b} e≤M h (modᴹ h′) = subst (pow e ∣_) (cancel a b)
  (∣m∣n⇒∣m-n h (∣-trans (pow-∣ e≤M) h′))
  where
  cancel : ∀ a b → a -ℤ (a -ℤ b) ≡ b
  cancel = ℤSolver.solve 2 (λ a b → a ℤSolver.:- (a ℤSolver.:- b)
                                    ℤSolver.:= b) refl

-- A polynomial of order at most d has a canonical form of order at
-- most d, term by term.

canonical-Ordᵀ : (d : ℕ) (P : Poly n m) → Ord≤ d P → Ordᵀ d (canonical d P)
canonical-Ordᵀ {n} {m} d P ordP = keep-All nonzero (sparse d P)
  (AllP.map⁺ {f = λ δ → δ , residue (P δ)}
    (All.universal (λ δ → ∣-≡ᴹ (val≤M d ∥ δ ∥) (ordP δ)
                            (≡ᴹ-sym (coeff-residue (P δ))))
                   (monomials≤ n m d)))

-- A sum of terms of order at most d has order at most d.

Ordᵀ⇒Ord≤ : {ts : List (Term n m)} → Ordᵀ d ts → Ord≤ d ⟦ ts ⟧ˢ
Ordᵀ⇒Ord≤         {ts = []}           []       γ = i∣0
Ordᵀ⇒Ord≤ {d = d} {ts = (δ , a) ∷ ts} (h ∷ hs) γ =
  ∣m∣n⇒∣m+n term (Ordᵀ⇒Ord≤ hs γ)
  where
  term : pow (val d ∥ γ ∥) ∣ (coeff a *ℤ monoᴾ δ γ)
  term with γ ≟ᵐ δ
  ... | yes refl = subst (pow (val d ∥ γ ∥) ∣_)
                         (sym (ℤP.*-identityʳ (coeff a))) h
  ... | no  _    = subst (pow (val d ∥ γ ∥) ∣_)
                         (sym (ℤP.*-zeroʳ (coeff a))) i∣0


------------------------------------------------------------------------
-- The cost of canonicalising

-- With K monomials of degree at most d: 3 (n + m + 2) K to enumerate
-- them, K (1 + L (n + m + 2)) to read off their coefficients, and 2 K
-- to drop the zeros -- at most (L + 5)(n + m + 2) K in all.

private
  total : ∀ N L K →
          3 * (2 + N) * K + (K * suc (L * (2 + N)) + K * 2) + K * (2 * N + 1)
          ≡ (L + 5) * (2 + N) * K
  total = solve 3 (λ N L K →
    con 3 :* (con 2 :+ N) :* K :+
      (K :* (con 1 :+ L :* (con 2 :+ N)) :+ K :* con 2) :+
      K :* (con 2 :* N :+ con 1) :=
    (L :+ con 5) :* (con 2 :+ N) :* K) refl

cost-canonᶜ : (d : ℕ) (ts : List (Term n m)) →
              cost (canonᶜ d ts) ≤
              (length ts + 5) * suc (suc (n + m)) * suc (n + m) ^ d
cost-canonᶜ {n} {m} d ts = ℕ.≤-trans
  (ℕ.+-mono-≤ enum (ℕ.+-mono-≤ reads drops))
  (ℕ.≤-trans (ℕ.m≤m+n _ (K * (2 * N + 1)))
    (ℕ.≤-trans (ℕ.≤-reflexive (total N L K))
               (ℕ.*-monoʳ-≤ ((L + 5) * (2 + N)) (length-monomials≤ n m d))))
  where
  N = n + m
  L = length ts
  δs = value (monomials≤ᶜ n m d)
  K = length (monomials≤ n m d)

  lenδs : length δs ≡ K
  lenδs = cong length (value-monomials≤ᶜ n m d)

  enum : cost (monomials≤ᶜ n m d) ≤ 3 * (2 + N) * K
  enum = ℕ.≤-trans (cost-monomials≤ᶜ n m d)
    (ℕ.≤-reflexive (cong (λ x → 3 * suc x * K) (ℕ.+-suc n m)))

  reads : cost (mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) δs) ≤
          K * suc (L * (2 + N))
  reads = ℕ.≤-trans
    (cost-mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) δs (cost-coeffOfᶜ ts))
    (ℕ.≤-reflexive (cong (_* suc (L * (2 + N))) lenδs))

  drops : cost (keepᶜ (λ t → step (nonzero t))
                      (value (mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) δs)))
          ≤ K * 2
  drops = ℕ.≤-trans
    (cost-keepᶜ (λ t → step (nonzero t))
      (value (mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) δs)) (λ _ → ℕ.≤-refl))
    (ℕ.≤-reflexive (cong (_* 2) (trans
      (cong length (value-mapᶜ (λ δ → (δ ,_) <$> coeffOfᶜ ts δ) δs))
      (trans (List.length-map (λ δ → δ , value (coeffOfᶜ ts δ)) δs) lenδs))))
