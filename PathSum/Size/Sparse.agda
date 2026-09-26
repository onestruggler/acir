------------------------------------------------------------------------
-- Presentations of groups
--
-- Sparse phase polynomials, and the size of a path-sum (for Amy, QPL
-- 2018, corollary 2.15)
--
-- A polynomial here is a function: Poly n m = Mon n m → ℤ gives the
-- numerator over 2^M of every one of the 2^(n+m) coefficients, so
-- "the size of a polynomial" is not a property of a Poly value.  The
-- size of a path-sum is the size of a representation of it that one
-- would write down, and this module defines one.
--
-- A term is a pair (δ , c) of a monomial δ and a coefficient
-- c ∈ [0, 2^M), standing for c/2^M · x^δ (Term, with c : Fin (2^M));
-- a list of terms stands for their sum (⟦_⟧ˢ, whose value at an
-- assignment is the sum of the coefficients of the monomials it
-- satisfies, eval-⟦⟧ˢ).  A representation (Rep) of a path-sum with n
-- inputs and m path variables is such a list for the phase together
-- with, for each output, a Z₂-linear form of PathSum.Linear, and it
-- represents ξ (Represents ξ R) when the list's sum agrees with the
-- phase of ξ modulo 1 -- coefficient by coefficient modulo 2^M, which
-- is all that e^(2πi P) reads -- and each output of ξ is the lifting
-- of its form, coefficient by coefficient.  The path-sum a
-- representation stands for is psʳ k R; PathSum.Size.Equivalence
-- shows ξ ≋ psʳ k R whenever R represents ξ.
--
-- The size of a representation (size) counts bits: a monomial is a bit
-- vector of length n + m (Subset n × Subset m is Vec Bool n × Vec Bool
-- m) and a coefficient is M bits, so a term is n + m + M bits
-- (termBits); a form c ⊕ ⨁S is one bit and a subset of the n + m
-- variables (formBits, n + m + 1 bits).  The numbers n, m, the
-- normalisation k and the list's length are left out, being
-- logarithmic in what is counted.
--
-- The one construction is sparse d P: the terms (δ , P δ mod 2^M) for
-- every monomial δ of degree at most d, in the order of
-- PathSum.Size.Monomials.monomials≤.  Its sum agrees with P modulo
-- 2^M exactly when P has degree at most d in the sense of
-- PathSum.CRK.Circuit.Deg≤ (every coefficient of degree above d an
-- integer, i.e. its numerator divisible by 2^M): sparse-≈.  It has
-- at most (n + m + 1)^d terms (sparse-length), each of degree at most
-- d (sparse-small).  Terms with coefficient 0 are kept: dropping them
-- would only shorten the list.  Conversely, any list of terms of
-- degree at most d that represents P shows that P has degree at most
-- d modulo 1 (small-Deg≤), so the degree bound is exactly what a
-- representation of degree d needs (Deg≤⇔sparse, represents-Deg≤).
-- represent packages sparse with the forms, and size-bound turns the
-- count into a bound on the size, polynomial in n + m for fixed d and
-- M; size-volume restates it in the volume n · ℓ when n and ℓ are at
-- least 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Size.Sparse (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; T)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; NonZero)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.DivMod using (_/_; _%_; n%d<d; a≡a%n+[a/n]*n)
open import Data.Integer.Divisibility.Signed using (_∣_; divides)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _≤_; _<_; _≤ᵇ_; z≤n; s≤s; >-nonZero)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.CRK.Circuit M using (Deg≤)
open import PathSum.Linear using (Lin; liftᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Mon; Poly; ∥_∥; _≟ᵐ_; 0ᴾ; _+ᴾ_; _·ᴾ_; _≈[_]_; Σmon; satᵐ; eval)
open import PathSum.Polynomial.Product using (monoᴾ; eval-monoᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (Σmon-cong; Σmon-delta; ⌊≟ᵐ⌋; ≡ᵐᵇ-sym; _≡ᵐᵇ_; eval-+ᴾ; eval-·ᴾ)
open import PathSum.Size.Monomials using
  (Σˡ; Σˡ-map; Σˡ-monomials≤; cut; monomials≤; monomials≤-small;
   length-monomials≤)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:-_; _:=_)

private
  variable
    n m k : ℕ


------------------------------------------------------------------------
-- Terms and their sums

-- A term c/2^M · x^δ, the coefficient given by its numerator
-- c ∈ [0, 2^M).

Term : ℕ → ℕ → Set
Term n m = Mon n m × Fin (2 ^ M)

coeff : Fin (2 ^ M) → ℤ
coeff c = + toℕ c

-- A list of terms stands for their sum.

⟦_⟧ˢ : List (Term n m) → Poly n m
⟦ []           ⟧ˢ = 0ᴾ
⟦ (δ , c) ∷ ts ⟧ˢ = (coeff c ·ᴾ monoᴾ δ) +ᴾ ⟦ ts ⟧ˢ

-- Its coefficients, as a sum over the list.

⟦⟧ˢ-at : (ts : List (Term n m)) (γ : Mon n m) →
         ⟦ ts ⟧ˢ γ ≡ Σˡ ts (λ t → coeff (proj₂ t) *ℤ monoᴾ (proj₁ t) γ)
⟦⟧ˢ-at []             γ = refl
⟦⟧ˢ-at ((δ , c) ∷ ts) γ =
  cong (λ z → (coeff c *ℤ monoᴾ δ γ) +ℤ z) (⟦⟧ˢ-at ts γ)

-- Its value at an assignment: the sum of the coefficients of the
-- monomials the assignment satisfies.  So the representation can be
-- evaluated without the dense polynomial.

private
  scale-if : ∀ (b : Bool) (z : ℤ) →
             z *ℤ (if b then 1ℤ else 0ℤ) ≡ (if b then z else 0ℤ)
  scale-if true  z = ℤP.*-identityʳ z
  scale-if false z = ℤP.*-zeroʳ z

eval-⟦⟧ˢ : (ts : List (Term n m)) (x : Fin n → Bool) (y : Fin m → Bool) →
           eval ⟦ ts ⟧ˢ x y ≡
           Σˡ ts (λ t → if satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ)
eval-⟦⟧ˢ []             x y = eval-0ᴾ x y
eval-⟦⟧ˢ ((δ , c) ∷ ts) x y = trans
  (eval-+ᴾ (coeff c ·ᴾ monoᴾ δ) ⟦ ts ⟧ˢ x y)
  (cong₂ _+ℤ_ (trans (eval-·ᴾ (coeff c) (monoᴾ δ) x y)
                     (trans (cong (λ z → coeff c *ℤ z) (eval-monoᴾ δ x y))
                            (scale-if (satᵐ δ x y) (coeff c))))
              (eval-⟦⟧ˢ ts x y))


------------------------------------------------------------------------
-- Coefficients modulo 2^M

private
  2^M≢0 : NonZero (pow M)
  2^M≢0 = ℕ.m^n≢0 2 M

-- The residue of an integer modulo 2^M, as a coefficient.

residue : ℤ → Fin (2 ^ M)
residue z = fromℕ< (n%d<d z (pow M) {{2^M≢0}})

-- It differs from the integer by a multiple of 2^M.

residue-∣ : ∀ z → pow M ∣ (z -ℤ coeff (residue z))
residue-∣ z = divides q (begin
  z -ℤ coeff (residue z)
    ≡⟨ cong (λ w → z -ℤ (+ w)) (toℕ-fromℕ< (n%d<d z (pow M) {{2^M≢0}})) ⟩
  z -ℤ (+ r)
    ≡⟨ cong (λ w → w -ℤ (+ r)) (a≡a%n+[a/n]*n z (pow M) {{2^M≢0}}) ⟩
  ((+ r) +ℤ q *ℤ pow M) -ℤ (+ r)
    ≡⟨ cancel (+ r) (q *ℤ pow M) ⟩
  q *ℤ pow M ∎)
  where
  open ≡-Reasoning

  r : ℕ
  r = _%_ z (pow M) {{2^M≢0}}

  q : ℤ
  q = _/_ z (pow M) {{2^M≢0}}

  cancel : ∀ a b → (a +ℤ b) -ℤ a ≡ b
  cancel = solve 2 (λ a b → (a :+ b) :- a := b) refl


------------------------------------------------------------------------
-- The sparse representation of a polynomial of bounded degree

-- The terms (δ , P δ mod 2^M) for the monomials δ of degree at most d.

sparse : ℕ → Poly n m → List (Term n m)
sparse {n} {m} d P = map (λ δ → δ , residue (P δ)) (monomials≤ n m d)

-- Its coefficient at γ is P γ mod 2^M if γ has degree at most d, and
-- 0 otherwise.

private
  guard : ∀ (b q : Bool) (z : ℤ) →
          (if b then z *ℤ (if q then 1ℤ else 0ℤ) else 0ℤ) ≡
          (if q then (if b then z else 0ℤ) else 0ℤ)
  guard true  true  z = ℤP.*-identityʳ z
  guard true  false z = ℤP.*-zeroʳ z
  guard false true  z = refl
  guard false false z = refl

sparse-at : ∀ d (P : Poly n m) (γ : Mon n m) →
            ⟦ sparse d P ⟧ˢ γ ≡ cut d ∥ γ ∥ (coeff (residue (P γ)))
sparse-at {n} {m} d P γ = begin
  ⟦ sparse d P ⟧ˢ γ
    ≡⟨ ⟦⟧ˢ-at (sparse d P) γ ⟩
  Σˡ (map f (monomials≤ n m d))
     (λ t → coeff (proj₂ t) *ℤ monoᴾ (proj₁ t) γ)
    ≡⟨ Σˡ-map f (monomials≤ n m d)
         (λ t → coeff (proj₂ t) *ℤ monoᴾ (proj₁ t) γ) ⟩
  Σˡ (monomials≤ n m d) (λ δ → c δ *ℤ monoᴾ δ γ)
    ≡⟨ Σˡ-monomials≤ n m d (λ δ → c δ *ℤ monoᴾ δ γ) ⟩
  Σmon (λ δ → cut d ∥ δ ∥ (c δ *ℤ monoᴾ δ γ))
    ≡⟨ Σmon-cong each ⟩
  Σmon (λ δ → if δ ≡ᵐᵇ γ then cut d ∥ δ ∥ (c δ) else 0ℤ)
    ≡⟨ Σmon-delta γ (λ δ → cut d ∥ δ ∥ (c δ)) ⟩
  cut d ∥ γ ∥ (c γ) ∎
  where
  open ≡-Reasoning

  c : Mon n m → ℤ
  c δ = coeff (residue (P δ))

  f : Mon n m → Term n m
  f δ = δ , residue (P δ)

  each : ∀ δ → cut d ∥ δ ∥ (c δ *ℤ monoᴾ δ γ) ≡
               (if δ ≡ᵐᵇ γ then cut d ∥ δ ∥ (c δ) else 0ℤ)
  each δ = trans
    (cong (λ q → cut d ∥ δ ∥ (c δ *ℤ (if q then 1ℤ else 0ℤ)))
          (trans (⌊≟ᵐ⌋ γ δ) (≡ᵐᵇ-sym γ δ)))
    (guard (∥ δ ∥ ≤ᵇ d) (δ ≡ᵐᵇ γ) (c δ))

-- So it represents P modulo 1 exactly when P has degree at most d
-- modulo 1.

sparse-≈ : ∀ d (P : Poly n m) → Deg≤ d P → P ≈[ pow M ] ⟦ sparse d P ⟧ˢ
sparse-≈ d P deg γ =
  subst (λ z → pow M ∣ (P γ -ℤ z)) (sym (sparse-at d P γ))
        (by-cut (∥ γ ∥ ≤ᵇ d) refl)
  where
  by-cut : ∀ b → (∥ γ ∥ ≤ᵇ d) ≡ b →
           pow M ∣ (P γ -ℤ (if b then coeff (residue (P γ)) else 0ℤ))
  by-cut true  _  = residue-∣ (P γ)
  by-cut false eq = subst (pow M ∣_) (sym (ℤP.+-identityʳ (P γ)))
    (deg γ (ℕ.≰⇒> (λ le → subst T eq (ℕ.≤⇒≤ᵇ le))))

-- Every term has degree at most d, and there are at most
-- (n + m + 1)^d of them.

sparse-small : ∀ d (P : Poly n m) →
               All (λ t → ∥ proj₁ t ∥ ≤ d) (sparse d P)
sparse-small {n} {m} d P =
  AllP.map⁺ {f = λ δ → δ , residue (P δ)} (monomials≤-small n m d)

sparse-length : ∀ d (P : Poly n m) → length (sparse d P) ≤ suc (n + m) ^ d
sparse-length {n} {m} d P = ℕ.≤-trans
  (ℕ.≤-reflexive
    (List.length-map (λ δ → δ , residue (P δ)) (monomials≤ n m d)))
  (length-monomials≤ n m d)

-- Conversely, terms of degree at most d sum to a polynomial with no
-- coefficient above degree d.  So a polynomial has a representation
-- by such terms exactly when it has degree at most d modulo 1.

⟦⟧ˢ-above : ∀ d (ts : List (Term n m)) →
            All (λ t → ∥ proj₁ t ∥ ≤ d) ts →
            ∀ γ → d < ∥ γ ∥ → ⟦ ts ⟧ˢ γ ≡ 0ℤ
⟦⟧ˢ-above d []             []            γ d<γ = refl
⟦⟧ˢ-above d ((δ , c) ∷ ts) (δ≤d ∷ small) γ d<γ =
  cong₂ _+ℤ_ term (⟦⟧ˢ-above d ts small γ d<γ)
  where
  term : coeff c *ℤ monoᴾ δ γ ≡ 0ℤ
  term with γ ≟ᵐ δ
  ... | yes γ≡δ = contradiction (subst (λ z → ∥ z ∥ ≤ d) (sym γ≡δ) δ≤d)
                                (ℕ.<⇒≱ d<γ)
  ... | no  _   = ℤP.*-zeroʳ (coeff c)

small-Deg≤ : ∀ d (P : Poly n m) (ts : List (Term n m)) →
             All (λ t → ∥ proj₁ t ∥ ≤ d) ts → P ≈[ pow M ] ⟦ ts ⟧ˢ →
             Deg≤ d P
small-Deg≤ d P ts small P≈ γ d<γ =
  subst (pow M ∣_) (ℤP.+-identityʳ (P γ))
    (subst (λ z → pow M ∣ (P γ -ℤ z)) (⟦⟧ˢ-above d ts small γ d<γ)
           (P≈ γ))

Deg≤⇔sparse : ∀ d (P : Poly n m) →
              Deg≤ d P ⇔
              (∃ λ ts → All (λ t → ∥ proj₁ t ∥ ≤ d) ts ×
                        P ≈[ pow M ] ⟦ ts ⟧ˢ)
Deg≤⇔sparse d P = mk⇔
  (λ deg → sparse d P , sparse-small d P , sparse-≈ d P deg)
  (λ (ts , small , P≈) → small-Deg≤ d P ts small P≈)


------------------------------------------------------------------------
-- Representations of path-sums

-- A sparse phase and a linear form for each output.

record Rep (n m : ℕ) : Set where
  constructor rep
  field
    terms : List (Term n m)
    forms : Fin n → Lin n m

open Rep public

-- The path-sum a representation stands for, at any normalisation.

psʳ : (k : ℕ) → Rep n m → PathSum n k m
psʳ k R = ⟨ ⟦ terms R ⟧ˢ , (λ w → liftᴸ (forms R w)) ⟩

-- R represents ξ: the phases agree modulo 1, and the outputs are the
-- liftings of the forms.

Represents : PathSum n k m → Rep n m → Set
Represents ξ R =
  (phase ξ ≈[ pow M ] ⟦ terms R ⟧ˢ) ×
  (∀ w γ → out ξ w γ ≡ liftᴸ (forms R w) γ)

-- Every term of R has degree at most d.

Small : ℕ → Rep n m → Set
Small d R = All (λ t → ∥ proj₁ t ∥ ≤ d) (terms R)

-- The size in bits.

termBits : ℕ → ℕ → ℕ
termBits n m = n + m + M

formBits : ℕ → ℕ → ℕ
formBits n m = suc (n + m)

size : Rep n m → ℕ
size {n} {m} R = length (terms R) * termBits n m + n * formBits n m

-- The sparse representation of a path-sum of bounded degree with
-- given forms.

represent : ℕ → PathSum n k m → (Fin n → Lin n m) → Rep n m
represent d ξ f = rep (sparse d (phase ξ)) f

represent-correct : ∀ d (ξ : PathSum n k m) (f : Fin n → Lin n m) →
                    Deg≤ d (phase ξ) →
                    (∀ w γ → out ξ w γ ≡ liftᴸ (f w) γ) →
                    Represents ξ (represent d ξ f)
represent-correct d ξ f deg outs = sparse-≈ d (phase ξ) deg , outs

represent-small : ∀ d (ξ : PathSum n k m) (f : Fin n → Lin n m) →
                  Small d (represent d ξ f)
represent-small d ξ f = sparse-small d (phase ξ)

represent-length : ∀ d (ξ : PathSum n k m) (f : Fin n → Lin n m) →
                   length (terms (represent d ξ f)) ≤ suc (n + m) ^ d
represent-length d ξ f = sparse-length d (phase ξ)

-- Conversely, a representation by terms of degree at most d bounds
-- the degree of the phase.

represents-Deg≤ : ∀ d (ξ : PathSum n k m) (R : Rep n m) → Small d R →
                  Represents ξ R → Deg≤ d (phase ξ)
represents-Deg≤ d ξ R small (P≈ , _) =
  small-Deg≤ d (phase ξ) (terms R) small P≈


------------------------------------------------------------------------
-- The size bound

-- With at most (n + m + 1)^d terms, d ≥ 1 and m ≤ ℓ, the size is at
-- most 2 (n + ℓ + M + 1)^(d+1): the terms take (n + m + 1)^d times
-- n + m + M bits and the forms n times n + m + 1, both at most
-- K^(d+1) with K = n + ℓ + M + 1.

size-bound : ∀ d ℓ (R : Rep n m) → 1 ≤ d → m ≤ ℓ →
             length (terms R) ≤ suc (n + m) ^ d →
             size R ≤ 2 * suc (n + ℓ + M) ^ suc d
size-bound {n} {m} d ℓ R 1≤d m≤ℓ len = ℕ.≤-trans
  (ℕ.+-mono-≤ terms≤ forms≤)
  (ℕ.≤-reflexive (sym twice))
  where
  K : ℕ
  K = suc (n + ℓ + M)

  nm≤ : n + m ≤ n + ℓ + M
  nm≤ = ℕ.≤-trans (ℕ.+-monoʳ-≤ n m≤ℓ) (ℕ.m≤m+n (n + ℓ) M)

  base≤ : suc (n + m) ≤ K
  base≤ = s≤s nm≤

  bits≤ : n + m + M ≤ K
  bits≤ = ℕ.≤-trans (ℕ.+-monoˡ-≤ M (ℕ.+-monoʳ-≤ n m≤ℓ)) (ℕ.n≤1+n _)

  n≤K : n ≤ K
  n≤K = ℕ.≤-trans (ℕ.m≤m+n n m) (ℕ.≤-trans nm≤ (ℕ.n≤1+n _))

  K≤K^d : K ≤ K ^ d
  K≤K^d = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ K)))
                    (ℕ.^-monoʳ-≤ K {{>-nonZero (s≤s z≤n)}} 1≤d)

  terms≤ : length (terms R) * termBits n m ≤ K ^ suc d
  terms≤ = ℕ.≤-trans
    (ℕ.*-mono-≤ (ℕ.≤-trans len (ℕ.^-monoˡ-≤ d base≤)) bits≤)
    (ℕ.≤-reflexive (ℕ.*-comm (K ^ d) K))

  forms≤ : n * formBits n m ≤ K ^ suc d
  forms≤ = ℕ.≤-trans (ℕ.*-mono-≤ n≤K base≤) (ℕ.*-monoʳ-≤ K K≤K^d)

  twice : 2 * K ^ suc d ≡ K ^ suc d + K ^ suc d
  twice = cong (λ z → K ^ suc d + z) (ℕ.+-identityʳ (K ^ suc d))

-- n + ℓ is at most twice the volume n · ℓ, when both are at least 1.

volume-≤ : ∀ n ℓ → 1 ≤ n → 1 ≤ ℓ → n + ℓ ≤ 2 * (n * ℓ)
volume-≤ n ℓ 1≤n 1≤ℓ = ℕ.≤-trans
  (ℕ.+-mono-≤ (ℕ.m≤m*n n ℓ {{>-nonZero 1≤ℓ}})
              (ℕ.m≤n*m ℓ n {{>-nonZero 1≤n}}))
  (ℕ.≤-reflexive (cong (λ z → n * ℓ + z)
                       (sym (ℕ.+-identityʳ (n * ℓ)))))

-- So the size is polynomial in the volume.

size-volume : ∀ d ℓ (R : Rep n m) → 1 ≤ d → m ≤ ℓ → 1 ≤ n → 1 ≤ ℓ →
              length (terms R) ≤ suc (n + m) ^ d →
              size R ≤ 2 * suc (2 * (n * ℓ) + M) ^ suc d
size-volume {n} d ℓ R 1≤d m≤ℓ 1≤n 1≤ℓ len = ℕ.≤-trans
  (size-bound d ℓ R 1≤d m≤ℓ len)
  (ℕ.*-monoʳ-≤ 2 (ℕ.^-monoˡ-≤ (suc d)
    (s≤s (ℕ.+-monoˡ-≤ M (volume-≤ n ℓ 1≤n 1≤ℓ)))))

-- Whatever the phase, the forms alone take n (n + m + 1) bits.

size-forms : (R : Rep n m) → n * formBits n m ≤ size R
size-forms {n} {m} R =
  ℕ.m≤n+m (n * formBits n m) (length (terms R) * termBits n m)
