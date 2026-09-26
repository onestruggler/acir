------------------------------------------------------------------------
-- Presentations of groups
--
-- Operations on sparse phases, and the lifting of a linear form
-- truncated at degree d (for Amy, QPL 2018, lemma 2.13 and
-- corollary 2.15)
--
-- The steps of the sparse interpreter of PathSum.Size.Interpreter
-- (whose header has the plan), each proved to track the dense
-- polynomial it stands for, modulo 2^M and coefficient by coefficient:
--
--  * concatenation of term lists is the sum of their polynomials
--    (⟦++⟧ˢ, ≈-++);
--  * wkᵀ reads a term with one more path variable at the head, and
--    tracks PathSum.Circuit.wkPoly (wk-≈); y₀ᵀ multiplies a term by
--    that fresh variable, and tracks PathSum.Linear.mul-y₀ (y₀-≈);
--  * a single term (δ , c mod 2^M) tracks c · x^δ (term-≈);
--  * the residue of an integer modulo 2^M is the one coefficient in
--    [0, 2^M) congruent to it (residue-unique), so congruent
--    polynomials have the same sparse listing (sparse-cong);
--  * liftTerms a d l is the lifting of the linear form l = c ⊕ ⨁S
--    scaled by a, written out term by term and truncated at degree d.
--    Its terms are indexed by the submonomials S′ of S of degree at
--    most d (PathSum.Size.Submonomials.subᵐ≤), and the coefficient of
--    S′ is a (1 - 2c) (-2)^(|S′|-1), or a c for S′ = ∅ (lcoeff) --
--    the expansion  ⨁_{j ∈ S} x_j = Σ_{∅ ≠ S′ ⊆ S} (-2)^(|S′|-1)
--    Π_{j ∈ S′} x_j  of the proof of lemma 2.13, with 1 ⊕ P = 1 - P.
--    It tracks a · liftᴸ l whenever the terms left out vanish modulo
--    1, i.e. whenever a · liftᴸ l has degree at most d modulo 1
--    (liftTerms-≈).  For R_k that is 2^(M-k) · liftᴸ l at d = k
--    (Deg≤-R; R_k† negates it, Deg≤-R†), and for the Hadamard's
--    ½ · liftᴸ l at d = 1 -- both lemma 2.13's order bound read as a
--    degree bound (PathSum.Order.Ord≤-liftXor,
--    PathSum.CRK.Circuit.Ord≤⇒Deg≤): a term of degree j has
--    coefficient divisible by 2^(M-k) 2^(j-1), an integer once j > k.
--    There are exactly Σ_{i ≤ d} C(|S|, i) terms
--    (liftTerms-length), at most (n + m + 1)^d (liftTerms-length≤),
--    each of degree at most d (liftTerms-small).
--
-- The coefficient is computed from |S′| and c alone: none of the
-- operations the interpreter performs evaluates a dense polynomial;
-- the dense ones appear only in the statements that they track them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Size.Terms (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; T)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; ∣_∣)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣m⇒∣-m; ∣m⇒∣m*n; ∣⇒∣ᵤ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat.Base using
  (zero; suc; _+_; _∸_; _^_; _≤_; _<_; _≤ᵇ_; s≤s)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import PathSum.Circuit M using (wkPoly)
open import PathSum.CRK.Circuit M using (Deg≤; Ord≤⇒Deg≤)
open import PathSum.Linear using (Lin; liftᴸ; mul-y₀)
open import PathSum.Order M using (pow; Ord≤-liftXor)
open import PathSum.Polynomial using
  (Mon; Poly; 1ᵐ; ∥_∥; _≟ᵐ_; _⊆ᵐ?_; _+ᴾ_; _·ᴾ_; _≈[_]_; sgn; negpow;
   liftXor; Σmon)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Properties using
  (i∣0; _⊆ᵐᵇ_; ⌊⊆ᵐ?⌋; ⌊≟ᵐ⌋; _≡ᵐᵇ_; ≡ᵐᵇ⇒≡; ≡ᵐᵇ-sym; 1ᵐ⊆ᵐᵇ; Σmon-cong;
   Σmon-delta)
open import PathSum.Reduction M using (½)
open import PathSum.Size.Monomials using
  (Σˡ; Σˡ-map; cut; binomials; monomials≤)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; ⟦⟧ˢ-at; residue; residue-∣; sparse)
open import PathSum.Size.Submonomials using
  (subᵐ≤; Σˡ-subᵐ≤; subᵐ≤-small; length-subᵐ≤-binomial; length-subᵐ≤)

import Data.Fin.Properties as Fin
import Data.Fin.Subset.Properties as Subset
import Data.Nat.Divisibility as ℕDiv
import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Combinatorics as Comb
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Concatenation

⟦++⟧ˢ : (us ts : List (Term n m)) (γ : Mon n m) →
        ⟦ us ++ ts ⟧ˢ γ ≡ ⟦ us ⟧ˢ γ +ℤ ⟦ ts ⟧ˢ γ
⟦++⟧ˢ []             ts γ = sym (ℤP.+-identityˡ (⟦ ts ⟧ˢ γ))
⟦++⟧ˢ ((δ , c) ∷ us) ts γ = trans
  (cong (λ z → (coeff c *ℤ monoᴾ δ γ) +ℤ z) (⟦++⟧ˢ us ts γ))
  (sym (ℤP.+-assoc (coeff c *ℤ monoᴾ δ γ) (⟦ us ⟧ˢ γ) (⟦ ts ⟧ˢ γ)))

-- Tracking P and Q by ts and us, us ++ ts tracks P + Q.

≈-++ : {P Q : Poly n m} (ts us : List (Term n m)) →
       P ≈[ pow M ] ⟦ ts ⟧ˢ → Q ≈[ pow M ] ⟦ us ⟧ˢ →
       (P +ᴾ Q) ≈[ pow M ] ⟦ us ++ ts ⟧ˢ
≈-++ {P = P} {Q} ts us hP hQ γ =
  subst (pow M ∣_) eq (∣m∣n⇒∣m+n (hP γ) (hQ γ))
  where
  shuffle : ∀ p q t u → (p -ℤ t) +ℤ (q -ℤ u) ≡ (p +ℤ q) -ℤ (u +ℤ t)
  shuffle = solve 4 (λ p q t u → (p :- t) :+ (q :- u) := (p :+ q) :- (u :+ t))
                    refl

  eq : (P γ -ℤ ⟦ ts ⟧ˢ γ) +ℤ (Q γ -ℤ ⟦ us ⟧ˢ γ) ≡
       (P γ +ℤ Q γ) -ℤ ⟦ us ++ ts ⟧ˢ γ
  eq = trans (shuffle (P γ) (Q γ) (⟦ ts ⟧ˢ γ) (⟦ us ⟧ˢ γ))
             (cong ((P γ +ℤ Q γ) -ℤ_) (sym (⟦++⟧ˢ us ts γ)))

-- Tracking is up to pointwise equality of the tracked polynomial.

≈-≗ : {P P′ : Poly n m} (ts : List (Term n m)) → (∀ γ → P γ ≡ P′ γ) →
      P′ ≈[ pow M ] ⟦ ts ⟧ˢ → P ≈[ pow M ] ⟦ ts ⟧ˢ
≈-≗ ts eq h γ = subst (λ z → pow M ∣ (z -ℤ ⟦ ts ⟧ˢ γ)) (sym (eq γ)) (h γ)


------------------------------------------------------------------------
-- A fresh path variable

-- A term read with one more path variable at the head, and a term
-- multiplied by that variable.

wkᵀ : Term n m → Term n (suc m)
wkᵀ ((α , β) , c) = (α , outside ∷ β) , c

y₀ᵀ : Term n m → Term n (suc m)
y₀ᵀ ((α , β) , c) = (α , inside ∷ β) , c

-- A monic monomial at a monomial differing in the head path variable.

private
  mono-≗ : (α α′ : Subset n) (β β′ : Subset m) (s : Bool) →
           monoᴾ (α′ , s ∷ β′) (α , s ∷ β) ≡ monoᴾ (α′ , β′) (α , β)
  mono-≗ α α′ β β′ true  = cong (λ b → if b then 1ℤ else 0ℤ)
    (trans (⌊≟ᵐ⌋ (α , inside ∷ β) (α′ , inside ∷ β′))
           (sym (⌊≟ᵐ⌋ (α , β) (α′ , β′))))
  mono-≗ α α′ β β′ false = cong (λ b → if b then 1ℤ else 0ℤ)
    (trans (⌊≟ᵐ⌋ (α , outside ∷ β) (α′ , outside ∷ β′))
           (sym (⌊≟ᵐ⌋ (α , β) (α′ , β′))))

  mono-oi : (α α′ : Subset n) (β β′ : Subset m) →
            monoᴾ (α′ , outside ∷ β′) (α , inside ∷ β) ≡ 0ℤ
  mono-oi α α′ β β′ = cong (λ b → if b then 1ℤ else 0ℤ)
    (trans (⌊≟ᵐ⌋ (α , inside ∷ β) (α′ , outside ∷ β′)) (∧-zeroʳ _))

  mono-io : (α α′ : Subset n) (β β′ : Subset m) →
            monoᴾ (α′ , inside ∷ β′) (α , outside ∷ β) ≡ 0ℤ
  mono-io α α′ β β′ = cong (λ b → if b then 1ℤ else 0ℤ)
    (trans (⌊≟ᵐ⌋ (α , outside ∷ β) (α′ , inside ∷ β′)) (∧-zeroʳ _))

-- The coefficients of the weakened and of the multiplied list.

⟦wk⟧ˢ-outside : (ts : List (Term n m)) (α : Subset n) (β : Subset m) →
                ⟦ map wkᵀ ts ⟧ˢ (α , outside ∷ β) ≡ ⟦ ts ⟧ˢ (α , β)
⟦wk⟧ˢ-outside []                     α β = refl
⟦wk⟧ˢ-outside (((α′ , β′) , c) ∷ ts) α β = cong₂ _+ℤ_
  (cong (coeff c *ℤ_) (mono-≗ α α′ β β′ outside))
  (⟦wk⟧ˢ-outside ts α β)

⟦wk⟧ˢ-inside : (ts : List (Term n m)) (α : Subset n) (β : Subset m) →
               ⟦ map wkᵀ ts ⟧ˢ (α , inside ∷ β) ≡ 0ℤ
⟦wk⟧ˢ-inside []                     α β = refl
⟦wk⟧ˢ-inside (((α′ , β′) , c) ∷ ts) α β = cong₂ _+ℤ_
  (trans (cong (coeff c *ℤ_) (mono-oi α α′ β β′)) (ℤP.*-zeroʳ (coeff c)))
  (⟦wk⟧ˢ-inside ts α β)

⟦y₀⟧ˢ-inside : (ts : List (Term n m)) (α : Subset n) (β : Subset m) →
               ⟦ map y₀ᵀ ts ⟧ˢ (α , inside ∷ β) ≡ ⟦ ts ⟧ˢ (α , β)
⟦y₀⟧ˢ-inside []                     α β = refl
⟦y₀⟧ˢ-inside (((α′ , β′) , c) ∷ ts) α β = cong₂ _+ℤ_
  (cong (coeff c *ℤ_) (mono-≗ α α′ β β′ inside))
  (⟦y₀⟧ˢ-inside ts α β)

⟦y₀⟧ˢ-outside : (ts : List (Term n m)) (α : Subset n) (β : Subset m) →
                ⟦ map y₀ᵀ ts ⟧ˢ (α , outside ∷ β) ≡ 0ℤ
⟦y₀⟧ˢ-outside []                     α β = refl
⟦y₀⟧ˢ-outside (((α′ , β′) , c) ∷ ts) α β = cong₂ _+ℤ_
  (trans (cong (coeff c *ℤ_) (mono-io α α′ β β′)) (ℤP.*-zeroʳ (coeff c)))
  (⟦y₀⟧ˢ-outside ts α β)

-- So they track wkPoly and mul-y₀.

wk-≈ : {P : Poly n m} (ts : List (Term n m)) → P ≈[ pow M ] ⟦ ts ⟧ˢ →
       wkPoly P ≈[ pow M ] ⟦ map wkᵀ ts ⟧ˢ
wk-≈         ts h (α , inside  ∷ β) =
  subst (λ z → pow M ∣ (0ℤ -ℤ z)) (sym (⟦wk⟧ˢ-inside ts α β)) i∣0
wk-≈ {P = P} ts h (α , outside ∷ β) =
  subst (λ z → pow M ∣ (P (α , β) -ℤ z)) (sym (⟦wk⟧ˢ-outside ts α β))
        (h (α , β))

y₀-≈ : {Q : Poly n m} (us : List (Term n m)) → Q ≈[ pow M ] ⟦ us ⟧ˢ →
       mul-y₀ Q ≈[ pow M ] ⟦ map y₀ᵀ us ⟧ˢ
y₀-≈ {Q = Q} us h (α , inside  ∷ β) =
  subst (λ z → pow M ∣ (Q (α , β) -ℤ z)) (sym (⟦y₀⟧ˢ-inside us α β))
        (h (α , β))
y₀-≈         us h (α , outside ∷ β) =
  subst (λ z → pow M ∣ (0ℤ -ℤ z)) (sym (⟦y₀⟧ˢ-outside us α β)) i∣0


------------------------------------------------------------------------
-- Residues

-- The residue of z is the one coefficient c ∈ [0, 2^M) with
-- 2^M ∣ z - c: two such differ by a multiple of 2^M smaller than 2^M.

residue-unique : ∀ z (r : Fin (2 ^ M)) → pow M ∣ (z -ℤ coeff r) →
                 residue z ≡ r
residue-unique z r h = sym (Fin.toℕ-injective (ℤP.+-injective
  (ℤP.i-j≡0⇒i≡j (+ b) (+ a)
    (ℤP.∣i∣≡0⇒i≡0 (zero-of ∣ + b -ℤ + a ∣ bound (∣⇒∣ᵤ diff))))))
  where
  a b : ℕ
  a = toℕ (residue z)
  b = toℕ r

  cancel : ∀ z a b → (z -ℤ a) -ℤ (z -ℤ b) ≡ b -ℤ a
  cancel = solve 3 (λ z a b → (z :- a) :- (z :- b) := b :- a) refl

  diff : pow M ∣ (+ b -ℤ + a)
  diff = subst (pow M ∣_) (cancel z (+ a) (+ b))
               (∣m∣n⇒∣m-n (residue-∣ z) h)

  bound : ∣ + b -ℤ + a ∣ < 2 ^ M
  bound = ℕ.≤-<-trans
    (ℕ.≤-trans (ℕ.≤-reflexive (cong ∣_∣ (ℤP.[+m]-[+n]≡m⊖n b a)))
               (ℤP.∣m⊝n∣≤m⊔n b a))
    (ℕ.⊔-lub (Fin.toℕ<n r) (Fin.toℕ<n (residue z)))

  zero-of : ∀ v → v < 2 ^ M → (2 ^ M) ℕDiv.∣ v → v ≡ 0
  zero-of zero    _  _  = refl
  zero-of (suc v) lt dv = contradiction (ℕDiv.∣⇒≤ dv) (ℕ.<⇒≱ lt)

-- So congruent integers have the same residue, and a polynomial's
-- sparse listing depends only on it modulo 2^M.

residue-cong : ∀ a b → pow M ∣ (a -ℤ b) → residue a ≡ residue b
residue-cong a b h = residue-unique a (residue b)
  (subst (pow M ∣_) (telescope a b (coeff (residue b)))
         (∣m∣n⇒∣m+n h (residue-∣ b)))
  where
  telescope : ∀ a b r → (a -ℤ b) +ℤ (b -ℤ r) ≡ a -ℤ r
  telescope = solve 3 (λ a b r → (a :- b) :+ (b :- r) := a :- r) refl

sparse-cong : ∀ d {P Q : Poly n m} → P ≈[ pow M ] Q →
              sparse d P ≡ sparse d Q
sparse-cong {n} {m} d {P} {Q} h = List.map-cong
  (λ δ → cong (δ ,_) (residue-cong (P δ) (Q δ) (h δ)))
  (monomials≤ n m d)


------------------------------------------------------------------------
-- A single term

term-≈ : (c : ℤ) (δ : Mon n m) →
         (c ·ᴾ monoᴾ δ) ≈[ pow M ] ⟦ (δ , residue c) ∷ [] ⟧ˢ
term-≈ c δ γ =
  subst (pow M ∣_) (eq c (coeff (residue c)) (monoᴾ δ γ))
        (∣m⇒∣m*n (monoᴾ δ γ) (residue-∣ c))
  where
  distrib : ∀ a r x → (a -ℤ r) *ℤ x ≡ (a *ℤ x) -ℤ (r *ℤ x)
  distrib = solve 3 (λ a r x → (a :- r) :* x := (a :* x) :- (r :* x)) refl

  eq : ∀ a r x → (a -ℤ r) *ℤ x ≡ (a *ℤ x) -ℤ ((r *ℤ x) +ℤ 0ℤ)
  eq a r x = trans (distrib a r x)
    (cong (λ z → (a *ℤ x) -ℤ z) (sym (ℤP.+-identityʳ (r *ℤ x))))


------------------------------------------------------------------------
-- The lifting of a linear form, truncated

-- The coefficient of the lifting of c ⊕ ⨁S at a submonomial S′ of S:
-- c if S′ is empty, and (1 - 2c) (-2)^(|S′|-1) otherwise.

lcoeff : Bool → Mon n m → ℤ
lcoeff c γ = if ⌊ γ ≟ᵐ 1ᵐ ⌋ then (if c then 1ℤ else 0ℤ)
             else sgn c *ℤ negpow (∥ γ ∥ ∸ 1)

-- It is liftXor's on the submonomials of S; liftXor vanishes on the
-- others.

liftXor-⊆ : (c : Bool) (S γ : Mon n m) → γ ⊆ᵐᵇ S ≡ true →
            liftXor c S γ ≡ lcoeff c γ
liftXor-⊆ c S γ eq = cong
  (λ b → if ⌊ γ ≟ᵐ 1ᵐ ⌋ then (if c then 1ℤ else 0ℤ)
         else if b then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ)
  (trans (⌊⊆ᵐ?⌋ γ S) eq)

liftXor-⊄ : (c : Bool) (S γ : Mon n m) → γ ⊆ᵐᵇ S ≡ false →
            liftXor c S γ ≡ 0ℤ
liftXor-⊄ c S γ eq = by-1ᵐ ⌊ γ ≟ᵐ 1ᵐ ⌋ refl
  where
  by-1ᵐ : ∀ b → ⌊ γ ≟ᵐ 1ᵐ ⌋ ≡ b →
          (if b then (if c then 1ℤ else 0ℤ)
           else if ⌊ γ ⊆ᵐ? S ⌋ then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ)
          ≡ 0ℤ
  by-1ᵐ true  e = ⊥-elim (true≢false (trans (sym (1ᵐ⊆ᵐᵇ S))
    (trans (cong (_⊆ᵐᵇ S)
                 (sym (≡ᵐᵇ⇒≡ γ 1ᵐ (trans (sym (⌊≟ᵐ⌋ γ 1ᵐ)) e))))
           eq)))
    where
    true≢false : true ≡ false → ⊥
    true≢false ()
  by-1ᵐ false e = cong (λ b → if b then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ)
                       (trans (⌊⊆ᵐ?⌋ γ S) eq)

-- The terms a · (lifting), on the submonomials of degree at most d.

lterm : ℤ → Bool → Mon n m → Fin (2 ^ M)
lterm a c δ = residue (a *ℤ lcoeff c δ)

liftTerms : ℤ → ℕ → Lin n m → List (Term n m)
liftTerms a d (c , (α , β)) = map (λ δ → δ , lterm a c δ) (subᵐ≤ α β d)

-- Its coefficient at γ: lterm a c γ on the submonomials of S of
-- degree at most d, and 0 elsewhere.

private
  guard : ∀ (s b q : Bool) (z : ℤ) →
          (if s then (if b then z *ℤ (if q then 1ℤ else 0ℤ) else 0ℤ)
           else 0ℤ) ≡
          (if q then (if s then (if b then z else 0ℤ) else 0ℤ) else 0ℤ)
  guard true  true  true  z = ℤP.*-identityʳ z
  guard true  true  false z = ℤP.*-zeroʳ z
  guard true  false true  z = refl
  guard true  false false z = refl
  guard false b     true  z = refl
  guard false b     false z = refl

liftTerms-at : ∀ a d (c : Bool) (α : Subset n) (β : Subset m)
               (γ : Mon n m) →
               ⟦ liftTerms a d (c , (α , β)) ⟧ˢ γ ≡
               (if γ ⊆ᵐᵇ (α , β) then cut d ∥ γ ∥ (coeff (lterm a c γ))
                else 0ℤ)
liftTerms-at {n} {m} a d c α β γ = begin
  ⟦ map f (subᵐ≤ α β d) ⟧ˢ γ
    ≡⟨ ⟦⟧ˢ-at (map f (subᵐ≤ α β d)) γ ⟩
  Σˡ (map f (subᵐ≤ α β d))
     (λ t → coeff (proj₂ t) *ℤ monoᴾ (proj₁ t) γ)
    ≡⟨ Σˡ-map f (subᵐ≤ α β d)
         (λ t → coeff (proj₂ t) *ℤ monoᴾ (proj₁ t) γ) ⟩
  Σˡ (subᵐ≤ α β d) (λ δ → r δ *ℤ monoᴾ δ γ)
    ≡⟨ Σˡ-subᵐ≤ α β d (λ δ → r δ *ℤ monoᴾ δ γ) ⟩
  Σmon (λ δ → if δ ⊆ᵐᵇ (α , β) then cut d ∥ δ ∥ (r δ *ℤ monoᴾ δ γ)
              else 0ℤ)
    ≡⟨ Σmon-cong each ⟩
  Σmon (λ δ → if δ ≡ᵐᵇ γ then h δ else 0ℤ)
    ≡⟨ Σmon-delta γ h ⟩
  h γ ∎
  where
  open ≡-Reasoning

  r : Mon n m → ℤ
  r δ = coeff (lterm a c δ)

  f : Mon n m → Term n m
  f δ = δ , lterm a c δ

  h : Mon n m → ℤ
  h δ = if δ ⊆ᵐᵇ (α , β) then cut d ∥ δ ∥ (r δ) else 0ℤ

  each : ∀ δ → (if δ ⊆ᵐᵇ (α , β) then cut d ∥ δ ∥ (r δ *ℤ monoᴾ δ γ)
                else 0ℤ) ≡
               (if δ ≡ᵐᵇ γ then h δ else 0ℤ)
  each δ = trans
    (cong (λ q → if δ ⊆ᵐᵇ (α , β)
                 then cut d ∥ δ ∥ (r δ *ℤ (if q then 1ℤ else 0ℤ)) else 0ℤ)
          (trans (⌊≟ᵐ⌋ γ δ) (≡ᵐᵇ-sym γ δ)))
    (guard (δ ⊆ᵐᵇ (α , β)) (∥ δ ∥ ≤ᵇ d) (δ ≡ᵐᵇ γ) (r δ))

-- So it tracks a · liftᴸ l, provided that the terms above degree d
-- vanish modulo 1.

liftTerms-≈ : ∀ a d (l : Lin n m) → Deg≤ d (a ·ᴾ liftᴸ l) →
              (a ·ᴾ liftᴸ l) ≈[ pow M ] ⟦ liftTerms a d l ⟧ˢ
liftTerms-≈ a d (c , (α , β)) deg γ =
  subst (λ z → pow M ∣ ((a *ℤ liftXor c (α , β) γ) -ℤ z))
        (sym (liftTerms-at a d c α β γ))
        (cases (γ ⊆ᵐᵇ (α , β)) refl (∥ γ ∥ ≤ᵇ d) refl)
  where
  cases : ∀ s → γ ⊆ᵐᵇ (α , β) ≡ s → ∀ b → (∥ γ ∥ ≤ᵇ d) ≡ b →
          pow M ∣ ((a *ℤ liftXor c (α , β) γ) -ℤ
                   (if s then (if b then coeff (lterm a c γ) else 0ℤ)
                    else 0ℤ))
  cases true  e₁ true  _  =
    subst (λ z → pow M ∣ ((a *ℤ z) -ℤ coeff (lterm a c γ)))
          (sym (liftXor-⊆ c (α , β) γ e₁)) (residue-∣ (a *ℤ lcoeff c γ))
  cases true  _  false e₂ =
    subst (pow M ∣_) (sym (ℤP.+-identityʳ (a *ℤ liftXor c (α , β) γ)))
          (deg γ (ℕ.≰⇒> (λ le → subst T e₂ (ℕ.≤⇒≤ᵇ le))))
  cases false e₁ _     _  =
    subst (λ z → pow M ∣ ((a *ℤ z) -ℤ 0ℤ))
          (sym (liftXor-⊄ c (α , β) γ e₁))
          (subst (λ z → pow M ∣ (z -ℤ 0ℤ)) (sym (ℤP.*-zeroʳ a)) i∣0)

-- The terms left out do vanish, by lemma 2.13's order bound: for R_k
-- at d = k, for R_k† likewise, and for the Hadamard's ½ at d = 1.

Deg≤-R : ∀ k (l : Lin n m) → Deg≤ k (pow (M ∸ k) ·ᴾ liftᴸ l)
Deg≤-R k (c , S) = Ord≤⇒Deg≤ (Ord≤-liftXor k c S)

Deg≤-R† : ∀ k (l : Lin n m) → Deg≤ k ((- pow (M ∸ k)) ·ᴾ liftᴸ l)
Deg≤-R† k l γ k<γ =
  subst (pow M ∣_) (ℤP.neg-distribˡ-* (pow (M ∸ k)) (liftᴸ l γ))
        (∣m⇒∣-m (Deg≤-R k l γ k<γ))

Deg≤-H : (l : Lin n m) → Deg≤ 1 (½ ·ᴾ liftᴸ l)
Deg≤-H = Deg≤-R 1


------------------------------------------------------------------------
-- The number of terms

-- The weight of a form: the number of variables it adds up.

weight : Lin n m → ℕ
weight (c , S) = ∥ S ∥

weight≤ : (l : Lin n m) → weight l ≤ n + m
weight≤ (c , (α , β)) = ℕ.+-mono-≤ (Subset.∣p∣≤n α) (Subset.∣p∣≤n β)

-- Exactly Σ_{i ≤ d} C(|S|, i) terms, so at most (n + m + 1)^d.

liftTerms-length : ∀ a d (l : Lin n m) →
                   length (liftTerms a d l) ≡ binomials (weight l) d
liftTerms-length a d (c , (α , β)) = trans
  (List.length-map (λ δ → δ , lterm a c δ) (subᵐ≤ α β d))
  (length-subᵐ≤-binomial α β d)

liftTerms-length≤ : ∀ a d (l : Lin n m) →
                    length (liftTerms a d l) ≤ suc (n + m) ^ d
liftTerms-length≤ a d (c , (α , β)) = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (λ δ → δ , lterm a c δ) (subᵐ≤ α β d)))
  (ℕ.≤-trans (length-subᵐ≤ α β d)
             (ℕ.^-monoˡ-≤ d (s≤s (weight≤ (c , (α , β))))))

-- At degree 1, one term for the constant and one per variable.

binomials-1 : ∀ s → binomials s 1 ≡ suc s
binomials-1 s = cong suc (Comb.nC1≡n s)

-- Each of degree at most d.

liftTerms-small : ∀ a d (l : Lin n m) →
                  All (λ t → ∥ proj₁ t ∥ ≤ d) (liftTerms a d l)
liftTerms-small a d (c , (α , β)) =
  AllP.map⁺ {f = λ δ → δ , lterm a c δ} (subᵐ≤-small α β d)
