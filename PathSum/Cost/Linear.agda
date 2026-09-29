------------------------------------------------------------------------
-- Presentations of groups
--
-- Matching a quotient against a lifted linear form, on the sparse
-- representation (for Amy, QPL 2018, figure 2 and lemma 4.3)
--
-- The rules [ω] and [HH] match the quotient Q of the phase by the
-- eliminated path variable against ¼ + ½(c ⊕ ⨁S) and ½(c ⊕ ⨁S).
-- Modulo 1, ½ times the lifting of c ⊕ ⨁S is ½c + ½ Σ_{u ∈ S} u: its
-- terms of degree 2 or more are integers.  So Q matches when it has no
-- term of degree 2 or more, each of its linear coefficients is 0 or ½,
-- and its constant is the rule's (¼ + ½c, or ½c); S is then the set of
-- variables whose coefficient is ½ -- the support of the quotient, as
-- the proof of lemma 4.3 reads it (PathSum.Clifford.supp).
--
-- linearᶜ checks the first two conditions on a sparse quotient and
-- returns its constant and S: every term must have degree at most 1,
-- and every linear coefficient, read off the list with
-- PathSum.Cost.Split.readᶜ, must be 0 or ½.  linear-≈ is its soundness,
-- for any list: if the checks pass and the constant is base + ½c
-- modulo 2^M, the list stands for κ base + ½ · liftXor c S modulo 2^M,
-- coefficient by coefficient -- the premise of [ω] at base ¼ and of
-- [HH] at base 0.  The degree check is termwise, so it is sound for any
-- list and exact for a canonical one, where no term has a coefficient
-- 0 modulo 2^M.  The cost is one pass for the degrees and one per
-- variable for the coefficients: at most 11 (L + 1) B² for L terms and
-- any B ≥ n + m + 2 (cost-linearᶜ), in the cost model of
-- PathSum.Cost: a cost model, not a machine model; nothing is claimed
-- about Turing machines or complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Linear (M : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside; ⊥; ⁅_⁆; ∣_∣)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-trans; ∣-reflexive; *-monoʳ-∣)
open import Data.Integer.Solver using () renaming (module +-*-Solver to ℤS)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _^_; _≤_; _<_; _≤ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)
  renaming (map to mapⱽ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Cost
open import PathSum.Cost.Bound using
  (Bnd; ^-pos; lift-B; lift-LB; _≤[_]_; unbound; ≤-1ᶜ; ≤-*ᶜ; ≤-+ᶜ;
   ≤-0ᶜ; ≤-weakenᶜ; B*B)
open import PathSum.Cost.Coeff M using
  (Coeff; 0ᶠ; coeff-0ᶠ; _==ᶠ_; ==ᶠ-true; eqᶠᶜ; _≡ᴹ_; modᴹ; ∣diff;
   ≡ᴹ-refl; ≡ᴹ-reflexive; ≡ᴹ-sym; ≡ᴹ-trans; coeff-residue)
open import PathSum.Cost.Monomial using (degᵐᶜ; value-degᵐᶜ; cost-degᵐᶜ)
open import PathSum.Cost.Split M using
  (Reading; reading; readᶜ; value-readᶜ; cost-readᶜ; liftXor-at;
   liftXor-by)
open import PathSum.Order M using (pow; pow-suc; pow-∣; pow-+)
open import PathSum.Polynomial using
  (Mon; Var; x[_]; y[_]; ⟪_⟫; 1ᵐ; ∥_∥; _≟ᵐ_; _+ᴾ_; _·ᴾ_; _≈[_]_; κ;
   sgn; negpow; liftXor)
open import PathSum.Polynomial.Properties using
  (_⊆ᵇ_; _⊆ᵐᵇ_; emptyᵇ; emptyᵐ; emptyᵇ-⊥; ⊥⊆ᵇ; ⌊≟ᵐ1ᵐ⌋; ≡1ᵐ⇒emptyᵐ;
   ∥⟪v⟫∥≡1; ∥γ∥≡0⇒γ≡1ᵐ; ∥γ∥≡1⇒γ≡⟪v⟫; liftXor-1ᵐ; liftXor-∣; i∣0; 1∣i;
   emptyᵐ⇒≡1ᵐ; ∥1ᵐ∥≡0)
open import PathSum.Reduction M using (½)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; residue; ⟦⟧ˢ-above)

import Data.Integer.Properties as ℤP
import Data.Nat.Properties as ℕ
import Data.Nat.Solver
import Data.Vec.Properties as Vec

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- The checks

-- ½ as a coefficient, and a coefficient that is 0 or ½.

halfᶠ : Coeff
halfᶠ = residue ½

zeroOrHalf : Coeff → Bool
zeroOrHalf b = (b ==ᶠ 0ᶠ) ∨ (b ==ᶠ halfᶠ)

-- A term of degree at most 1.

lowᶜ : Term n m → Cost Bool
lowᶜ (γ , a) = do
  s ← degᵐᶜ γ
  step (s ≤ᵇ 1)

-- The verdict: whether the checks pass, the constant coefficient, and
-- the variables with coefficient ½.

record Linearity (n m : ℕ) : Set where
  constructor linearity
  field
    linear? : Bool
    const   : Coeff
    support : Mon n m

open Linearity public

linearᶜ : List (Term n m) → Cost (Linearity n m)
linearᶜ q = do
  low ← allᶜ lowᶜ q
  r   ← readᶜ q
  okx ← allVᶜ (λ b → step (zeroOrHalf b)) (proj₁ (proj₂ r))
  oky ← allVᶜ (λ b → step (zeroOrHalf b)) (proj₂ (proj₂ r))
  sx  ← mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) (proj₁ (proj₂ r))
  sy  ← mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) (proj₂ (proj₂ r))
  pure (linearity (low ∧ (okx ∧ oky)) (proj₁ r) (sx , sy))


------------------------------------------------------------------------
-- Facts about liftings and constants at small monomials

private
  ∧-true : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
  ∧-true true true _ = refl , refl

  ∨-false : ∀ a b → a ∨ b ≡ true → b ≡ false → a ≡ true
  ∨-false true  b _  _ = refl
  ∨-false false true  _ ()

  ≤ᵇ-true : ∀ {s d} → (s ≤ᵇ d) ≡ true → s ≤ d
  ≤ᵇ-true {s} {d} eq = ℕ.≤ᵇ⇒≤ s d (subst T (sym eq) tt)

  -- A constant is read only at 1.

  κ-at : ∀ (z : ℤ) (γ : Mon n m) → κ z γ ≡ (if emptyᵐ γ then z else 0ℤ)
  κ-at z γ = cong (λ b → if b then z else 0ℤ) (⌊≟ᵐ1ᵐ⌋ γ)

  emptyᵇ-⁅⁆ : (i : Fin k) → emptyᵇ ⁅ i ⁆ ≡ false
  emptyᵇ-⁅⁆ zero    = refl
  emptyᵇ-⁅⁆ (suc i) = emptyᵇ-⁅⁆ i

  emptyᵐ-var : (v : Var n m) → emptyᵐ ⟪ v ⟫ ≡ false
  emptyᵐ-var {m = m} x[ i ] = cong (_∧ emptyᵇ (⊥ {m})) (emptyᵇ-⁅⁆ i)
  emptyᵐ-var {n = n} y[ j ] = trans (cong (_∧ emptyᵇ ⁅ j ⁆) (emptyᵇ-⊥ {n}))
                                    (emptyᵇ-⁅⁆ j)

  ⁅⁆⊆ᵇ : (i : Fin k) (p : Subset k) → (⁅ i ⁆ ⊆ᵇ p) ≡ lookup p i
  ⁅⁆⊆ᵇ zero    (inside  ∷ p) = ⊥⊆ᵇ p
  ⁅⁆⊆ᵇ zero    (outside ∷ p) = refl
  ⁅⁆⊆ᵇ (suc i) (b       ∷ p) = ⁅⁆⊆ᵇ i p

-- Whether a variable is in a monomial, as its bit.

bitᵛ : Mon n m → Var n m → Bool
bitᵛ (α , β) x[ i ] = lookup α i
bitᵛ (α , β) y[ j ] = lookup β j

-- The lifting at a single variable: ±1 on S, 0 elsewhere.

liftXor-var : (c : Bool) (S : Mon n m) (v : Var n m) →
              liftXor c S ⟪ v ⟫ ≡
              (if bitᵛ S v then sgn c *ℤ negpow 0 else 0ℤ)
liftXor-var c S v = trans (liftXor-by c S ⟪ v ⟫)
  (trans (cong₂ (λ e s → liftXor-at c e (⟪ v ⟫ ⊆ᵐᵇ S) s)
                (emptyᵐ-var v) (∥⟪v⟫∥≡1 v))
         (cong (λ b → liftXor-at c false b 1) (sub S v)))
  where
  sub : (S : Mon _ _) (v : Var _ _) → (⟪ v ⟫ ⊆ᵐᵇ S) ≡ bitᵛ S v
  sub (α , β) x[ i ] = trans (cong₂ _∧_ (⁅⁆⊆ᵇ i α) (⊥⊆ᵇ β))
                             (∧-identityʳ (lookup α i))
  sub (α , β) y[ j ] = trans (cong₂ _∧_ (⊥⊆ᵇ α) (⁅⁆⊆ᵇ j β)) refl

-- ½ and -½ agree modulo 2^M: 2^M divides 2 · 2^(M-1) (or is 1).

half-twice : ∀ e → pow e ∣ (pow (e ∸ 1) +ℤ pow (e ∸ 1))
half-twice zero    = 1∣i
half-twice (suc e) = ∣-reflexive (trans (pow-suc e) (double (pow e)))
  where
  double : ∀ z → z *ℤ (+ 2) ≡ z +ℤ z
  double = ℤS.solve 1 (λ z → z ℤS.:* ℤS.con (+ 2) ℤS.:= z ℤS.:+ z) refl

half-sgn : (c : Bool) → ½ ≡ᴹ ½ *ℤ (sgn c *ℤ negpow 0)
half-sgn false = ≡ᴹ-reflexive (sym (ℤP.*-identityʳ ½))
half-sgn true  = modᴹ (subst (pow M ∣_) (flip ½) (half-twice M))
  where
  flip : ∀ h → h +ℤ h ≡ h -ℤ (h *ℤ -1ℤ)
  flip = ℤS.solve 1 (λ h → h ℤS.:+ h ℤS.:= h ℤS.:- (h ℤS.:* ℤS.con -1ℤ))
                   refl

-- Above degree 1, ½ times a lifting is an integer.

half-big : (c : Bool) (S γ : Mon n m) → 2 ≤ ∥ γ ∥ →
           pow M ∣ (½ *ℤ liftXor c S γ)
half-big c S γ 2≤ = ∣-trans (pow-∣ bound)
  (subst (_∣ (½ *ℤ liftXor c S γ)) (pow-+ (M ∸ 1) (∥ γ ∥ ∸ 1))
         (*-monoʳ-∣ ½ (liftXor-∣ c S γ)))
  where
  ≤∸+ : ∀ a b → a ≤ (a ∸ b) + b
  ≤∸+ zero    b       = z≤n
  ≤∸+ (suc a) zero    = ℕ.≤-reflexive (sym (ℕ.+-identityʳ (suc a)))
  ≤∸+ (suc a) (suc b) = ℕ.≤-trans (s≤s (≤∸+ a b))
                                  (ℕ.≤-reflexive (sym (ℕ.+-suc (a ∸ b) b)))

  bound : M ≤ (M ∸ 1) + (∥ γ ∥ ∸ 1)
  bound = ℕ.≤-trans (≤∸+ M 1) (ℕ.+-monoʳ-≤ (M ∸ 1) (ℕ.∸-monoˡ-≤ 1 2≤))


------------------------------------------------------------------------
-- Soundness

-- A linear coefficient that is 0 or ½, read at a variable whose bit is
-- whether it is ½.

private
  var-case : (b : Coeff) {z : ℤ} → z ≡ᴹ coeff b → zeroOrHalf b ≡ true →
             (c : Bool) →
             z ≡ᴹ (0ℤ +ℤ ½ *ℤ (if b ==ᶠ halfᶠ then sgn c *ℤ negpow 0 else 0ℤ))
  var-case b {z} h ok c = by (b ==ᶠ halfᶠ) refl
    where
    by : ∀ e → (b ==ᶠ halfᶠ) ≡ e →
         z ≡ᴹ (0ℤ +ℤ ½ *ℤ (if e then sgn c *ℤ negpow 0 else 0ℤ))
    by true  eq = ≡ᴹ-trans h (≡ᴹ-trans
      (≡ᴹ-reflexive (cong coeff (==ᶠ-true b halfᶠ eq)))
      (≡ᴹ-trans (coeff-residue ½) (≡ᴹ-trans (half-sgn c)
        (≡ᴹ-reflexive (sym (ℤP.+-identityˡ (½ *ℤ (sgn c *ℤ negpow 0))))))))
    by false eq = ≡ᴹ-trans h (≡ᴹ-reflexive (trans
      (trans (cong coeff (==ᶠ-true b 0ᶠ (∨-false _ _ ok eq))) coeff-0ᶠ)
      (sym (cong (0ℤ +ℤ_) (ℤP.*-zeroʳ ½)))))

-- If the checks pass and the constant is base + ½c modulo 2^M, the list
-- stands for κ base + ½ · liftXor c S.

linear-≈ : (q : List (Term n m)) → linear? (value (linearᶜ q)) ≡ true →
           (base : ℤ) (c : Bool) →
           coeff (const (value (linearᶜ q))) ≡ᴹ base +ℤ ½ *ℤ [ c ]ᶻ →
           ⟦ q ⟧ˢ ≈[ pow M ]
           (κ base +ᴾ (½ ·ᴾ liftXor c (support (value (linearᶜ q)))))
linear-≈ {n} {m} q ok base c hc γ = ∣diff (at γ (∥ γ ∥) refl)
  where
  r   = value (readᶜ q)
  xs  = proj₁ (proj₂ r)
  ys  = proj₂ (proj₂ r)
  low = value (allᶜ lowᶜ q)
  okx = value (allVᶜ (λ b → step (zeroOrHalf b)) xs)
  oky = value (allVᶜ (λ b → step (zeroOrHalf b)) ys)
  S   = support (value (linearᶜ q))

  r≡ : r ≡ reading ⟦ q ⟧ˢ
  r≡ = value-readᶜ q

  low≡ : low ≡ true
  low≡ = proj₁ (∧-true low (okx ∧ oky) ok)

  okx≡ : okx ≡ true
  okx≡ = proj₁ (∧-true okx oky (proj₂ (∧-true low (okx ∧ oky) ok)))

  oky≡ : oky ≡ true
  oky≡ = proj₂ (∧-true okx oky (proj₂ (∧-true low (okx ∧ oky) ok)))

  -- Every term has degree at most 1, so the sum vanishes above.
  small : All (λ t → ∥ proj₁ t ∥ ≤ 1) q
  small = go q (all-true (λ t → value (lowᶜ t)) q
                  (trans (sym (value-allᶜ lowᶜ q)) low≡))
    where
    go : (ts : List (Term n m)) → All (λ t → value (lowᶜ t) ≡ true) ts →
         All (λ t → ∥ proj₁ t ∥ ≤ 1) ts
    go []             []       = []
    go ((γ , a) ∷ ts) (h ∷ hs) =
      ≤ᵇ-true (trans (cong (_≤ᵇ 1) (sym (value-degᵐᶜ γ))) h) ∷ go ts hs

  -- The linear coefficients are read correctly.
  xs-at : ∀ i → lookup xs i ≡ residue (⟦ q ⟧ˢ ⟪ x[ i ] ⟫)
  xs-at i = trans (cong (λ v → lookup (proj₁ (proj₂ v)) i) r≡)
                  (Vec.lookup∘tabulate _ i)

  ys-at : ∀ j → lookup ys j ≡ residue (⟦ q ⟧ˢ ⟪ y[ j ] ⟫)
  ys-at j = trans (cong (λ v → lookup (proj₂ (proj₂ v)) j) r≡)
                  (Vec.lookup∘tabulate _ j)

  -- The bits of S are whether they are ½.
  bit-x : ∀ i → bitᵛ S x[ i ] ≡ (lookup xs i ==ᶠ halfᶠ)
  bit-x i = trans (cong (λ v → lookup v i)
                        (value-mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) xs))
                  (Vec.lookup-map i (λ b → b ==ᶠ halfᶠ) xs)

  bit-y : ∀ j → bitᵛ S y[ j ] ≡ (lookup ys j ==ᶠ halfᶠ)
  bit-y j = trans (cong (λ v → lookup v j)
                        (value-mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) ys))
                  (Vec.lookup-map j (λ b → b ==ᶠ halfᶠ) ys)

  -- At 1: the constant.
  at1 : ⟦ q ⟧ˢ 1ᵐ ≡ᴹ (κ base (1ᵐ {n} {m}) +ℤ ½ *ℤ liftXor c S 1ᵐ)
  at1 = ≡ᴹ-trans (≡ᴹ-sym (coeff-residue (⟦ q ⟧ˢ 1ᵐ)))
    (≡ᴹ-trans (≡ᴹ-reflexive (cong (λ v → coeff (proj₁ v)) (sym r≡)))
      (≡ᴹ-trans hc (≡ᴹ-reflexive (sym (cong₂ _+ℤ_
        (trans (κ-at base (1ᵐ {n} {m}))
               (cong (λ b → if b then base else 0ℤ)
                     (≡1ᵐ⇒emptyᵐ (1ᵐ {n} {m}) refl)))
        (cong (½ *ℤ_) (liftXor-1ᵐ c S)))))))

  -- At a variable: 0 or ½, as its bit says.
  at-var : (v : Var n m) →
           ⟦ q ⟧ˢ ⟪ v ⟫ ≡ᴹ (κ base ⟪ v ⟫ +ℤ ½ *ℤ liftXor c S ⟪ v ⟫)
  at-var v = ≡ᴹ-trans (by-var v) (≡ᴹ-reflexive (sym (cong₂ _+ℤ_
    (trans (κ-at base ⟪ v ⟫) (cong (λ b → if b then base else 0ℤ)
                                   (emptyᵐ-var v)))
    (cong (½ *ℤ_) (liftXor-var c S v)))))
    where
    by-var : (v : Var n m) →
             ⟦ q ⟧ˢ ⟪ v ⟫ ≡ᴹ
             (0ℤ +ℤ ½ *ℤ (if bitᵛ S v then sgn c *ℤ negpow 0 else 0ℤ))
    by-var x[ i ] = subst (λ b → ⟦ q ⟧ˢ ⟪ x[ i ] ⟫ ≡ᴹ
                                 (0ℤ +ℤ ½ *ℤ (if b then sgn c *ℤ negpow 0
                                              else 0ℤ)))
      (sym (bit-x i))
      (var-case (lookup xs i)
        (≡ᴹ-trans (≡ᴹ-sym (coeff-residue (⟦ q ⟧ˢ ⟪ x[ i ] ⟫)))
                  (≡ᴹ-reflexive (cong coeff (sym (xs-at i)))))
        (allVᶜ-true (λ b → step (zeroOrHalf b)) xs okx≡ i) c)
    by-var y[ j ] = subst (λ b → ⟦ q ⟧ˢ ⟪ y[ j ] ⟫ ≡ᴹ
                                 (0ℤ +ℤ ½ *ℤ (if b then sgn c *ℤ negpow 0
                                              else 0ℤ)))
      (sym (bit-y j))
      (var-case (lookup ys j)
        (≡ᴹ-trans (≡ᴹ-sym (coeff-residue (⟦ q ⟧ˢ ⟪ y[ j ] ⟫)))
                  (≡ᴹ-reflexive (cong coeff (sym (ys-at j)))))
        (allVᶜ-true (λ b → step (zeroOrHalf b)) ys oky≡ j) c)

  -- Above degree 1: nothing on either side, modulo 2^M.
  at-big : (γ : Mon n m) → 2 ≤ ∥ γ ∥ →
           ⟦ q ⟧ˢ γ ≡ᴹ (κ base γ +ℤ ½ *ℤ liftXor c S γ)
  at-big γ 2≤ = ≡ᴹ-trans (≡ᴹ-reflexive (⟦⟧ˢ-above 1 q small γ 2≤))
    (≡ᴹ-sym (≡ᴹ-trans
      (≡ᴹ-reflexive (cong (_+ℤ ½ *ℤ liftXor c S γ)
        (trans (κ-at base γ) (cong (λ b → if b then base else 0ℤ) empty≡))))
      (≡ᴹ-trans (≡ᴹ-reflexive (ℤP.+-identityˡ (½ *ℤ liftXor c S γ)))
        (modᴹ (subst (pow M ∣_) (sym (ℤP.+-identityʳ (½ *ℤ liftXor c S γ)))
                     (half-big c S γ 2≤))))))
    where
    empty≡ : emptyᵐ γ ≡ false
    empty≡ = by (emptyᵐ γ) refl
      where
      by : ∀ e → emptyᵐ γ ≡ e → e ≡ false
      by false _  = refl
      by true  eq with subst (λ s → 2 ≤ s) (cong ∥_∥ (emptyᵐ⇒≡1ᵐ γ eq)) 2≤
      ... | le with subst (2 ≤_) (∥1ᵐ∥≡0 {n} {m}) le
      ...   | ()

  at : (γ : Mon n m) (s : ℕ) → ∥ γ ∥ ≡ s →
       ⟦ q ⟧ˢ γ ≡ᴹ (κ base γ +ℤ ½ *ℤ liftXor c S γ)
  at γ zero          eq = subst (λ δ → ⟦ q ⟧ˢ δ ≡ᴹ
                                       (κ base δ +ℤ ½ *ℤ liftXor c S δ))
                                (sym (∥γ∥≡0⇒γ≡1ᵐ γ eq)) at1
  at γ (suc zero)    eq with ∥γ∥≡1⇒γ≡⟪v⟫ γ eq
  ... | v , refl = at-var v
  at γ (suc (suc s)) eq =
    at-big γ (subst (2 ≤_) (sym eq) (s≤s (s≤s z≤n)))


------------------------------------------------------------------------
-- Cost

-- A degree test reads the monomial.

cost-lowᶜ : (t : Term n m) → cost (lowᶜ t) ≤ suc (n + m)
cost-lowᶜ {n} {m} (γ , a) = ℕ.≤-trans
  (ℕ.≤-reflexive (ℕ.+-comm (cost (degᵐᶜ γ)) 1))
  (s≤s (cost-degᵐᶜ γ))

-- One pass for the degrees, the reading, and a step per variable for
-- each of the four checks and maps: at most 11 (L + 1) B² for any
-- B ≥ n + m + 2.

cost-linearᶜ : (q : List (Term n m)) (B : ℕ) → 2 + (n + m) ≤ B →
               cost (linearᶜ q) ≤ 11 * Bnd (length q) B 2
cost-linearᶜ {n} {m} q B le = unbound
  (≤-+ᶜ low≤ (≤-+ᶜ read≤ (≤-+ᶜ (two n n≤B (okᶜ xs)) (≤-+ᶜ (two m m≤B (okᶜ ys))
    (≤-+ᶜ (two n n≤B (bitᶜ xs)) (≤-+ᶜ (two m m≤B (bitᶜ ys)) ≤-0ᶜ))))))
  where
  L = length q
  r = value (readᶜ q)
  xs = proj₁ (proj₂ r)
  ys = proj₂ (proj₂ r)

  1≤B : 1 ≤ B
  1≤B = ℕ.≤-trans (s≤s z≤n) le

  B≤B¹ : B ≤ B ^ 1
  B≤B¹ = ℕ.≤-reflexive (sym (ℕ.*-identityʳ B))

  n≤B : n ≤ B
  n≤B = ℕ.≤-trans (ℕ.m≤m+n n m) (ℕ.≤-trans (ℕ.m≤n+m (n + m) 2) le)

  m≤B : m ≤ B
  m≤B = ℕ.≤-trans (ℕ.m≤n+m m n) (ℕ.≤-trans (ℕ.m≤n+m (n + m) 2) le)

  low≤ : cost (allᶜ lowᶜ q) ≤[ 1 ] Bnd L B 2
  low≤ = ≤-1ᶜ (lift-LB L B 1 2 1≤B (s≤s z≤n)
    (ℕ.≤-trans (cost-allᶜ lowᶜ q cost-lowᶜ)
    (ℕ.*-monoʳ-≤ L (ℕ.≤-trans le B≤B¹))))

  sq : ∀ B L → B * (B + L * B) ≡ B ^ 2 + L * B ^ 2
  sq = NS.solve 2 (λ B L → B NS.:* (B NS.:+ L NS.:* B) NS.:=
                           B NS.:^ 2 NS.:+ L NS.:* B NS.:^ 2) refl
    where
    module NS = Data.Nat.Solver.+-*-Solver

  read≤ : cost (readᶜ q) ≤[ 2 ] Bnd L B 2
  read≤ = ≤-weakenᶜ
    (ℕ.≤-trans (cost-readᶜ q)
      (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.≤-trans (ℕ.n≤1+n _) le)
                   (ℕ.+-mono-≤ (ℕ.≤-trans (ℕ.n≤1+n _) le)
                               (ℕ.*-monoʳ-≤ L le)))
                 (ℕ.≤-reflexive (sq B L))))
    (≤-+ᶜ (≤-1ᶜ (lift-B L B 2 2 1≤B ℕ.≤-refl ℕ.≤-refl))
          (≤-1ᶜ (lift-LB L B 2 2 1≤B ℕ.≤-refl ℕ.≤-refl)))

  okᶜ : ∀ {k} (v : Vec Coeff k) →
        cost (allVᶜ (λ b → step (zeroOrHalf b)) v) ≤ k * 2
  okᶜ v = cost-allVᶜ (λ b → step (zeroOrHalf b)) v (λ _ → ℕ.≤-refl)

  bitᶜ : ∀ {k} (v : Vec Coeff k) →
         cost (mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) v) ≤ k * 2
  bitᶜ v = cost-mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) v (λ _ → ℕ.≤-refl)

  two : ∀ k {a} → k ≤ B → a ≤ k * 2 → a ≤[ 2 ] Bnd L B 2
  two k k≤B a≤ = ≤-weakenᶜ (ℕ.≤-trans a≤ (ℕ.≤-reflexive (ℕ.*-comm k 2)))
    (≤-*ᶜ 2 (lift-B L B 1 2 1≤B (s≤s z≤n) (ℕ.≤-trans k≤B B≤B¹)))
