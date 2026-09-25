------------------------------------------------------------------------
-- Presentations of groups
--
-- All of figure 2 keeps a Clifford path-sum Clifford, and corollary
-- 4.4 for every normal form
--
-- The paper's corollary 4.4 (Amy, QPL 2018) reduces the path-sum of a
-- Clifford circuit with the rules of figure 2 and reads the verdict
-- off what is left: the identity if and only if nothing is left but
-- |x⟩ ↦ |x⟩.  Its proof cites lemma 4.3 -- a path-sum with internal
-- path variables and a phase of order at most 2 that is the identity
-- reduces, again to such a path-sum -- and proposition 3.2.  Read as
-- "iterate the step lemma 4.3 constructs" it is PathSum.Clifford.
-- corollary-4-4 (and, at any variables, PathSum.Anywhere.Clifford).
-- Read as "reduce in any way until no rule applies", which is what
-- proposition 3.2 is about, it needs more than lemma 4.3 states: that
-- *every* step keeps a path-sum Clifford, not only the one its proof
-- picks.  For the linear rules that is lemma 2.13; for [ω] and [HH]
-- with general Boolean-valued quotients and for [Case] the paper does
-- not say, and lemma 2.13 fails for non-linear quotients
-- (PathSum.Polynomial.Substitution).  It is proved here, for all of
-- figure 2 at any variables (_⟶ᶠ_).  The reason is that at a Clifford
-- path-sum the quotients are not arbitrary:
--
-- * [ω] and [HH]: the quotient of an order-2 phase by an internal
--   variable is ¼a + ½(linear form) (PathSum.Clifford.decompose), so a
--   Boolean-valued Q with ½Q congruent to its ½-part has the parities
--   of a linear form, hence is its lifting exactly (lift-unique):
--   lin-≈ and bool-≡.  The general reduct is then, coefficient by
--   coefficient, the linear one, and lemma 2.13 applies.
-- * [Case]: X enters its premise with weight ¼ and every coefficient
--   of q₁₀ but the constant one is a multiple of ½, so X is even off
--   the constant monomial: a Boolean-valued X is the constant 0 or 1.
--   The reduct (1 - X)·R[y₁ ← Q] + X·R′[y₀ ← Q′] is then one of its two
--   branches, whose quotient is again a linear lifting; the product of
--   such a lifting with a quotient of an order-2 phase has order at
--   most 2 (Ord≤-*ᴾ, the argument of lemma 2.13 for a product).
--
-- So every step of _⟶ᶠ_ keeps a path-sum Clifford (⟶ᶠ-Clifford,
-- ⟶ᶠ*-Clifford).  With PathSum.Full.Match this gives corollary 4.4 in
-- its strongest form: take ⟦ C ⟧ᴿ to *any* irreducible path-sum, by
-- any rules of figure 2 in any order; if a path variable is left the
-- circuit is not the identity (irreducible-refutesᶠ), and otherwise it
-- is the identity iff what is left is syntactically |x⟩ ↦ |x⟩
-- (corollary-4-4-normalᶠ).  Hence also a decision procedure that
-- normalises with all of figure 2 (circuit-decidableᶠ; decidability as
-- such is elementary, and the type does not record the route).  The
-- polynomial time bounds are not formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.Clifford (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside; ∣_∣)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣-refl; ∣-trans; ∣⇒∣ᵤ; 0∣⇒≡0; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n;
   ∣m⇒∣m*n; *-monoʳ-∣; *-monoˡ-∣; *-cancelˡ-∣)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseʳ; *-zeroʳ; i-j≡0⇒i≡j)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_; _≤_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (_∷_; there)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using
  (PathSum; phase; out; idPS; Internal; head-part; tail-part;
   tail-Internal)
open import PathSum.Circuit M using (Circuit; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Order M using
  (Ord≤; pow; val; val-bound; pow-∣; pow-+; pow-suc; parity; Ord≤-+;
   Ord≤-∸; Ord≤-κ; Ord≤-liftXor; subst-Ord≤)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; 1ᵐ; ⟪_⟫; _∪ᵐ_; _∈ᵐ_; _∈ᵐ?_; _≟ᵐ_; _∖ᵐ_; ∥_∥;
   0ᴾ; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval; liftXor)
  renaming (subst to substˡ)
open import PathSum.Polynomial.Properties using
  (Σmon-∣; Σmon-cong; ∥∪ᵐ∥≤; eval-≈; eval-+ᴾ; eval-−ᴾ; eval-κ; eval-ext;
   liftXor-∣; liftXor-0; subst-NoVar; i∣0)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ)
open import PathSum.Polynomial.Boolean using
  (BoolValued; BoolValued-κ; BoolValued-liftXor; lift-unique;
   liftXor-split-≈; ≈-from-values)
open import PathSum.Polynomial.Substitution using
  (Absent; substᴾ; q₀₀; q₀₁; q₁₀; drop₁; substHead)
open import PathSum.Reduction M using (¼; ½; tail-Ord≤)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; ωᴳ-reduct; hhᴳ-reduct; case-reduct)
open import PathSum.Reorder using (front; Internal-front)
open import PathSum.Anywhere M using (PSRel; Anywhere; plain; at; Ord≤-front)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_; ⟶⇒⟶ᶠ)
open import PathSum.Full.Canonical M using (½∣pow; coarsen)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)

import PathSum.Denotation
private module Den = PathSum.Denotation M₀

open Den using (_≋_; semantics)

import PathSum.Clifford
private module Cliff = PathSum.Clifford M₀ semantics

import PathSum.Circuit
private module Circ = PathSum.Circuit M

import PathSum.Decide
private module Dcd = PathSum.Decide M₀

import PathSum.Full.Corollary
private module FC = PathSum.Full.Corollary M₀

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    d n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Clifford path-sums

-- Every path variable internal, and a phase of order at most 2: the
-- hypotheses of lemma 4.3.

IsClifford : PathSum n k m → Set
IsClifford ξ = Internal ξ × Ord≤ 2 (phase ξ)


------------------------------------------------------------------------
-- Arithmetic

private
  -- Halving: 2^M = 2·½ and ½ = 2·¼ (M ≥ 3 here).
  half-cancel : ∀ {a} → pow M ∣ (½ * a) → (+ 2) ∣ a
  half-cancel {a} h = *-cancelˡ-∣ ½ {{m^n≢0 2 (M ∸ 1)}}
    (subst (_∣ (½ * a)) (pow-suc (M ∸ 1)) h)

  quarter-cancel : ∀ {a} → ½ ∣ (¼ * a) → (+ 2) ∣ a
  quarter-cancel {a} h = *-cancelˡ-∣ ¼ {{m^n≢0 2 (M ∸ 2)}}
    (subst (_∣ (¼ * a)) (pow-suc (M ∸ 2)) h)

  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  -- The constant polynomial, and a monic one at its own variable.
  κ-1ᵐ : (c : ℤ) → κ {n} {m} c 1ᵐ ≡ c
  κ-1ᵐ {n} {m} c with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  κ-0 : (γ : Mon n m) → κ {n} {m} 0ℤ γ ≡ 0ℤ
  κ-0 γ with γ ≟ᵐ 1ᵐ
  ... | yes _ = refl
  ... | no  _ = refl

  μ-⟪⟫ : (v : Var n m) → μ v ⟪ v ⟫ ≡ 1ℤ
  μ-⟪⟫ v with ⟪ v ⟫ ≟ᵐ ⟪ v ⟫
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  -- Pointwise equality transports the order and the absence of a
  -- variable.
  Ord≤-≗ : {P Q : Poly n m} → (∀ γ → P γ ≡ Q γ) → Ord≤ d P → Ord≤ d Q
  Ord≤-≗ {d = d} h ordP γ = subst (pow (val d ∥ γ ∥) ∣_) (h γ) (ordP γ)

  NoVar-≗ : ∀ {c} {v : Var n m} {P Q : Poly n m} →
            (∀ γ → P γ ≡ Q γ) → NoVar c v P → NoVar c v Q
  NoVar-≗ {c = c} h nv γ v∈γ = subst (c ∣_) (h γ) (nv γ v∈γ)


------------------------------------------------------------------------
-- Values determine coefficients

-- Möbius inversion at 0: equal values, equal coefficients.

same-coefficients : (P Q : Poly n m) →
                    (∀ x y → eval P x y ≡ eval Q x y) → ∀ γ → P γ ≡ Q γ
same-coefficients P Q h γ = i-j≡0⇒i≡j (P γ) (Q γ) (0∣⇒≡0
  (≈-from-values {c = 0ℤ} P Q (λ x y →
     subst (0ℤ ∣_) (sym (trans (cong (_- eval Q x y) (h x y))
                               (+-inverseʳ (eval Q x y)))) i∣0) γ))

-- Two Boolean-valued polynomials with the same parities are equal.

bool-≡ : (R L : Poly n m) → BoolValued R → BoolValued L →
         R ≈[ + 2 ] L → ∀ γ → R γ ≡ L γ
bool-≡ R L bR bL R≈L = lift-unique R L bR bL (eval-≈ R L R≈L)


------------------------------------------------------------------------
-- Linear quotients

-- A quotient of an order-2 phase has a profile: its linear
-- coefficients are multiples of ½, its coefficients of degree at least
-- 2 multiples of 1.  If H ≈ κ base + ½·R for such an H, then R has the
-- parities of a linear form, the one PathSum.Clifford.decompose reads
-- off H.

lin-≈ : (H R : Poly n m) (base : ℤ) →
        (∀ v → pow (M ∸ 1) ∣ H ⟪ v ⟫) →
        (∀ γ → 2 ≤ ∥ γ ∥ → pow M ∣ H γ) →
        H ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ R)) →
        ∃ λ c → R ≈[ + 2 ] liftXor c (Cliff.supp H)
lin-≈ {n} {m} H R base p⟪⟫ p≥2 eq =
  c , λ γ → half-cancel (subst (pow M ∣_)
    (shape (H γ) (κ base γ) (R γ) (liftXor c (Cliff.supp H) γ) ½)
    (∣m∣n⇒∣m-n (eqL γ) (eq γ)))
  where
  hbase : pow (M ∸ 1) ∣ (H 1ᵐ - base)
  hbase = subst (λ z → ½ ∣ (H 1ᵐ - z)) (κ-1ᵐ {n} {m} base)
    (coarsen ½ H (κ base) R ½∣pow ∣-refl eq 1ᵐ)

  dec : ∃ λ c → H ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c (Cliff.supp H)))
  dec = Cliff.decompose H base p⟪⟫ p≥2 hbase

  c : Bool
  c = proj₁ dec

  eqL : H ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c (Cliff.supp H)))
  eqL = proj₂ dec

  -- ½ is a variable to the solver: it is a symbolic constant.
  shape : ∀ h b r l t → (h - (b + t * l)) - (h - (b + t * r)) ≡ t * (r - l)
  shape = solve 5 (λ h b r l t →
    (h :- (b :+ t :* l)) :- (h :- (b :+ t :* r)) := t :* (r :- l)) refl


------------------------------------------------------------------------
-- The order of a product with a linear lifting

-- The argument of lemma 2.13, for L · H with L of the shape of a
-- linear lifting (its coefficient at δ a multiple of 2^(|δ| - 1)) and
-- H a quotient of a polynomial of order d.

Ord≤-*ᴾ : (L H : Poly n m) →
          (∀ δ → pow (∥ δ ∥ ∸ 1) ∣ L δ) →
          (∀ β → pow (val d (suc ∥ β ∥)) ∣ H β) →
          Ord≤ d (L *ᴾ H)
Ord≤-*ᴾ {d = d} L H linL headH γ = Σmon-∣ _ (λ δ → Σmon-∣ _ (each δ))
  where
  each : ∀ δ β →
         pow (val d ∥ γ ∥) ∣ (if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then L δ * H β else 0ℤ)
  each δ β with (δ ∪ᵐ β) ≟ᵐ γ
  ... | no  _  = i∣0
  ... | yes eq = ∣-trans (pow-∣ bound) product
    where
    γ≤ : ∥ γ ∥ ≤ ∥ β ∥ ℕ.+ ∥ δ ∥
    γ≤ = subst (λ z → ∥ z ∥ ≤ ∥ β ∥ ℕ.+ ∥ δ ∥) eq
      (ℕ.≤-trans (∥∪ᵐ∥≤ δ β) (ℕ.≤-reflexive (ℕ.+-comm (∥ δ ∥) (∥ β ∥))))

    bound : val d ∥ γ ∥ ≤ (∥ δ ∥ ∸ 1) ℕ.+ val d (suc ∥ β ∥)
    bound = ℕ.≤-trans (val-bound d (∥ β ∥) (∥ δ ∥) (∥ γ ∥) γ≤)
      (ℕ.≤-reflexive (ℕ.+-comm (val d (suc ∥ β ∥)) (∥ δ ∥ ∸ 1)))

    product : pow ((∥ δ ∥ ∸ 1) ℕ.+ val d (suc ∥ β ∥)) ∣ (L δ * H β)
    product = subst (_∣ (L δ * H β)) (pow-+ (∥ δ ∥ ∸ 1) (val d (suc ∥ β ∥)))
      (∣-trans (*-monoˡ-∣ (pow (val d (suc ∥ β ∥))) (linL δ))
               (*-monoʳ-∣ (L δ) (headH β)))

-- The quotient of a polynomial of order d by its head variable, and
-- the part of a polynomial free of its second variable.

head-ord : {P : Poly n (suc m)} → Ord≤ d P →
           ∀ δ → pow (val d (suc ∥ δ ∥)) ∣ head-part P δ
head-ord {d = d} {P = P} ordP (α , β) =
  subst (λ z → pow (val d z) ∣ P (α , inside ∷ β))
        (ℕ.+-suc (∣ α ∣) (∣ β ∣)) (ordP (α , inside ∷ β))

drop₁-Ord≤ : {P : Poly n (suc (suc m))} → Ord≤ d P → Ord≤ d (drop₁ P)
drop₁-Ord≤ ordP (α , inside  ∷ β) = ordP (α , inside ∷ outside ∷ β)
drop₁-Ord≤ ordP (α , outside ∷ β) = ordP (α , outside ∷ outside ∷ β)


------------------------------------------------------------------------
-- Substitution respects equal quotients

substᴾ-cong : (P : Poly n m) (v : Var n m) (L L′ : Poly n m) →
              (∀ γ → L γ ≡ L′ γ) → ∀ γ → substᴾ P v L γ ≡ substᴾ P v L′ γ
substᴾ-cong P v L L′ h γ =
  cong (λ z → (if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ) + z)
    (Σmon-cong (λ δ → Σmon-cong (λ β →
      cong (λ z → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                  else (if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then P (δ ∪ᵐ ⟪ v ⟫) * z
                        else 0ℤ))
           (h β))))


------------------------------------------------------------------------
-- [ω] keeps a path-sum Clifford

-- Its Boolean-valued quotient is the lifting of a linear form, so the
-- reduct's new term ⅛ - ¼Q has order at most 2.

ω-Clifford : (ξ : PathSum n (suc k) (suc m)) (Q : Poly n m) →
             BoolValued Q →
             head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) →
             IsClifford ξ → IsClifford (ωᴳ-reduct ξ Q)
ω-Clifford ξ Q bQ eq (int , ordP) =
  tail-Internal ξ int ,
  Ord≤-+ (Ord≤-∸ (Ord≤-κ ∣-refl) ord¼Q) (tail-Ord≤ ordP)
  where
  H = head-part (phase ξ)
  S = Cliff.supp H

  lin : ∃ λ c → Q ≈[ + 2 ] liftXor c S
  lin = lin-≈ H Q ¼ (Cliff.prof⟪⟫ ordP) (Cliff.prof≥2 ordP) eq

  L : Poly _ _
  L = liftXor (proj₁ lin) S

  Q≡L : ∀ γ → Q γ ≡ L γ
  Q≡L = bool-≡ Q L bQ (BoolValued-liftXor (proj₁ lin) S) (proj₂ lin)

  ord¼Q : Ord≤ 2 (¼ ·ᴾ Q)
  ord¼Q = Ord≤-≗ {P = ¼ ·ᴾ L} {Q = ¼ ·ᴾ Q} (λ γ → cong (¼ *_) (sym (Q≡L γ)))
                 (Ord≤-liftXor 2 (proj₁ lin) S)


------------------------------------------------------------------------
-- [HH] keeps a path-sum Clifford

-- ½(y_i + Q) is the quotient, so y_i + Q has the parities of a linear
-- form on a set S containing y_i, and Q is the lifting of the form on
-- S ∖ y_i.  The reduct is then, coefficient by coefficient, that of the
-- linear [HH], and lemma 2.13 applies.

hh-Clifford : (ξ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m) →
              BoolValued Q → Absent y[ i ] Q →
              head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)) →
              IsClifford ξ → IsClifford (hhᴳ-reduct ξ i Q)
hh-Clifford {n = n} {m = m} ξ i Q bQ absQ eq (int , ordP) =
  (λ j w → NoVar-≗ {v = y[ j ]} {P = substˡ (tail-part (out ξ w)) y[ i ] c S′}
                   {Q = substᴾ (tail-part (out ξ w)) y[ i ] Q}
                   (same (tail-part (out ξ w)))
     (subst-NoVar (tail-part (out ξ w)) i c S′
        (λ j′ → tail-Internal ξ int j′ w) j)) ,
  Ord≤-≗ (same (tail-part (phase ξ)))
    (subst-Ord≤ (tail-part (phase ξ)) y[ i ] c S′ (tail-Ord≤ ordP))
  where
  H = head-part (phase ξ)
  S = Cliff.supp H

  eq′ : H ≈[ pow M ] (κ 0ℤ +ᴾ (½ ·ᴾ (μ y[ i ] +ᴾ Q)))
  eq′ γ = subst (λ z → pow M ∣ (H γ - z))
    (sym (trans (cong (_+ (½ * (μ y[ i ] γ + Q γ))) (κ-0 γ))
                (+-identityˡ _)))
    (eq γ)

  lin : ∃ λ c → (μ y[ i ] +ᴾ Q) ≈[ + 2 ] liftXor c S
  lin = lin-≈ H (μ y[ i ] +ᴾ Q) 0ℤ (Cliff.prof⟪⟫ ordP) (Cliff.prof≥2 ordP) eq′

  c : Bool
  c = proj₁ lin

  -- y_i is in S: its coefficient in y_i + Q is 1.
  i∈S : y[ i ] ∈ᵐ S
  i∈S = decide (y[ i ] ∈ᵐ? S)
    where
    decide : Dec (y[ i ] ∈ᵐ S) → y[ i ] ∈ᵐ S
    decide (yes p) = p
    decide (no ¬p) = ⊥-elim (2∤1 (subst ((+ 2) ∣_)
      (cong₂ _-_
        (cong₂ _+_ (μ-⟪⟫ {n = n} {m = m} y[ i ])
                   (absQ ⟪ y[ i ] ⟫ (x∈⁅x⁆ i)))
        (liftXor-0 c S ⟪ y[ i ] ⟫ y[ i ] (x∈⁅x⁆ i) ¬p))
      (proj₂ lin ⟪ y[ i ] ⟫)))

  S′ : Mon n m
  S′ = S ∖ᵐ y[ i ]

  shape : ∀ u q l l′ → ((u + q) - l) + (l - (u + l′)) ≡ q - l′
  shape = solve 4 (λ u q l l′ →
    ((u :+ q) :- l) :+ (l :- (u :+ l′)) := q :- l′) refl

  Q≈ : Q ≈[ + 2 ] liftXor c S′
  Q≈ γ = subst ((+ 2) ∣_)
    (shape (μ y[ i ] γ) (Q γ) (liftXor c S γ) (liftXor c S′ γ))
    (∣m∣n⇒∣m+n (proj₂ lin γ) (liftXor-split-≈ c S y[ i ] i∈S γ))

  Q≡ : ∀ γ → Q γ ≡ liftXor c S′ γ
  Q≡ = bool-≡ Q (liftXor c S′) bQ (BoolValued-liftXor c S′) Q≈

  -- The linear substitution is, by definition, substᴾ at the lifting.
  same : (R : Poly n m) → ∀ γ →
         substˡ R y[ i ] c S′ γ ≡ substᴾ R y[ i ] Q γ
  same R = substᴾ-cong R y[ i ] (liftXor c S′) Q (λ γ → sym (Q≡ γ))


------------------------------------------------------------------------
-- [Case] keeps a path-sum Clifford

-- X is even off the constant monomial, so it is the constant 0 or 1,
-- and the reduct is one of its branches: q₀₀ + Q·q₀₁ with Q linear
-- when X = 0, q₀₀ + Q′·q₁₀ with Q′ linear when X = 1.

private
  bitᶻ : ℤ → Bool
  bitᶻ z = if ⌊ (+ 2) ∣? z ⌋ then false else true

  [_]ᵇ : Bool → ℤ
  [ b ]ᵇ = if b then 1ℤ else 0ℤ

  bit-≡ : ∀ z → (+ 2) ∣ (z - [ bitᶻ z ]ᵇ)
  bit-≡ z = go ((+ 2) ∣? z)
    where
    go : (t : Dec ((+ 2) ∣ z)) →
         (+ 2) ∣ (z - [ if ⌊ t ⌋ then false else true ]ᵇ)
    go (yes 2∣z) = subst ((+ 2) ∣_) (sym (+-identityʳ z)) 2∣z
    go (no ¬2∣z) with parity z
    ... | inj₁ (r , z≡) = contradiction (divides r z≡) ¬2∣z
    ... | inj₂ (r , z≡) = divides r (trans (cong (_- 1ℤ) z≡) (drop1 r))
      where
      drop1 : ∀ r → ((r * (+ 2)) + 1ℤ) - 1ℤ ≡ r * (+ 2)
      drop1 = solve 1 (λ r →
        ((r :* con (+ 2)) :+ con 1ℤ) :- con 1ℤ := r :* con (+ 2)) refl

case-Clifford : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
                (X Q Q′ : Poly n m) →
                BoolValued X → BoolValued Q → BoolValued Q′ →
                q₁₀ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
                q₀₁ (phase ξ) ≈[ pow M ]
                  ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) →
                IsClifford ξ → IsClifford (case-reduct ξ X Q Q′)
case-Clifford {n = n} {m = m} ξ X Q Q′ bX bQ bQ′ e₁₀ e₀₁ (int , ordP) =
  outs , branch (bitᶻ (X 1ᵐ)) X≡
  where
  P : Poly n (suc (suc m))
  P = phase ξ

  -- The outputs lose y₀ and y₁ and keep the others internal.
  outs : Internal (case-reduct ξ X Q Q′)
  outs j w (α , β) j∈β =
    int (suc (suc j)) w (α , outside ∷ outside ∷ β) (there (there j∈β))

  -- q₁₀ is the quotient of drop₁ P by its head, q₀₁ that of
  -- tail-part P; both phases have order at most 2.
  ordD : Ord≤ 2 (drop₁ P)
  ordD = drop₁-Ord≤ ordP

  ordT : Ord≤ 2 (tail-part P)
  ordT = tail-Ord≤ ordP

  ½∣q₁₀ : ∀ γ → γ ≢ 1ᵐ → ½ ∣ q₁₀ P γ
  ½∣q₁₀ γ γ≢ = by (Cliff.shape γ)
    where
    by : Cliff.Shape γ → ½ ∣ q₁₀ P γ
    by (Cliff.const γ≡)    = contradiction γ≡ γ≢
    by (Cliff.single v γ≡) =
      subst (λ z → ½ ∣ q₁₀ P z) (sym γ≡) (Cliff.prof⟪⟫ ordD v)
    by (Cliff.big 2≤)      = ∣-trans ½∣pow (Cliff.prof≥2 ordD γ 2≤)

  X-even : ∀ γ → γ ≢ 1ᵐ → (+ 2) ∣ X γ
  X-even γ γ≢ = quarter-cancel (subst (½ ∣_)
    (shape (q₁₀ P γ) (¼ * X γ) (½ * Q γ))
    (∣m∣n⇒∣m-n (∣m∣n⇒∣m-n (½∣q₁₀ γ γ≢) (∣-trans ½∣pow (e₁₀ γ)))
               (∣m⇒∣m*n (Q γ) ∣-refl)))
    where
    shape : ∀ a x q → (a - (a - (x + q))) - q ≡ x
    shape = solve 3 (λ a x q → (a :- (a :- (x :+ q))) :- q := x) refl

  -- So X has the parities of the constant bit of X 1ᵐ, and is it.
  X≈ : X ≈[ + 2 ] κ [ bitᶻ (X 1ᵐ) ]ᵇ
  X≈ γ = go (γ ≟ᵐ 1ᵐ)
    where
    go : (t : Dec (γ ≡ 1ᵐ)) →
         (+ 2) ∣ (X γ - (if ⌊ t ⌋ then [ bitᶻ (X 1ᵐ) ]ᵇ else 0ℤ))
    go (yes refl) = bit-≡ (X 1ᵐ)
    go (no γ≢)    = subst ((+ 2) ∣_) (sym (+-identityʳ (X γ))) (X-even γ γ≢)

  X≡ : ∀ γ → X γ ≡ κ [ bitᶻ (X 1ᵐ) ]ᵇ γ
  X≡ = bool-≡ X (κ [ bitᶻ (X 1ᵐ) ]ᵇ) bX (BoolValued-κ (bitᶻ (X 1ᵐ))) X≈

  -- The two branches.
  A B : Poly n m
  A = substHead (tail-part P) Q
  B = substHead (drop₁ P) Q′

  R₀ : Poly n m
  R₀ = phase (case-reduct ξ X Q Q′)

  eval-R₀ : ∀ x y → eval R₀ x y ≡
            ((1ℤ - eval X x y) * eval A x y) + (eval X x y * eval B x y)
  eval-R₀ x y = trans (eval-+ᴾ ((κ 1ℤ -ᴾ X) *ᴾ A) (X *ᴾ B) x y)
    (cong₂ _+_
      (trans (eval-*ᴾ (κ 1ℤ -ᴾ X) A x y)
        (cong (_* eval A x y)
          (trans (eval-−ᴾ (κ 1ℤ) X x y)
                 (cong (_- eval X x y) (eval-κ 1ℤ x y)))))
      (eval-*ᴾ X B x y))

  branch : (b : Bool) → (∀ γ → X γ ≡ κ [ b ]ᵇ γ) → Ord≤ 2 R₀
  branch false X≡κ = Ord≤-≗ {P = A} {Q = R₀}
    (λ γ → sym (same-coefficients R₀ A vals γ)) ordA
    where
    eval-X : ∀ x y → eval X x y ≡ 0ℤ
    eval-X x y = trans (eval-ext X (κ 0ℤ) X≡κ x y) (eval-κ 0ℤ x y)

    pick : ∀ a b → ((1ℤ - 0ℤ) * a) + (0ℤ * b) ≡ a
    pick = solve 2 (λ a b →
      ((con 1ℤ :- con 0ℤ) :* a) :+ (con 0ℤ :* b) := a) refl

    vals : ∀ x y → eval R₀ x y ≡ eval A x y
    vals x y = trans (eval-R₀ x y)
      (trans (cong (λ z → ((1ℤ - z) * eval A x y) + (z * eval B x y))
                   (eval-X x y))
             (pick (eval A x y) (eval B x y)))

    -- Q is linear: q₁₀ ≈ ½Q.
    e₁₀′ : q₁₀ P ≈[ pow M ] (κ 0ℤ +ᴾ (½ ·ᴾ Q))
    e₁₀′ γ = subst (λ z → pow M ∣ (q₁₀ P γ - (z + ½ * Q γ)))
      (trans (cong (¼ *_) (trans (X≡κ γ) (κ-0 γ)))
             (trans (*-zeroʳ ¼) (sym (κ-0 γ))))
      (e₁₀ γ)

    lin : ∃ λ c → Q ≈[ + 2 ] liftXor c (Cliff.supp (q₁₀ P))
    lin = lin-≈ (q₁₀ P) Q 0ℤ (Cliff.prof⟪⟫ ordD) (Cliff.prof≥2 ordD) e₁₀′

    L : Poly n m
    L = liftXor (proj₁ lin) (Cliff.supp (q₁₀ P))

    Q≡L : ∀ γ → Q γ ≡ L γ
    Q≡L = bool-≡ Q L bQ
      (BoolValued-liftXor (proj₁ lin) (Cliff.supp (q₁₀ P))) (proj₂ lin)

    ordA : Ord≤ 2 A
    ordA = Ord≤-+ {P = tail-part (tail-part P)}
                  {Q = Q *ᴾ head-part (tail-part P)}
      (tail-Ord≤ ordT)
      (Ord≤-*ᴾ Q (head-part (tail-part P))
        (λ δ → subst (pow (∥ δ ∥ ∸ 1) ∣_) (sym (Q≡L δ))
                     (liftXor-∣ (proj₁ lin) (Cliff.supp (q₁₀ P)) δ))
        (head-ord ordT))

  branch true X≡κ = Ord≤-≗ {P = B} {Q = R₀}
    (λ γ → sym (same-coefficients R₀ B vals γ)) ordB
    where
    eval-X : ∀ x y → eval X x y ≡ 1ℤ
    eval-X x y = trans (eval-ext X (κ 1ℤ) X≡κ x y) (eval-κ 1ℤ x y)

    pick : ∀ a b → ((1ℤ - 1ℤ) * a) + (1ℤ * b) ≡ b
    pick = solve 2 (λ a b →
      ((con 1ℤ :- con 1ℤ) :* a) :+ (con 1ℤ :* b) := b) refl

    vals : ∀ x y → eval R₀ x y ≡ eval B x y
    vals x y = trans (eval-R₀ x y)
      (trans (cong (λ z → ((1ℤ - z) * eval A x y) + (z * eval B x y))
                   (eval-X x y))
             (pick (eval A x y) (eval B x y)))

    -- Q′ is linear: q₀₁ ≈ ½Q′.
    e₀₁′ : q₀₁ P ≈[ pow M ] (κ 0ℤ +ᴾ (½ ·ᴾ Q′))
    e₀₁′ γ = subst (λ z → pow M ∣ (q₀₁ P γ - (z + ½ * Q′ γ)))
      (trans (cong (λ u → ¼ * (κ 1ℤ γ - u)) (X≡κ γ))
        (trans (cong (¼ *_) (+-inverseʳ (κ 1ℤ γ)))
          (trans (*-zeroʳ ¼) (sym (κ-0 γ)))))
      (e₀₁ γ)

    lin : ∃ λ c → Q′ ≈[ + 2 ] liftXor c (Cliff.supp (q₀₁ P))
    lin = lin-≈ (q₀₁ P) Q′ 0ℤ (Cliff.prof⟪⟫ ordT) (Cliff.prof≥2 ordT) e₀₁′

    L : Poly n m
    L = liftXor (proj₁ lin) (Cliff.supp (q₀₁ P))

    Q′≡L : ∀ γ → Q′ γ ≡ L γ
    Q′≡L = bool-≡ Q′ L bQ′
      (BoolValued-liftXor (proj₁ lin) (Cliff.supp (q₀₁ P))) (proj₂ lin)

    ordB : Ord≤ 2 B
    ordB = Ord≤-+ {P = tail-part (drop₁ P)}
                  {Q = Q′ *ᴾ head-part (drop₁ P)}
      (tail-Ord≤ ordD)
      (Ord≤-*ᴾ Q′ (head-part (drop₁ P))
        (λ δ → subst (pow (∥ δ ∥ ∸ 1) ∣_) (sym (Q′≡L δ))
                     (liftXor-∣ (proj₁ lin) (Cliff.supp (q₀₁ P)) δ))
        (head-ord ordD))


------------------------------------------------------------------------
-- Every step keeps a path-sum Clifford

⟶ᴳ-Clifford : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
              ξ ⟶ᴳ ζ → IsClifford ξ → IsClifford ζ
⟶ᴳ-Clifford (elimᴳ ξ _ _) (int , ordP) = tail-Internal ξ int , tail-Ord≤ ordP
⟶ᴳ-Clifford (ωᴳ ξ Q bQ eq _)             = ω-Clifford ξ Q bQ eq
⟶ᴳ-Clifford (hhᴳ ξ i Q bQ absQ eq _)     = hh-Clifford ξ i Q bQ absQ eq
⟶ᴳ-Clifford (caseᴳ ξ X Q Q′ bX bQ bQ′ _ e₁₀ e₀₁ _ _) =
  case-Clifford ξ X Q Q′ bX bQ bQ′ e₁₀ e₀₁

-- Renumbering keeps internality and the order.

front-Clifford : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) →
                 IsClifford ξ → IsClifford (front j ξ)
front-Clifford j ξ (int , ordP) = Internal-front j ξ int , Ord≤-front j ordP

Anywhere-Clifford : {R : PSRel} →
  (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
   R ξ ζ → IsClifford ξ → IsClifford ζ) →
  ∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
  Anywhere R ξ ζ → IsClifford ξ → IsClifford ζ
Anywhere-Clifford keep (plain r)           cξ = keep r cξ
Anywhere-Clifford keep {ξ = ξ} (at j r) cξ = keep r (front-Clifford j ξ cξ)

⟶ᶠ-Clifford : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
              ξ ⟶ᶠ ζ → IsClifford ξ → IsClifford ζ
⟶ᶠ-Clifford = Anywhere-Clifford {R = Anywhere _⟶ᴳ_}
  (Anywhere-Clifford {R = _⟶ᴳ_} ⟶ᴳ-Clifford)

⟶ᶠ*-Clifford : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
               ξ ⟶ᶠ* ζ → IsClifford ξ → IsClifford ζ
⟶ᶠ*-Clifford εᶠ        cξ = cξ
⟶ᶠ*-Clifford (s ◅ᶠ ss) cξ = ⟶ᶠ*-Clifford ss (⟶ᶠ-Clifford s cξ)


------------------------------------------------------------------------
-- Lemma 4.3 at an irreducible path-sum

-- A Clifford path-sum with a path variable to which no rule of
-- figure 2 applies is not the identity: lemma 4.3's progress gives a
-- linear step, which would be one of _⟶ᶠ_, or a refutation.

stuck-not-id : (ξ : PathSum n k (suc m)) → IsClifford ξ →
               Irreducibleᶠ ξ → ¬ (ξ ≋ idPS)
stuck-not-id ξ (int , ordP) irr = go (Cliff.progress ξ int ordP)
  where
  go : Cliff.Progress ξ → ¬ (ξ ≋ idPS)
  go (Cliff.reduces _ step _ _) = λ _ → irr (⟶⇒⟶ᶠ step)
  go (Cliff.not-id ¬id)         = ¬id


------------------------------------------------------------------------
-- Corollary 4.4 for every normal form

-- ⟦ C ⟧ᴿ is Clifford (PathSum.Circuit), and so is everything it
-- reduces to.

circuit-Clifford : (C : Circuit n) → IsClifford ⟦ C ⟧ᴿ
circuit-Clifford C = Circ.⟦⟧ᴿ-Internal C , Circ.⟦⟧ᴿ-Ord≤ C

-- An irreducible end with a path variable left refutes the circuit.

irreducible-refutesᶠ : (C : Circuit n) {ξ′ : PathSum n k′ (suc m′)} →
                       ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
                       ¬ (⟦ C ⟧ ≋ idPS)
irreducible-refutesᶠ C {ξ′} steps irr =
  FC.circuit-not-idᶠ C {ξ′ = ξ′} steps
    (stuck-not-id ξ′ (⟶ᶠ*-Clifford steps (circuit-Clifford C)) irr)

-- Reduce ⟦ C ⟧ᴿ with any rules of figure 2, at any variables, in any
-- order, until none applies: the circuit is the identity iff no path
-- variable is left and what is left is syntactically |x⟩ ↦ |x⟩.

corollary-4-4-normalᶠ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (m′ ≡ 0 × k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-normalᶠ {m′ = zero} C {ξ′} steps irr = mk⇔
  (λ eq → refl , Equivalence.to (FC.corollary-4-4-anyᶠ C {ξ′ = ξ′} steps) eq)
  (λ (_ , s) → Equivalence.from (FC.corollary-4-4-anyᶠ C {ξ′ = ξ′} steps) s)
corollary-4-4-normalᶠ {m′ = suc _} C {ξ′} steps irr = mk⇔
  (λ eq → ⊥-elim (irreducible-refutesᶠ C {ξ′ = ξ′} steps irr eq))
  (λ { (() , _) })

-- Hence a decision procedure: normalise with all of figure 2, then
-- refute, or test the path-sum without path variables that is left.

circuit-decidableᶠ : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidableᶠ {n} C = settle (normal-formᶠ ⟦ C ⟧ᴿ)
  where
  at-end : ∀ {k′ m′} (ξ′ : PathSum n k′ m′) → ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ →
           Irreducibleᶠ ξ′ → Dec (⟦ C ⟧ ≋ idPS)
  at-end {m′ = zero}  ξ′ steps irr =
    map′ (Equivalence.from (FC.reduct≋ᶠ C {ξ′ = ξ′} steps))
         (Equivalence.to (FC.reduct≋ᶠ C {ξ′ = ξ′} steps))
         (Dcd.decide-≋-id ξ′)
  at-end {m′ = suc _} ξ′ steps irr =
    no (irreducible-refutesᶠ C {ξ′ = ξ′} steps irr)

  settle : (∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
              (⟦ C ⟧ᴿ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) →
           Dec (⟦ C ⟧ ≋ idPS)
  settle (_ , _ , ξ′ , steps , irr) = at-end ξ′ steps irr
