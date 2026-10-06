------------------------------------------------------------------------
-- Presentations of groups
--
-- A ladder of Toffoli gadgets whose every normal form is exponentially
-- large (Amy, QPL 2018, section 3.2 and proposition 3.2): the family
--
-- Section 3.2 of the paper: "It is a trivial fact that our calculus
-- is terminating, as every rule reduces the number of path variables.
-- Moreover, each rewrite rule can be matched against in polynomial
-- time, hence every path-sum reduces to a normal form in polynomial
-- time."  Proposition 3.2: "Every sequence of rewrites terminates with
-- an irreducible path-sum.  The sequence is linear in the number of
-- path variables m and for an n-qubit path-sum takes time polynomial
-- in n and m."
--
-- What was known.  PathSum.Full proves termination and the linear
-- length.  PathSum.Cost proves the time bound in a cost model for the
-- linear rules ([Elim], and [ω] and [HH] with Z₂-linear quotients) at
-- a fixed order, and PathSum.Cost.Irreducible for all of figure 2 at
-- order 2; PathSum.Cost.Excluded shows that one [HH] with a non-linear
-- Boolean-valued quotient raises the order from 3 to 4.  The question
-- this development settles is the rest: all of figure 2 -- [HH] and
-- [ω] with Boolean-valued quotients, and [Case] -- beyond order 2.
--
-- The answer: the claim is false there, for figure 2 as stated and
-- for path-sums represented as in definition 2.1 (polynomials written
-- as sums of monomials), reading time as at least the size of the
-- output.  For every n there is a path-sum ξ n on 2n qubits with 2n
-- path variables, 4n phase terms, order at most 3 (exactly 3 for
-- n ≥ 2, which is not formalised; ξ 1 has order 2) and single-variable
-- outputs, such that *every* normal form of figure 2 reachable from
-- it -- whatever rules are applied, in whatever order, at whatever
-- variables (PathSum.Full's _⟶ᶠ_) -- has no path variables and an
-- output polynomial with an odd coefficient on each of the 2^n
-- monomials over the x inputs, so that every list of monomials
-- representing it, read modulo 2, has at least 2^n entries.  A normal
-- form exists (PathSum.Full.Match.normal-formᶠ), and every chain to
-- one has at most 2n steps (PathSum.Full.⟶ᶠ*-bounded); so "every
-- sequence terminates" and "the sequence is linear in m" are true, and
-- "takes time polynomial in n and m" is false for any procedure that
-- writes its normal form down as a list of monomials, as definition
-- 2.1 has it: the output alone is exponentially long.  The quantifier
-- is universal -- every reachable normal form -- so this refutes the
-- existence of a polynomial-time strategy, not merely of a polynomial
-- bound for every strategy.  The paper's inference fails because a
-- step can multiply the size: substituting a non-linear quotient into
-- a polynomial multiplies out products, and each step being cheap in
-- the size of its input bounds nothing when the inputs grow
-- geometrically.  Not refuted: the claim for ⟦ C ⟧ of Clifford+T
-- circuits, and representations with sharing or with complemented
-- literals, in which these normal forms have polynomial size
-- (PathSum.Ladder.Size says more).
--
-- The family.  Gadget g (0 ≤ g < n) has an input wire x_g, a target
-- wire a_g and two path variables u_g and v_g, and its phase is
-- example 3.3's Toffoli with a negated control,
--
--    ½ u_g (v_g + a_g + V_(g-1) (1 + x_g)),     V_(-1) = 1, V_h = v_h,
--
-- the target's output being v_g: four terms ½u_g v_g, ½u_g a_g,
-- ½u_g V_(g-1), ½u_g V_(g-1) x_g, of degree at most 3.  The outputs of
-- the x wires are the x's.  This is the path-sum the paper's
-- composition gives to the ladder of Toffoli gates
-- a_g ⊕= ¬x_g ∧ a_(g-1) (a_(-1) = 1), written with example 3.3's
-- Toffoli path-sum, and its operator is |x, a⟩ ↦ |x, V⟩ with
-- V_g = a_g ⊕ (¬x_g ∧ V_(g-1)) -- at n = 1, |x, a⟩ ↦ |x, a ⊕ ¬x⟩.  The
-- operator is not a stated theorem: what is stated is that every
-- reachable normal form has phase 0 and outputs x and V
-- (PathSum.Ladder.Size.normal-form-phase, normal-form-outputs), from
-- which it follows by soundness (PathSum.Full.Sound).  At a = 0 the
-- last target's value is the NOR of the x's, whose algebraic normal
-- form Π_g (1 ⊕ x_g) has all 2^n monomials over the x's.
--
-- The argument (the plan of this development).
--
--  1. PathSum.Ladder.Gadget: the Boolean bookkeeping.  Each gadget is
--     live (both variables present), half (after [HH] at u_g: v_g has
--     been substituted by c_g = a_g ⊕ (¬x_g ∧ V_(g-1)) and is left as a
--     variable nothing mentions) or dead (after [Elim] at v_g); the
--     phase bit, the value each gadget hands on and its output are
--     Boolean functions of the states and the point (Bsum, Vs).
--  2. This module: ξ n, its sparse representation (PathSum.Size.
--     Sparse's Rep, 4n terms; ξ-represents, ξ-terms), and its values:
--     the phase is ½·Bsum modulo 1 and the outputs are x and v
--     (eval-ξ-phase, odd-ξ-out).  Its order, at most 3, is
--     PathSum.Ladder.Size.ξ-order.
--  3. PathSum.Ladder.Invariant: an invariant of path-sums, Inv, stated
--     through values only -- a layout giving each path variable its
--     gadget and kind (u or v) and each gadget its state; the
--     normalisation is the sum of the states' weights; the phase is
--     ½·Bsum modulo 1 and the outputs the gadgets' values, at every
--     point.  ξ n satisfies it, and renumbering the path variables
--     (PathSum.Reorder.front) keeps it.
--  4. PathSum.Ladder.Steps: every step of figure 2 keeps it.  The
--     phase only takes the values 0 and ½ modulo 1, so [ω] and [Case],
--     which need a ¼, never apply.  [Elim] applies only at the left-
--     over v_g of a half gadget (a live u_g has a non-zero quotient, a
--     live v_g is an output), and makes it dead.  [HH] applies only at a
--     live u_g (the v's of live gadgets are outputs, those of half ones
--     have quotient 0), its substituted variable is forced to be v_g --
--     any other choice is refuted at a point with x_g = 1, where the
--     quotient is v_g ⊕ a_g -- and its quotient is c_g as a function;
--     the gadget becomes half.  Hence every chain keeps the invariant.
--  5. PathSum.Ladder.Progress: a path-sum satisfying the invariant with
--     a path variable left is reducible: [HH] at a live u_g with the
--     lift of c_g as quotient (a PathSum.Polynomial.Boolean.BExp), or
--     [Elim] at a half v_g.
--  6. PathSum.Ladder.Size: so a reachable normal form has no path
--     variables, every gadget is dead, and the last output is V_(n-1),
--     the NOR at a = 0; by Möbius inversion modulo 2 every polynomial
--     with those values -- the normal form's own, or any list of
--     monomials -- has an odd coefficient on every monomial over the
--     x's.  The theorems, and the erratum, are stated there.
--
-- The precision is M = 3 + M₀, as in PathSum.Full.Clifford; only
-- M ≥ 2 is used (a ¼ that is not a multiple of ½).  Nothing here is
-- about running time on a machine: the conclusion about time is the
-- size of what is written down, as in PathSum.Hardness.Blowup.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ladder (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Fin.Base using
  (Fin; zero; suc; inject₁; splitAt; _↑ˡ_; _↑ʳ_; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n)
open import Data.Integer.Properties using (+-inverseʳ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  M : ℕ
  M = ℕ.suc (ℕ.suc (ℕ.suc M₀))

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Ladder.Gadget using
  (State; live; Gad; gad; term; prevAt; Bsum; step; prevAt-live)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ; valᴸ; valᴸ-var; eval-liftᴸ)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using
  (Mon; x[_]; y[_]; ⟪_⟫; 1ᵐ; _∪ᵐ_; satᵐ; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Parity using (odd-[])
open import PathSum.Polynomial.Properties using
  (satᵐ-∪; satᵐ-⟪⟫; satᵐ-1ᵐ; i∣0)
open import PathSum.Reduction M using (½)
open import PathSum.Size.Monomials using (Σˡ; Σˡ-++)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; eval-⟦⟧ˢ; Rep; rep; terms; forms; Represents)

open import Data.Nat.Base using (zero; suc)

private
  variable
    n : ℕ
    A : Set


------------------------------------------------------------------------
-- Congruence modulo 2^M, and halves

-- A record, so that the two sides stay visible to unification.

infix 4 _≡ᴹ_

record _≡ᴹ_ (a b : ℤ) : Set where
  constructor mk≡ᴹ
  field
    ≡ᴹ⇒∣ : pow M ∣ (a - b)

open _≡ᴹ_ public

≡ᴹ-refl : ∀ {a} → a ≡ᴹ a
≡ᴹ-refl {a} = mk≡ᴹ (subst (pow M ∣_) (sym (+-inverseʳ a)) i∣0)

≡⇒≡ᴹ : ∀ {a b} → a ≡ b → a ≡ᴹ b
≡⇒≡ᴹ refl = ≡ᴹ-refl

≡ᴹ-trans : ∀ {a b c} → a ≡ᴹ b → b ≡ᴹ c → a ≡ᴹ c
≡ᴹ-trans {a} {b} {c} (mk≡ᴹ p) (mk≡ᴹ q) =
  mk≡ᴹ (subst (pow M ∣_) (split a b c) (∣m∣n⇒∣m+n p q))
  where
  split : ∀ a b c → (a - b) + (b - c) ≡ a - c
  split = solve 3 (λ a b c → (a :- b) :+ (b :- c) := a :- c) refl

≡ᴹ-sym : ∀ {a b} → a ≡ᴹ b → b ≡ᴹ a
≡ᴹ-sym {a} {b} (mk≡ᴹ (divides q eq)) = mk≡ᴹ (divides (- q)
  (trans (flip a b) (trans (cong -_ eq) (neg q (pow M)))))
  where
  flip : ∀ a b → b - a ≡ - (a - b)
  flip = solve 2 (λ a b → b :- a := :- (a :- b)) refl

  neg : ∀ q p → - (q * p) ≡ (- q) * p
  neg = solve 2 (λ q p → :- (q :* p) := (:- q) :* p) refl

≡ᴹ-+ : ∀ {a b c d} → a ≡ᴹ b → c ≡ᴹ d → (a + c) ≡ᴹ (b + d)
≡ᴹ-+ {a} {b} {c} {d} (mk≡ᴹ p) (mk≡ᴹ q) =
  mk≡ᴹ (subst (pow M ∣_) (split a b c d) (∣m∣n⇒∣m+n p q))
  where
  split : ∀ a b c d → (a - b) + (c - d) ≡ (a + c) - (b + d)
  split = solve 4 (λ a b c d →
    (a :- b) :+ (c :- d) := (a :+ c) :- (b :+ d)) refl

-- ½ times a bit.

hb : Bool → ℤ
hb b = if b then ½ else 0ℤ

-- 2^M is twice ½.

½+½ : ½ + ½ ≡ pow M
½+½ = trans (twice ½) (sym (pow-suc (ℕ.suc (ℕ.suc M₀))))
  where
  twice : ∀ h → h + h ≡ h * (+ 2)
  twice = solve 1 (λ h → h :+ h := h :* con (+ 2)) refl

-- Halves of bits add up to the half of their exclusive or, modulo 1.

hb-xor : ∀ a b → (hb a + hb b) ≡ᴹ hb (a xor b)
hb-xor false false = ≡ᴹ-refl
hb-xor false true  = ≡ᴹ-refl
hb-xor true  false = ≡⇒≡ᴹ (+-identityʳ ½)
hb-xor true  true  = mk≡ᴹ (divides (+ 1) (trans (minus0 (½ + ½))
  (trans ½+½ (sym (one (pow M))))))
  where
  minus0 : ∀ a → a - 0ℤ ≡ a
  minus0 = solve 1 (λ a → a :- con 0ℤ := a) refl

  one : ∀ p → (+ 1) * p ≡ p
  one = solve 1 (λ p → con (+ 1) :* p := p) refl


------------------------------------------------------------------------
-- Wires and path variables

-- Input g of the first block, x_g, and of the second, a_g; the path
-- variables u_g and v_g are numbered the same way.

xw aw : Fin n → Fin (n ℕ.+ n)
xw {n} g = g ↑ˡ n
aw {n} g = n ↑ʳ g


------------------------------------------------------------------------
-- The path-sum

-- The numerator of ½.

½ᵗ : Fin (2 ℕ.^ M)
½ᵗ = fromℕ< (ℕ.^-monoʳ-< 2 (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) (ℕ.n<1+n (ℕ.suc (ℕ.suc M₀))))

coeff-½ : coeff ½ᵗ ≡ ½
coeff-½ = cong +_ (toℕ-fromℕ< _)

-- The monomial V_(g-1): 1 for gadget 0, v_(g-1) after.

prevMon : Fin n → Mon (n ℕ.+ n) (n ℕ.+ n)
prevMon {suc n} zero    = 1ᵐ
prevMon {suc n} (suc h) = ⟪ y[ aw {suc n} (inject₁ h) ] ⟫

-- Gadget g's four terms: ½u_g v_g, ½u_g a_g, ½u_g V_(g-1),
-- ½u_g V_(g-1) x_g.

gadgetTerms : Fin n → List (Term (n ℕ.+ n) (n ℕ.+ n))
gadgetTerms g =
  (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ y[ aw g ] ⟫ , ½ᵗ) ∷
  (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ x[ aw g ] ⟫ , ½ᵗ) ∷
  (⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g , ½ᵗ) ∷
  ((⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) ∪ᵐ ⟪ x[ xw g ] ⟫ , ½ᵗ) ∷
  []

-- All gadgets' terms, in order.

concatF : (Fin n → List A) → List A
concatF {zero}  f = []
concatF {suc n} f = f zero ++ concatF (λ g → f (suc g))

phaseTerms : (n : ℕ) → List (Term (n ℕ.+ n) (n ℕ.+ n))
phaseTerms n = concatF {n} gadgetTerms

-- The outputs: x_g on wire x_g, v_g on wire a_g.

outForm : (n : ℕ) → Fin (n ℕ.+ n) → Lin (n ℕ.+ n) (n ℕ.+ n)
outForm n w =
  [ (λ g → varᴸ x[ xw {n} g ]) , (λ g → varᴸ y[ aw {n} g ]) ]′ (splitAt n w)

-- The family: 2n qubits, normalisation 1/√2^(2n), 2n path variables.

ξ : (n : ℕ) → PathSum (n ℕ.+ n) (n ℕ.+ n) (n ℕ.+ n)
ξ n = ⟨ ⟦ phaseTerms n ⟧ˢ , (λ w → liftᴸ (outForm n w)) ⟩


------------------------------------------------------------------------
-- Its size

-- PathSum.Size.Sparse's representation, with 4n terms: the size the
-- cost model of PathSum.Cost works with.

ξ-rep : (n : ℕ) → Rep (n ℕ.+ n) (n ℕ.+ n)
ξ-rep n = rep (phaseTerms n) (outForm n)

ξ-represents : (n : ℕ) → Represents (ξ n) (ξ-rep n)
ξ-represents n =
  (λ γ → ≡ᴹ⇒∣ (≡ᴹ-refl {⟦ phaseTerms n ⟧ˢ γ})) , (λ w γ → refl)

private
  length-concatF : (f : Fin n → List A) → (∀ g → length (f g) ≡ 4) →
                   length (concatF f) ≡ 4 ℕ.* n
  length-concatF {zero}  f h = refl
  length-concatF {suc n} f h = trans
    (length-++ (f zero))
    (trans (cong₂ ℕ._+_ (h zero) (length-concatF (λ g → f (suc g))
                                                 (λ g → h (suc g))))
           (sym (ℕ.*-suc 4 n)))

ξ-terms : (n : ℕ) → length (terms (ξ-rep n)) ≡ 4 ℕ.* n
ξ-terms n = length-concatF {n} gadgetTerms (λ g → refl)


------------------------------------------------------------------------
-- Its values

-- Every gadget live, with the values of the point.

G₀ : (x y : Fin (n ℕ.+ n) → Bool) → Fin n → Gad
G₀ x y g = gad live (x (xw g)) (x (aw g)) (y (xw g)) (y (aw g))

private
  -- Sums over gadgets.

  ΣF : (Fin n → ℤ) → ℤ
  ΣF {zero}  f = 0ℤ
  ΣF {suc n} f = f zero + ΣF (λ g → f (suc g))

  Σˡ-concatF : (f : Fin n → List A) (h : A → ℤ) →
               Σˡ (concatF f) h ≡ ΣF (λ g → Σˡ (f g) h)
  Σˡ-concatF {zero}  f h = refl
  Σˡ-concatF {suc n} f h = trans (Σˡ-++ (f zero) (concatF (λ g → f (suc g))) h)
    (cong (λ z → Σˡ (f zero) h + z) (Σˡ-concatF (λ g → f (suc g)) h))

  -- The halves of the gadgets' contributions add up to the half of the
  -- phase bit.

  ΣF-Bsum : ∀ p (G : Fin n → Gad) →
            ΣF (λ g → hb (term (G g) (prevAt p G g))) ≡ᴹ hb (Bsum p G)
  ΣF-Bsum {zero}  p G = ≡ᴹ-refl
  ΣF-Bsum {suc n} p G = ≡ᴹ-trans
    (≡ᴹ-+ {a = hb (term (G zero) p)} ≡ᴹ-refl
          (ΣF-Bsum (step (G zero) p) (λ g → G (suc g))))
    (hb-xor (term (G zero) p) (Bsum (step (G zero) p) (λ g → G (suc g))))

  -- u ∧ (v ⊕ a ⊕ (¬x ∧ p)) term by term.

  not-and : ∀ x p → not x ∧ p ≡ p xor (p ∧ x)
  not-and true  true  = refl
  not-and true  false = refl
  not-and false true  = refl
  not-and false false = refl

  bool4 : ∀ u v a x p →
          u ∧ (v xor (a xor (not x ∧ p))) ≡
          (u ∧ v) xor ((u ∧ a) xor ((u ∧ p) xor ((u ∧ p) ∧ x)))
  bool4 false v a x p = refl
  bool4 true  v a x p = cong (λ z → v xor (a xor z)) (not-and x p)

  -- The value of one term ½·x^δ.

  term-val : (δ : Mon (n ℕ.+ n) (n ℕ.+ n)) (x y : Fin (n ℕ.+ n) → Bool) →
             (if satᵐ δ x y then coeff ½ᵗ else 0ℤ) ≡ hb (satᵐ δ x y)
  term-val δ x y = cong (λ c → if satᵐ δ x y then c else 0ℤ) coeff-½

  -- The monomial V_(g-1) is satisfied exactly when the value reaching
  -- gadget g is 1.

  sat-prev : (g : Fin n) (x y : Fin (n ℕ.+ n) → Bool) →
             satᵐ (prevMon g) x y ≡ prevAt true (G₀ x y) g
  sat-prev {suc n} zero    x y = satᵐ-1ᵐ x y
  sat-prev {suc n} (suc h) x y = trans (satᵐ-⟪⟫ y[ aw {suc n} (inject₁ h) ] x y)
    (sym (prevAt-live (G₀ x y) (λ _ → refl) true h))

  -- Four halves of bits, right-nested.

  hb4 : ∀ b₁ b₂ b₃ b₄ →
        (hb b₁ + (hb b₂ + (hb b₃ + (hb b₄ + 0ℤ)))) ≡ᴹ
        hb (b₁ xor (b₂ xor (b₃ xor b₄)))
  hb4 b₁ b₂ b₃ b₄ =
    ≡ᴹ-trans (≡ᴹ-+ {a = hb b₁} ≡ᴹ-refl
      (≡ᴹ-trans (≡ᴹ-+ {a = hb b₂} ≡ᴹ-refl
        (≡ᴹ-trans (≡ᴹ-+ {a = hb b₃} ≡ᴹ-refl (≡⇒≡ᴹ (+-identityʳ (hb b₄))))
                  (hb-xor b₃ b₄)))
        (hb-xor b₂ (b₃ xor b₄))))
    (hb-xor b₁ (b₂ xor (b₃ xor b₄)))

  -- One gadget's terms.

  gadget-val : (g : Fin n) (x y : Fin (n ℕ.+ n) → Bool) →
               Σˡ (gadgetTerms g)
                  (λ t → if satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ)
               ≡ᴹ hb (term (G₀ x y g) (prevAt true (G₀ x y) g))
  gadget-val {n} g x y = ≡ᴹ-trans
    (≡⇒≡ᴹ (cong₂ _+_ (term-val {n} (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ y[ aw g ] ⟫) x y)
      (cong₂ _+_ (term-val {n} (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ x[ aw g ] ⟫) x y)
        (cong₂ _+_ (term-val {n} (⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) x y)
          (cong (_+ 0ℤ)
            (term-val {n} ((⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) ∪ᵐ ⟪ x[ xw g ] ⟫)
                      x y))))))
    (≡ᴹ-trans (hb4 (satᵐ (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ y[ aw g ] ⟫) x y)
                   (satᵐ (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ x[ aw g ] ⟫) x y)
                   (satᵐ (⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) x y)
                   (satᵐ ((⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) ∪ᵐ ⟪ x[ xw g ] ⟫)
                         x y))
      (≡⇒≡ᴹ (cong hb (sym (trans
        (bool4 (y (xw g)) (y (aw g)) (x (aw g)) (x (xw g)) p)
        (cong₂ _xor_ (sym s₁)
          (cong₂ _xor_ (sym s₂)
            (cong₂ _xor_ (sym s₃) (sym s₄)))))))))
    where
    p : Bool
    p = prevAt true (G₀ x y) g

    s₁ : satᵐ (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ y[ aw g ] ⟫) x y ≡ y (xw g) ∧ y (aw g)
    s₁ = trans (satᵐ-∪ ⟪ y[ xw g ] ⟫ ⟪ y[ aw g ] ⟫ x y)
               (cong₂ _∧_ (satᵐ-⟪⟫ y[ xw g ] x y) (satᵐ-⟪⟫ y[ aw g ] x y))

    s₂ : satᵐ (⟪ y[ xw g ] ⟫ ∪ᵐ ⟪ x[ aw g ] ⟫) x y ≡ y (xw g) ∧ x (aw g)
    s₂ = trans (satᵐ-∪ ⟪ y[ xw g ] ⟫ ⟪ x[ aw g ] ⟫ x y)
               (cong₂ _∧_ (satᵐ-⟪⟫ y[ xw g ] x y) (satᵐ-⟪⟫ x[ aw g ] x y))

    s₃ : satᵐ (⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) x y ≡ y (xw g) ∧ p
    s₃ = trans (satᵐ-∪ ⟪ y[ xw g ] ⟫ (prevMon g) x y)
               (cong₂ _∧_ (satᵐ-⟪⟫ y[ xw g ] x y) (sat-prev g x y))

    s₄ : satᵐ ((⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) ∪ᵐ ⟪ x[ xw g ] ⟫) x y ≡
         (y (xw g) ∧ p) ∧ x (xw g)
    s₄ = trans (satᵐ-∪ (⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) ⟪ x[ xw g ] ⟫ x y)
               (cong₂ _∧_ s₃ (satᵐ-⟪⟫ x[ xw g ] x y))

  ΣF-≡ᴹ : {f f′ : Fin n → ℤ} → (∀ g → f g ≡ᴹ f′ g) → ΣF f ≡ᴹ ΣF f′
  ΣF-≡ᴹ {zero}  h = ≡ᴹ-refl
  ΣF-≡ᴹ {suc n} h = ≡ᴹ-+ (h zero) (ΣF-≡ᴹ (λ g → h (suc g)))

-- The phase of ξ n is ½ times the phase bit of the all-live ladder,
-- modulo 1.

eval-ξ-phase : (n : ℕ) (x y : Fin (n ℕ.+ n) → Bool) →
               eval (phase (ξ n)) x y ≡ᴹ hb (Bsum true (G₀ {n} x y))
eval-ξ-phase n x y = ≡ᴹ-trans
  (≡⇒≡ᴹ (trans (eval-⟦⟧ˢ (phaseTerms n) x y)
                (Σˡ-concatF {n} gadgetTerms
                  (λ t → if satᵐ (proj₁ t) x y then coeff (proj₂ t) else 0ℤ))))
  (≡ᴹ-trans (ΣF-≡ᴹ {n} (λ g → gadget-val g x y))
            (ΣF-Bsum true (G₀ {n} x y)))

-- Its outputs, read modulo 2: x_g on wire x_g and v_g on wire a_g.

outVal : (n : ℕ) (x y : Fin (n ℕ.+ n) → Bool) → Fin (n ℕ.+ n) → Bool
outVal n x y w =
  [ (λ g → x (xw {n} g)) , (λ g → y (aw {n} g)) ]′ (splitAt n w)

odd-ξ-out : (n : ℕ) (w : Fin (n ℕ.+ n)) (x y : Fin (n ℕ.+ n) → Bool) →
            odd (eval (out (ξ n) w) x y) ≡ outVal n x y w
odd-ξ-out n w x y = trans (cong odd (eval-liftᴸ (outForm n w) x y))
  (trans (odd-[] (valᴸ (outForm n w) x y)) (by (splitAt n w)))
  where
  by : (s : Fin n ⊎ Fin n) →
       valᴸ ([ (λ g → varᴸ x[ xw {n} g ]) , (λ g → varᴸ y[ aw {n} g ]) ]′ s)
            x y ≡
       [ (λ g → x (xw {n} g)) , (λ g → y (aw {n} g)) ]′ s
  by (inj₁ g) = valᴸ-var x[ xw {n} g ] x y
  by (inj₂ g) = valᴸ-var y[ aw {n} g ] x y
