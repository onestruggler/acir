------------------------------------------------------------------------
-- Presentations of groups
--
-- A family of Clifford+T circuits whose path-sums need space cubic in
-- the volume (Amy, QPL 2018, section 2.2)
--
-- Section 2.2 of the paper says that "even for the standard
-- Clifford+T gate set, the path-sum of a circuit requires space cubic
-- in the volume of the circuit [4]".  PathSum.Size proves the upper
-- bound: the phase of ⟦ C ⟧ (definition 2.9) has degree at most 3
-- modulo 1, so it is written with at most (n + |C| + 1)^3 terms
-- (repᴷ-length).  This module proves that the bound is attained, up
-- to a constant, as a function of the volume n · |C| alone.
--
-- * What "requires" can mean.  A path-sum's phase is determined
--   modulo 1 by its values, and by Möbius inversion its multilinear
--   coefficients are then determined modulo 1 too
--   (PathSum.Fourier.phase-unique).  So every representation of the
--   path-sum ⟦ C ⟧ that writes its phase as a list of monomial terms
--   (PathSum.Size.Sparse.Represents) lists every monomial whose
--   coefficient is not an integer, and its length is at least their
--   number.  That is a lower bound for the path-sum of the circuit,
--   the object the paper speaks of -- not for every path-sum with the
--   same operator, nor for other representations of the phase: its
--   Fourier expansion, for one, has at most three terms per gate
--   (PathSum.Fourier.Circuit), which is the paper's point in the next
--   paragraph -- on this family, at most 6k + 3 terms against the
--   C(k, 3) every multilinear representation needs
--   (fourier-vs-multilinear).
--
-- * The family.  Cube k, on two wires a and b, is k rounds of
--   (H a ; CNOT a b) followed by one T gate on b.  Each round puts a
--   fresh path variable on a and adds it to b, so after k rounds b
--   holds x_b ⊕ y_1 ⊕ ... ⊕ y_k (Shape); the rounds are Clifford, so
--   their phase has order at most 2 (proposition 2.14's argument), and
--   the T gate adds ⅛ times the lifting of that parity, whose
--   coefficient on every product of three of its variables is
--   ⅛ · (−2)^2 = ½.  So the phase of ⟦ Cube k ⟧ has a non-integer
--   coefficient on each of the C(k, 3) monomials y_i y_j y_l
--   (cubic-coefficient), and every representation of ⟦ Cube k ⟧ has at
--   least C(k, 3) terms (cubic-lower-bound).
--
-- * In the volume.  Cube k has 2k + 1 gates on 2 wires, volume
--   V = 4k + 2 (Cube-volume), and (V − 10)^3 ≤ 384 · C(k, 3)
--   (cubic-in-volume), so every representation has at least
--   (V − 10)^3 / 384 terms; and PathSum.Size's representation has at
--   most (2k + 4)^3 ≤ (V + 2)^3 (cubic-upper-bound).  So the space is
--   Θ(V^3) on this family -- with a single T gate, and two qubits.
--   cubic-space-Θ states the three facts together: that representation
--   represents ⟦ Cube k ⟧ (PathSum.Size.repᴷ-represents), has at most
--   (V + 2)^3 terms, and every representation has at least
--   (V − 10)^3 / 384.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Size.Cubic (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _xor_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset using (Subset; inside; outside; ⊥; ⊤; ⁅_⁆; ∣_∣)
open import Data.Fin.Subset.Properties using (⊥⊆; ⊆⊤; ∣⊥∣≡0)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣m+n∣m⇒∣n; ∣m∣n⇒∣m+n; ∣⇒∣ᵤ)
open import Data.Integer.Properties using (*-zeroʳ; +-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (length-map; length-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using
  (_≤_; _<_; _⊔_; _∸_; _^_; z≤n; s≤s)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.Combinatorics using
  (_C_; nCk+nC[k+1]≡[n+1]C[k+1]; nC1≡n)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_; zipWith)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Properties as ℕ
import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Solver as ℕSolver
import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; State; state; poly; sig; init; stepH;
   stepCNOT; stepR; run; run-++; ⟦_⟧; paths; level; Ord≤⇒Deg≤;
   Ord≤-wkPoly; Ord≤-mul-y₀)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ; wkLin; _⊕ᴸ_)
open import PathSum.Order M using (Ord≤; Ord≤-+; Ord≤-0ᴾ; Ord≤-liftXor; pow; pow-suc)
open import PathSum.Polynomial using
  (Mon; Poly; 1ᵐ; ∥_∥; x[_]; y[_]; _≟ᵐ_; _⊆ᵐ?_; _≈[_]_; liftXor; sgn;
   negpow)
open import PathSum.Polynomial.Count using
  (count; count-cong; count-false; count-cover)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; Rep; terms; Represents)

import PathSum.Fourier
import PathSum.Fourier.Circuit
import PathSum.Size

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  module Sz = PathSum.Size M
  module Fo = PathSum.Fourier M₀
  module FC = PathSum.Fourier.Circuit M₀

  variable
    k : ℕ

  -- Decisions read off.

  ⌊⌋-true : ∀ {A : Set} (d : Dec A) → A → ⌊ d ⌋ ≡ true
  ⌊⌋-true (yes _) _ = refl
  ⌊⌋-true (no ¬a) a = contradiction a ¬a

  ⌊⌋-false : ∀ {A : Set} (d : Dec A) → ¬ A → ⌊ d ⌋ ≡ false
  ⌊⌋-false (yes a) ¬a = contradiction a ¬a
  ⌊⌋-false (no _)  _  = refl


------------------------------------------------------------------------
-- The family

a b : Fin 2
a = fzero
b = fsuc fzero

-- One round: a fresh path variable on a, added to b.

round : Circuit 2
round = H a ∷ CNOT a b (λ ()) ∷ []

rounds : ℕ → Circuit 2
rounds zero    = []
rounds (suc k) = rounds k ++ round

-- k rounds, then T on b.

Cube : ℕ → Circuit 2
Cube k = rounds k ++ R 3 b ∷ []


------------------------------------------------------------------------
-- The state after the rounds

-- The parity on b after k rounds: x_b and every path variable.

formB : ∀ k → Lin 2 k
formB k = false , (⁅ b ⁆ , ⊤)

-- What the rounds leave: k path variables, that parity on b, and a
-- phase of order at most 2.

data Shape (k : ℕ) : ∃ (State 2) → Set where
  shape : (st : State 2 k) → sig st b ≡ formB k → Ord≤ 2 (poly st) →
          Shape k (k , st)

private
  xor-⊤⊥ : ∀ k → zipWith _xor_ (⊤ {k}) ⊥ ≡ ⊤
  xor-⊤⊥ zero    = refl
  xor-⊤⊥ (suc k) = cong (inside ∷_) (xor-⊤⊥ k)

-- A round adds a variable to b; the Hadamard's term ½ f_a y₀ has order
-- 2, as in proposition 2.14.

step-round : ∀ {k} {p : ∃ (State 2)} → Shape k p →
             Shape (suc k) (run round (proj₂ p))
step-round {k} (shape st e o) = shape (stepCNOT a b (stepH a st))
  (trans (cong (λ l → wkLin l ⊕ᴸ varᴸ y[ fzero ]) e)
         (cong (λ s → false , (⁅ b ⁆ , inside ∷ s)) (xor-⊤⊥ k)))
  (Ord≤-+ (Ord≤-wkPoly o)
    (Ord≤-mul-y₀ (Ord≤-liftXor 1 (proj₁ (sig st a)) (proj₂ (sig st a)))))

shape-rounds : ∀ k → Shape k (run (rounds k) init)
shape-rounds zero    = shape init refl Ord≤-0ᴾ
shape-rounds (suc k) = subst (Shape (suc k))
  (sym (run-++ (rounds k) round init)) (step-round (shape-rounds k))


------------------------------------------------------------------------
-- The T gate's cubic terms

private
  -- 2^(e+1) does not divide 2^e.

  pow-∤ : ∀ e → ¬ (pow (suc e) ∣ pow e)
  pow-∤ e h = ℕ.<⇒≱ (ℕ.^-monoʳ-< 2 (s≤s (s≤s z≤n)) (ℕ.n<1+n e))
                    (ℕDiv.∣⇒≤ {{ℕ.m^n≢0 2 e}} (∣⇒∣ᵤ h))

  pick : ∀ d₁ d₂ (v : ℤ) → d₁ ≡ false → d₂ ≡ true →
         (if d₁ then 0ℤ else if d₂ then v else 0ℤ) ≡ v
  pick false true v refl refl = refl

  3≢0 : ¬ (3 ≡ 0)
  3≢0 ()

  -- The lifting of x_b ⊕ y_1 ⊕ ... ⊕ y_k has coefficient (−2)^2 = 4 on
  -- every product of three path variables.

  lift-cubic : (β : Subset k) → ∣ β ∣ ≡ 3 →
               liftXor false (⁅ b ⁆ , ⊤) (⊥ , β) ≡ + 4
  lift-cubic {k} β h = trans
    (pick ⌊ γ ≟ᵐ 1ᵐ ⌋ ⌊ γ ⊆ᵐ? S ⌋ _
      (⌊⌋-false (γ ≟ᵐ 1ᵐ) (λ eq →
        3≢0 (trans (sym h) (trans (cong (λ δ → ∣ proj₂ δ ∣) eq) (∣⊥∣≡0 k)))))
      (⌊⌋-true (γ ⊆ᵐ? S) (⊥⊆ , ⊆⊤)))
    (cong (λ s → sgn false * negpow (s ∸ 1)) h)
    where
    γ S : Mon 2 k
    γ = ⊥ , β
    S = ⁅ b ⁆ , ⊤

  four : pow M₀ * + 4 ≡ pow (suc (suc M₀))
  four = sym (trans (pow-suc (suc M₀))
    (trans (cong (λ q → q * + 2) (pow-suc M₀))
           (solve 1 (λ p → p :* con (+ 2) :* con (+ 2) := p :* con (+ 4))
                  refl (pow M₀))))

-- After the rounds, T on b: every product of three path variables has a
-- coefficient that is not an integer (½, modulo 1).

coefficient : ∀ k (st : State 2 k) → sig st b ≡ formB k →
              Ord≤ 2 (poly st) → (β : Subset k) → ∣ β ∣ ≡ 3 →
              ¬ (pow M ∣ poly (stepR 3 b st) (⊥ , β))
coefficient k st e o β h d = pow-∤ (suc (suc M₀))
  (subst (pow M ∣_) term (∣m+n∣m⇒∣n d deg))
  where
  deg : pow M ∣ poly st (⊥ , β)
  deg = Ord≤⇒Deg≤ o (⊥ , β) (subst (2 <_) (sym h) (s≤s (s≤s (s≤s z≤n))))

  term : pow M₀ * liftᴸ (sig st b) (⊥ , β) ≡ pow (suc (suc M₀))
  term = trans (cong (λ l → pow M₀ * liftᴸ l (⊥ , β)) e)
               (trans (cong (pow M₀ *_) (lift-cubic β h)) four)


------------------------------------------------------------------------
-- Counting the cubic monomials

-- The subsets of k variables of size j: C(k, j) of them.

private
  -- ⌊ suc a ≟ suc b ⌋ is ⌊ a ≟ b ⌋ (propositionally: the builtin
  -- equality test does not reduce on open terms).

  suc≟suc : ∀ a b → ⌊ suc a ℕ.≟ suc b ⌋ ≡ ⌊ a ℕ.≟ b ⌋
  suc≟suc a b = helper (a ℕ.≟ b)
    where
    helper : Dec (a ≡ b) → ⌊ suc a ℕ.≟ suc b ⌋ ≡ ⌊ a ℕ.≟ b ⌋
    helper (yes e) = trans (⌊⌋-true (suc a ℕ.≟ suc b) (cong suc e))
                           (sym (⌊⌋-true (a ℕ.≟ b) e))
    helper (no ne) = trans (⌊⌋-false (suc a ℕ.≟ suc b)
                                     (λ e → ne (ℕ.suc-injective e)))
                           (sym (⌊⌋-false (a ℕ.≟ b) ne))

count-size : ∀ k j → count {k} (λ β → ⌊ ∣ β ∣ ℕ.≟ j ⌋) ≡ k C j
count-size zero    zero    = refl
count-size zero    (suc j) = refl
count-size (suc k) zero    = cong₂ _ℕ+_ (count-false {k}) (count-size k zero)
count-size (suc k) (suc j) =
  trans (cong₂ _ℕ+_ (trans (count-cong (λ (s : Subset k) → suc≟suc ∣ s ∣ j))
                           (count-size k j))
                    (count-size k (suc j)))
        (nCk+nC[k+1]≡[n+1]C[k+1] k j)

-- A list of terms whose sum has a coefficient that is not an integer
-- on γ lists γ.

listedˢ : ∀ {n m} (ts : List (Term n m)) (γ : Mon n m) →
          ¬ (pow M ∣ ⟦ ts ⟧ˢ γ) → γ ∈ map proj₁ ts
listedˢ []             γ h = contradiction i∣0 h
listedˢ ((δ , c) ∷ ts) γ h = by (γ ≟ᵐ δ)
  where
  by : Dec (γ ≡ δ) → γ ∈ map proj₁ ((δ , c) ∷ ts)
  by (yes γ≡δ) = here γ≡δ
  by (no γ≢δ)  = there (listedˢ ts γ (λ d → h (subst (pow M ∣_) (sym drop) d)))
    where
    zero-term : monoᴾ δ γ ≡ 0ℤ
    zero-term = cong (λ t → if t then + 1 else 0ℤ) (⌊⌋-false (γ ≟ᵐ δ) γ≢δ)

    drop : coeff c * monoᴾ δ γ + ⟦ ts ⟧ˢ γ ≡ ⟦ ts ⟧ˢ γ
    drop = trans (cong (λ t → coeff c * t + ⟦ ts ⟧ˢ γ) zero-term)
                 (trans (cong (λ t → t + ⟦ ts ⟧ˢ γ) (*-zeroʳ (coeff c)))
                        (+-identityˡ (⟦ ts ⟧ˢ γ)))

-- Any list of terms representing the phase modulo 1 has at least C(k, 3)
-- of them.

lb-state : ∀ k (st : State 2 k) → sig st b ≡ formB k → Ord≤ 2 (poly st) →
           (ts : List (Term 2 k)) → poly (stepR 3 b st) ≈[ pow M ] ⟦ ts ⟧ˢ →
           k C 3 ≤ length ts
lb-state k st e o ts eq = subst (_≤ length ts) (count-size k 3)
  (ℕ.≤-trans (count-cover _≟ᵐ_ p g inj (map proj₁ ts) cov)
             (ℕ.≤-reflexive (length-map proj₁ ts)))
  where
  p : Subset k → Bool
  p β = ⌊ ∣ β ∣ ℕ.≟ 3 ⌋

  g : Subset k → Mon 2 k
  g β = ⊥ , β

  inj : ∀ s t → g s ≡ g t → s ≡ t
  inj s t eq′ = cong proj₂ eq′

  extract : ∀ {A : Set} (d : Dec A) → ⌊ d ⌋ ≡ true → A
  extract (yes x) _  = x
  extract (no _)  ()

  size3 : ∀ β → p β ≡ true → ∣ β ∣ ≡ 3
  size3 β h = extract (∣ β ∣ ℕ.≟ 3) h

  cov : ∀ β → p β ≡ true → g β ∈ map proj₁ ts
  cov β pβ = listedˢ ts (⊥ , β) (λ d →
    coefficient k st e o β (size3 β pβ)
      (subst (pow M ∣_) (back (poly (stepR 3 b st) (⊥ , β)) (⟦ ts ⟧ˢ (⊥ , β)))
             (∣m∣n⇒∣m+n (eq (⊥ , β)) d)))
    where
    back : ∀ u v → (u - v) + v ≡ u
    back = solve 2 (λ u v → (u :- v) :+ v := u) refl


------------------------------------------------------------------------
-- The circuits' path-sums

-- Statements about the state a run ends in, so that they can be read at
-- ⟦ Cube k ⟧, whose number of path variables is computed by the run.

private
  LB : ℕ → ∃ (State 2) → Set
  LB k p = ∀ (ts : List (Term 2 (proj₁ p))) →
           poly (proj₂ p) ≈[ pow M ] ⟦ ts ⟧ˢ → k C 3 ≤ length ts

  NonInt : ∃ (State 2) → Set
  NonInt p = ∀ (β : Subset (proj₁ p)) → ∣ β ∣ ≡ 3 →
             ¬ (pow M ∣ poly (proj₂ p) (⊥ , β))

  Paths : ℕ → ∃ (State 2) → Set
  Paths k p = proj₁ p ≡ k

  after-T : ∀ {k} {p} → Shape k p →
            let q = run (R 3 b ∷ []) (proj₂ p) in
            LB k q × NonInt q × Paths k q
  after-T {k} (shape st e o) =
    lb-state k st e o , coefficient k st e o , refl

  cube : ∀ k → let q = run (Cube k) init in
         LB k q × NonInt q × Paths k q
  cube k = subst (λ q → LB k q × NonInt q × Paths k q)
    (sym (run-++ (rounds k) (R 3 b ∷ []) init)) (after-T (shape-rounds k))

-- ⟦ Cube k ⟧ has k path variables ...

Cube-paths : ∀ k → paths (Cube k) ≡ k
Cube-paths k = proj₂ (proj₂ (cube k))

-- ... a coefficient that is not an integer on each product of three of
-- them ...

cubic-coefficient : ∀ k (β : Subset (paths (Cube k))) → ∣ β ∣ ≡ 3 →
                    ¬ (pow M ∣ phase ⟦ Cube k ⟧ (⊥ , β))
cubic-coefficient k = proj₁ (proj₂ (cube k))

-- ... so every representation of it lists at least C(k, 3) terms.

cubic-lower-bound : ∀ k (ρ : Rep 2 (paths (Cube k))) →
                    Represents ⟦ Cube k ⟧ ρ → k C 3 ≤ length (terms ρ)
cubic-lower-bound k ρ rep = proj₁ (cube k) (terms ρ) (proj₁ rep)


------------------------------------------------------------------------
-- In the volume

private
  open ℕSolver.+-*-Solver using () renaming
    (solve to solveℕ; _:+_ to _⊕_; _:*_ to _⊛_; con to cn; _:=_ to _≐_)

  level-++ : (X Y : Circuit 2) → level (X ++ Y) ≡ level X ⊔ level Y
  level-++ []                Y = refl
  level-++ (H _ ∷ X)         Y = level-++ X Y
  level-++ (CNOT _ _ _ ∷ X)  Y = level-++ X Y
  level-++ (R k _ ∷ X)       Y =
    trans (cong (k ⊔_) (level-++ X Y)) (sym (ℕ.⊔-assoc k (level X) (level Y)))
  level-++ (R† k _ ∷ X)      Y =
    trans (cong (k ⊔_) (level-++ X Y)) (sym (ℕ.⊔-assoc k (level X) (level Y)))

  level-rounds : ∀ k → level (rounds k) ≡ 0
  level-rounds zero    = refl
  level-rounds (suc k) =
    trans (level-++ (rounds k) round) (cong (_⊔ 0) (level-rounds k))

  length-rounds : ∀ k → length (rounds k) ≡ 2 ℕ* k
  length-rounds zero    = refl
  length-rounds (suc k) = trans (length-++ (rounds k) {round})
    (trans (cong (_ℕ+ 2) (length-rounds k))
           (solveℕ 1 (λ k → cn 2 ⊛ k ⊕ cn 2 ≐ cn 2 ⊛ (cn 1 ⊕ k)) refl k))

-- Cube k has 2k + 1 gates on two wires, level 3.

Cube-length : ∀ k → length (Cube k) ≡ suc (2 ℕ* k)
Cube-length k = trans (length-++ (rounds k) {R 3 b ∷ []})
  (trans (cong (_ℕ+ 1) (length-rounds k)) (ℕ.+-comm (2 ℕ* k) 1))

Cube-level : ∀ k → level (Cube k) ≡ 3
Cube-level k = trans (level-++ (rounds k) (R 3 b ∷ []))
                     (cong (_⊔ 3) (level-rounds k))

-- Its volume n · |C| is 4k + 2.

Cube-volume : ∀ k → 2 ℕ* length (Cube k) ≡ 4 ℕ* k ℕ+ 2
Cube-volume k = trans (cong (2 ℕ*_) (Cube-length k))
  (solveℕ 1 (λ k → cn 2 ⊛ (cn 1 ⊕ cn 2 ⊛ k) ≐ cn 4 ⊛ k ⊕ cn 2) refl k)

-- PathSum.Size's representation has at most (2k + 4)^3 terms.

cubic-upper-bound : ∀ k → length (terms (Sz.repᴷ (Cube k))) ≤ (4 ℕ+ 2 ℕ* k) ^ 3
cubic-upper-bound k = subst₂ (λ ℓ d → length (terms (Sz.repᴷ (Cube k))) ≤
                                       suc (2 ℕ+ ℓ) ^ (2 ⊔ d))
  (Cube-length k) (Cube-level k) (Sz.repᴷ-length (Cube k))

-- 6 C(j + 2, 3) = (j + 2)(j + 1) j.

private
  two-C : ∀ j → 2 ℕ* (suc j C 2) ≡ suc j ℕ* j
  two-C zero    = refl
  two-C (suc j) = trans
    (cong (2 ℕ*_) (sym (nCk+nC[k+1]≡[n+1]C[k+1] (suc j) 1)))
    (trans (cong (λ t → 2 ℕ* (t ℕ+ suc j C 2)) (nC1≡n (suc j)))
      (trans (ℕ.*-distribˡ-+ 2 (suc j) (suc j C 2))
        (trans (cong (λ t → 2 ℕ* suc j ℕ+ t) (two-C j))
               (solveℕ 1 (λ j → cn 2 ⊛ (cn 1 ⊕ j) ⊕ (cn 1 ⊕ j) ⊛ j ≐
                                (cn 2 ⊕ j) ⊛ (cn 1 ⊕ j)) refl j))))

  six-C : ∀ j → 6 ℕ* (suc (suc j) C 3) ≡ suc (suc j) ℕ* suc j ℕ* j
  six-C zero    = refl
  six-C (suc j) = trans
    (cong (6 ℕ*_) (sym (nCk+nC[k+1]≡[n+1]C[k+1] (suc (suc j)) 2)))
    (trans (ℕ.*-distribˡ-+ 6 (suc (suc j) C 2) (suc (suc j) C 3))
      (trans (cong₂ _ℕ+_ (trans (solveℕ 1 (λ t → cn 6 ⊛ t ≐ cn 3 ⊛ (cn 2 ⊛ t))
                                         refl (suc (suc j) C 2))
                                (cong (3 ℕ*_) (two-C (suc j))))
                         (six-C j))
             (solveℕ 1 (λ j → cn 3 ⊛ ((cn 2 ⊕ j) ⊛ (cn 1 ⊕ j)) ⊕
                              (cn 2 ⊕ j) ⊛ (cn 1 ⊕ j) ⊛ j ≐
                              (cn 3 ⊕ j) ⊛ (cn 2 ⊕ j) ⊛ (cn 1 ⊕ j)) refl j)))

  cube≤ : ∀ j → j ^ 3 ≤ suc (suc j) ℕ* suc j ℕ* j
  cube≤ j = subst (_≤ suc (suc j) ℕ* suc j ℕ* j)
    (solveℕ 1 (λ j → j ⊛ j ⊛ j ≐ j ⊛ (j ⊛ (j ⊛ cn 1))) refl j)
    (ℕ.*-mono-≤ (ℕ.*-mono-≤ (ℕ.≤-trans (ℕ.n≤1+n j) (ℕ.n≤1+n (suc j)))
                            (ℕ.n≤1+n j))
                (ℕ.≤-refl {j}))

-- (V − 10)^3 ≤ 384 C(k, 3) for the volume V = 4k + 2.

cubic-in-volume : ∀ k → (2 ℕ* length (Cube k) ∸ 10) ^ 3 ≤ 384 ℕ* (k C 3)
cubic-in-volume k = subst (λ v → (v ∸ 10) ^ 3 ≤ 384 ℕ* (k C 3))
  (sym (Cube-volume k)) (by k)
  where
  by : ∀ k → (4 ℕ* k ℕ+ 2 ∸ 10) ^ 3 ≤ 384 ℕ* (k C 3)
  by zero                = z≤n
  by (suc zero)          = z≤n
  by (suc (suc j))       = subst (_≤ 384 ℕ* (suc (suc j) C 3))
    (cong (_^ 3) (sym shift))
    (ℕ.≤-trans (ℕ.≤-reflexive (solveℕ 1 (λ j → (cn 4 ⊛ j) ⊛ ((cn 4 ⊛ j) ⊛ ((cn 4 ⊛ j) ⊛ cn 1)) ≐
                                                   cn 64 ⊛ (j ⊛ (j ⊛ (j ⊛ cn 1)))) refl j))
      (ℕ.≤-trans (ℕ.*-monoʳ-≤ 64 (cube≤ j))
        (ℕ.≤-reflexive (trans (cong (64 ℕ*_) (sym (six-C j)))
                              (sym (ℕ.*-assoc 64 6 (suc (suc j) C 3)))))))
    where
    shift : 4 ℕ* suc (suc j) ℕ+ 2 ∸ 10 ≡ 4 ℕ* j
    shift = trans (cong (_∸ 10) (solveℕ 1 (λ j → cn 4 ⊛ (cn 2 ⊕ j) ⊕ cn 2 ≐
                                                  cn 4 ⊛ j ⊕ cn 10) refl j))
                  (ℕ.m+n∸n≡m (4 ℕ* j) 10)

-- Hence every representation of ⟦ Cube k ⟧ has at least (V − 10)^3/384
-- terms: cubic in the volume.

cubic-volume-lower-bound :
  ∀ k (ρ : Rep 2 (paths (Cube k))) → Represents ⟦ Cube k ⟧ ρ →
  (2 ℕ* length (Cube k) ∸ 10) ^ 3 ≤ 384 ℕ* length (terms ρ)
cubic-volume-lower-bound k ρ rep = ℕ.≤-trans (cubic-in-volume k)
  (ℕ.*-monoʳ-≤ 384 (cubic-lower-bound k ρ rep))


------------------------------------------------------------------------
-- Against the Fourier expansion

-- The same phase has a Fourier expansion with at most 3 (2k + 1)
-- terms (PathSum.Fourier.Circuit), while every multilinear
-- representation has at least C(k, 3): the paper's two representations
-- of the phase, linear and cubic on one family.

fourier-vs-multilinear : ∀ k →
  (∃ λ (E : Fo.Expansion 2 (paths (Cube k))) →
     Fo.sizeᶠ E ≤ 3 ℕ* length (Cube k) × Fo.FourierOf 0 E (phase ⟦ Cube k ⟧)) ×
  (∀ (ρ : Rep 2 (paths (Cube k))) → Represents ⟦ Cube k ⟧ ρ →
     k C 3 ≤ length (terms ρ))
fourier-vs-multilinear k =
  FC.circuit-fourier-linear (Cube k) , cubic-lower-bound k


------------------------------------------------------------------------
-- Θ(V^3), in one statement

private
  -- 4 + 2k ≤ V + 2 for the volume V = 2 |Cube k| = 4k + 2.

  upper-in-volume : ∀ k → 4 ℕ+ 2 ℕ* k ≤ 2 ℕ* length (Cube k) ℕ+ 2
  upper-in-volume k = subst (λ v → 4 ℕ+ 2 ℕ* k ≤ v ℕ+ 2) (sym (Cube-volume k))
    (subst (4 ℕ+ 2 ℕ* k ≤_)
      (solveℕ 1 (λ k → (cn 4 ⊕ cn 2 ⊛ k) ⊕ cn 2 ⊛ k ≐ cn 4 ⊛ k ⊕ cn 2 ⊕ cn 2)
              refl k)
      (ℕ.m≤m+n (4 ℕ+ 2 ℕ* k) (2 ℕ* k)))

-- With V = 2 |Cube k| the volume of Cube k: PathSum.Size's
-- representation of ⟦ Cube k ⟧ (corollary 2.15) has at most (V + 2)^3
-- terms, and every representation has at least (V − 10)^3 / 384 --
-- the space of the path-sum is Θ(V^3) on this family.

cubic-space-Θ : ∀ k →
  Represents ⟦ Cube k ⟧ (Sz.repᴷ (Cube k)) ×
  length (terms (Sz.repᴷ (Cube k))) ≤ (2 ℕ* length (Cube k) ℕ+ 2) ^ 3 ×
  (∀ (ρ : Rep 2 (paths (Cube k))) → Represents ⟦ Cube k ⟧ ρ →
     (2 ℕ* length (Cube k) ∸ 10) ^ 3 ≤ 384 ℕ* length (terms ρ))
cubic-space-Θ k =
  Sz.repᴷ-represents (Cube k) ,
  ℕ.≤-trans (cubic-upper-bound k) (ℕ.^-monoˡ-≤ 3 (upper-in-volume k)) ,
  cubic-volume-lower-bound k
