------------------------------------------------------------------------
-- Presentations of groups
--
-- Reifying the isometry restriction by substitution, for any outputs
-- (Amy, QPL 2018, section 4.1)
--
-- The syntactic side of PathSum.Restrict.  Section 4.1 reifies the
-- restriction "if for some index i we have f_i(x,y) = y_i ⊕ Q(x,y)
-- where y_i doesn't appear in Q(x,y)".  Outputs are polynomials read
-- modulo 2, so that hypothesis says: the quotient of f_w by y_j is 1
-- modulo 2 (Pivot ξ w j, decidable: pivot?).  Writing f_w = y_j · A + B
-- with A = f_w /ʸ j and B = f_w ∖ʸ j both free of y_j, it is A ≡ 1, and
-- then f_w = y_j ⊕ B: Q is B.  The paper's own form of the hypothesis,
-- f_w ≡ y_j + Q modulo 2 with y_j not in Q, implies it (pivot-intro).
--
-- The step (restrictᴾ ξ w j) substitutes the solution
-- S = lift(x_w ⊕ Q) for y_j -- lifted as definition 2.6 lifts the
-- outputs it substitutes, by PathSum.Polynomial.Boolean.liftᴮ, so that
-- S takes exactly the value 0 or 1 of x_w ⊕ Q -- in the phase and in
-- every other output, and replaces f_w by x_w.  On the path y_j =
-- x_w ⊕ Q every output and the phase are the reduct's, and on the other
-- one f_w reads ¬x_w; that is a Restricts record (restrictᴾ-step), so
-- all of PathSum.Restrict applies.  It is the substitution with Q of
-- any degree, any constant included: an affine output 1 ⊕ y_j (an X
-- gate after a Hadamard) has Q = 1 and solution ¬x_w.
--
-- The reduct is unique: two restriction steps at the same wire and
-- path variable keep the same paths, and their reducts agree
-- coefficient by coefficient, the phases modulo 1 and the outputs
-- modulo 2 (restricts-unique, by Möbius inversion through
-- PathSum.Polynomial.Boolean.≈-from-values).  So a reduct written by
-- hand and checked against the semantic conditions -- as for a
-- composite, whose polynomials do not compute -- is the paper's
-- substitution (restricts≈restrictᴾ).
--
-- The procedure (restriction): substitute while some output has a
-- pivot, then stop.  What it stops at has no pivot left
-- (Restriction.stuck): the outputs that cannot be reified this way
-- are the ones section 4.1 "simply ignores", and PathSum.Restrict's
-- theorems read the verdict off the result whatever they are.  It
-- terminates since each step removes a path variable.  An output it
-- leaves free of path variables is either x_w modulo 2 -- solved, by
-- values (≈μ⇒Solved) -- or not, and then it refutes the identity at
-- some input with no well-formedness (settle-or-refute,
-- restriction-refutes-syntactic; PathSum.Interference.
-- even-or-odd-input finds the input).
--
-- Nothing here computes on closed instances in practice: liftᴮ folds
-- ⊕ over every monomial, and substAt multiplies dense polynomials.
-- Closed examples (PathSum.Examples.Restrict) write their reducts by
-- hand and check the semantic conditions instead, which by
-- restricts-unique is the same thing.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Restrict.Pivot (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (any?)
open import Data.Fin.Subset using (inside)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n)
open import Data.Integer.Properties using
  (+-identityʳ; +-inverseʳ; *-identityˡ; *-zeroˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (_∷_; here; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Bool.Properties as Bool
import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS)
open import PathSum.Denotation M₀ using (Assign; outBit; _≋_)
open import PathSum.HiddenShift.Sign M₀ using (odd-+; odd-[]; odd-≡)
open import PathSum.Interference M₀ using (even-or-odd-input)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; x[_]; y[_]; μ; κ; eval; _+ᴾ_; _-ᴾ_; 0ᴾ; _≈[_]_; NoVar)
open import PathSum.Polynomial.Bind using (odd; eval-liftᴮ)
open import PathSum.Polynomial.Boolean using (liftᴮ; ≈-from-values)
open import PathSum.Polynomial.Decidable using (_≈?[_]_)
open import PathSum.Polynomial.Product using (eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (eval-+ᴾ; eval-−ᴾ; eval-κ; eval-≈; i∣0)
open import PathSum.Polynomial.Substitution using (Absent-μ)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; _/ʸ_; _∖ʸ_; NoVar-front)
open import PathSum.Restrict M₀ using
  (substAt; eval-substAt; eval-insertᵃ; Solved; Restricts; _↝_; step;
   _↝*_; εʳ; _◅ʳ_; _⇝*_; restriction-refutes)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Parities

private
  odd-even : ∀ {z} → (+ 2) ∣ z → odd z ≡ false
  odd-even {z} d with (+ 2) ∣? z
  ... | yes _  = refl
  ... | no ¬d = contradiction d ¬d

  -- Integers congruent modulo 2 have the same parity.

  odd-cong : ∀ a b → (+ 2) ∣ (a - b) → odd a ≡ odd b
  odd-cong a b d = trans (cong odd (shape a b))
    (trans (odd-+ (a - b) b) (cong (λ c → c xor odd b) (odd-even d)))
    where
    shape : ∀ a b → a ≡ (a - b) + b
    shape = solve 2 (λ a b → a := (a :- b) :+ b) refl

  -- Times an odd number, a bit keeps its parity.

  odd-bit* : ∀ b a → odd a ≡ true → odd ([ b ]ᶻ * a) ≡ b
  odd-bit* true  a h = trans (cong odd (*-identityˡ a)) h
  odd-bit* false a h = trans (cong odd (*-zeroˡ a)) (odd-[] false)

  xor-back : ∀ q a → q xor (a xor q) ≡ a
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

  xor-miss : ∀ q a → q xor not (a xor q) ≡ not a
  xor-miss false false = refl
  xor-miss false true  = refl
  xor-miss true  false = refl
  xor-miss true  true  = refl

  not-≢ : ∀ b → not b ≢ b
  not-≢ false ()
  not-≢ true  ()

  ≢⇒not : ∀ {a} b → a ≢ b → a ≡ not b
  ≢⇒not {false} false ne = contradiction refl ne
  ≢⇒not {false} true  _  = refl
  ≢⇒not {true}  false _  = refl
  ≢⇒not {true}  true  ne = contradiction refl ne

  minus-0 : ∀ a → a - 0ℤ ≡ a
  minus-0 a = +-identityʳ a


------------------------------------------------------------------------
-- The quotient by a path variable

-- Its value is the difference of the values with y_j set to 1 and 0.

eval-/ʸ : (j : Fin (suc m)) (P : Poly n (suc m)) (x : Assign n)
          (g : Assign m) →
          eval (P /ʸ j) x g ≡
          eval P x (insertᵃ j true g) - eval P x (insertᵃ j false g)
eval-/ʸ j P x g = sym (trans
  (cong₂ _-_ (eval-insertᵃ j P x g true) (eval-insertᵃ j P x g false))
  (shape (eval (P /ʸ j) x g) (eval (P ∖ʸ j) x g)))
  where
  shape : ∀ a b → (b + 1ℤ * a) - (b + 0ℤ * a) ≡ a
  shape = solve 2 (λ a b → (b :+ con 1ℤ :* a) :- (b :+ con 0ℤ :* a) := a)
                  refl


------------------------------------------------------------------------
-- Pivots

-- f_w = y_j ⊕ Q with y_j not in Q, modulo 2: the quotient of f_w by y_j
-- is the constant 1.

Pivot : PathSum n k (suc m) → Fin n → Fin (suc m) → Set
Pivot ξ w j = (out ξ w /ʸ j) ≈[ + 2 ] κ 1ℤ

pivot? : (ξ : PathSum n k (suc m)) (w : Fin n) (j : Fin (suc m)) →
         Dec (Pivot ξ w j)
pivot? ξ w j = (out ξ w /ʸ j) ≈?[ + 2 ] κ 1ℤ

-- The paper's form: f_w ≡ y_j + Q modulo 2, with y_j not in Q modulo
-- 2.  The quotient of f_w by y_j is then, modulo 2, 1 plus the
-- quotient of Q, whose coefficients are even; by values and Möbius.

pivot-intro : (ξ : PathSum n k (suc m)) (w : Fin n) (j : Fin (suc m))
              (Q : Poly n (suc m)) →
              out ξ w ≈[ + 2 ] (μ y[ j ] +ᴾ Q) → NoVar (+ 2) y[ j ] Q →
              Pivot ξ w j
pivot-intro {n} {m = m} ξ w j Q f≈ noQ =
  ≈-from-values {c = + 2} (f /ʸ j) (κ 1ℤ) (λ x g → subst ((+ 2) ∣_)
    (cong (λ t → eval (f /ʸ j) x g - t) (sym (eval-κ 1ℤ x g)))
    (odd-ish x g))
  where
  f : Poly n (suc m)
  f = out ξ w

  μ/ : ∀ x g → eval (μ {n} {suc m} y[ j ] /ʸ j) x g ≡ 1ℤ
  μ/ x g = trans (eval-/ʸ j (μ y[ j ]) x g)
    (cong₂ _-_ (trans (eval-μᴾ y[ j ] x (insertᵃ j true g))
                      (cong [_]ᶻ (insertᵃ-here j true g)))
               (trans (eval-μᴾ y[ j ] x (insertᵃ j false g))
                      (cong [_]ᶻ (insertᵃ-here j false g))))

  Q/even : ∀ x g → (+ 2) ∣ eval (Q /ʸ j) x g
  Q/even x g = subst ((+ 2) ∣_)
    (trans (cong (λ t → eval (Q /ʸ j) x g - t) (eval-0ᴾ x g))
           (minus-0 (eval (Q /ʸ j) x g)))
    (eval-≈ {d = + 2} (Q /ʸ j) 0ᴾ (λ { (α , s) → subst ((+ 2) ∣_)
       (sym (minus-0 ((Q /ʸ j) (α , s))))
       (NoVar-front j Q noQ (α , inside ∷ s) here) }) x g)

  sum/ : ∀ x g → eval ((μ y[ j ] +ᴾ Q) /ʸ j) x g ≡
                 1ℤ + eval (Q /ʸ j) x g
  sum/ x g = trans (eval-+ᴾ (μ y[ j ] /ʸ j) (Q /ʸ j) x g)
                   (cong (λ t → t + eval (Q /ʸ j) x g) (μ/ x g))

  odd-ish : ∀ x g → (+ 2) ∣ (eval (f /ʸ j) x g - 1ℤ)
  odd-ish x g = subst ((+ 2) ∣_) (shape a q)
    (∣m∣n⇒∣m+n (subst ((+ 2) ∣_) (cong (λ t → a - t) (sum/ x g))
                (eval-≈ {d = + 2} (f /ʸ j) ((μ y[ j ] +ᴾ Q) /ʸ j)
                  (λ { (α , s) → f≈ (α , insertAt s j inside) }) x g))
               (Q/even x g))
    where
    a q : ℤ
    a = eval (f /ʸ j) x g
    q = eval (Q /ʸ j) x g

    shape : ∀ a q → (a - (1ℤ + q)) + q ≡ a - 1ℤ
    shape = solve 2 (λ a q → (a :- (con 1ℤ :+ q)) :+ q := a :- con 1ℤ) refl


------------------------------------------------------------------------
-- The step

-- The value y_j must take for wire w to read x_w: x_w ⊕ Q, Q = f_w ∖ʸ j,
-- lifted to a polynomial taking that bit as its value.

solution : PathSum n k (suc m) → Fin n → Fin (suc m) → Poly n m
solution ξ w j = liftᴮ (μ x[ w ] +ᴾ (out ξ w ∖ʸ j))

-- Substitute it for y_j in the phase and in every other output, and
-- read x_w on wire w.

restrictᴾ : PathSum n k (suc m) → Fin n → Fin (suc m) → PathSum n k m
restrictᴾ ξ w j =
  ⟨ substAt j (phase ξ) (solution ξ w j)
  , (λ v → if ⌊ v Fin.≟ w ⌋ then μ x[ w ]
           else substAt j (out ξ v) (solution ξ w j)) ⟩

-- Wire w reads its input variable.

restrictᴾ-out-w : (ξ : PathSum n k (suc m)) (w : Fin n) (j : Fin (suc m)) →
                  out (restrictᴾ ξ w j) w ≡ μ x[ w ]
restrictᴾ-out-w ξ w j = by (w Fin.≟ w)
  where
  by : (d : Dec (w ≡ w)) →
       (if ⌊ d ⌋ then μ x[ w ] else substAt j (out ξ w) (solution ξ w j)) ≡
       μ x[ w ]
  by (yes _) = refl
  by (no ¬p) = contradiction refl ¬p

module _ {n k m : ℕ} (ξ : PathSum n k (suc m)) (w : Fin n)
         (j : Fin (suc m)) (piv : Pivot ξ w j) where

  private
    f : Poly n (suc m)
    f = out ξ w

    B : Poly n m
    B = f ∖ʸ j

    S : Poly n m
    S = solution ξ w j

    keepᴾ : Assign n → Assign m → Bool
    keepᴾ x g = odd (eval (μ x[ w ] +ᴾ B) x g)

    eval-S : ∀ x g → eval S x g ≡ [ keepᴾ x g ]ᶻ
    eval-S x g = eval-liftᴮ (μ x[ w ] +ᴾ B) x g

    keep-val : ∀ x g → keepᴾ x g ≡ x w xor odd (eval B x g)
    keep-val x g = trans (cong odd (eval-+ᴾ (μ x[ w ]) B x g))
      (trans (odd-+ (eval (μ x[ w ]) x g) (eval B x g))
             (cong (λ b → b xor odd (eval B x g))
                   (trans (cong odd (eval-μᴾ x[ w ] x g)) (odd-[] (x w)))))

    A-odd : ∀ x g → odd (eval (f /ʸ j) x g) ≡ true
    A-odd x g = trans
      (odd-cong (eval (f /ʸ j) x g) 1ℤ
        (subst ((+ 2) ∣_)
               (cong (λ t → eval (f /ʸ j) x g - t) (eval-κ 1ℤ x g))
               (eval-≈ {d = + 2} (f /ʸ j) (κ 1ℤ) piv x g)))
      refl

    -- Along y_j = b the pivot's wire reads Q ⊕ b.

    out-at : ∀ x g b → outBit ξ x (insertᵃ j b g) w ≡ odd (eval B x g) xor b
    out-at x g b = trans (cong odd (eval-insertᵃ j f x g b))
      (trans (odd-+ (eval B x g) ([ b ]ᶻ * eval (f /ʸ j) x g))
             (cong (λ c → odd (eval B x g) xor c)
                   (odd-bit* b (eval (f /ʸ j) x g) (A-odd x g))))

    out-keep : ∀ x g → outBit ξ x (insertᵃ j (keepᴾ x g) g) w ≡ x w
    out-keep x g = trans (out-at x g (keepᴾ x g))
      (trans (cong (λ c → odd (eval B x g) xor c) (keep-val x g))
             (xor-back (odd (eval B x g)) (x w)))

    out-miss : ∀ x g →
               outBit ξ x (insertᵃ j (not (keepᴾ x g)) g) w ≡ not (x w)
    out-miss x g = trans (out-at x g (not (keepᴾ x g)))
      (trans (cong (λ c → odd (eval B x g) xor not c) (keep-val x g))
             (xor-miss (odd (eval B x g)) (x w)))

    -- The reduct's outputs, read along the kept path.

    outs-at : ∀ x g v (d : Dec (v ≡ w)) →
              odd (eval (if ⌊ d ⌋ then μ x[ w ] else substAt j (out ξ v) S)
                        x g) ≡
              outBit ξ x (insertᵃ j (keepᴾ x g) g) v
    outs-at x g v (yes refl) =
      trans (cong odd (eval-μᴾ x[ w ] x g))
            (trans (odd-[] (x w)) (sym (out-keep x g)))
    outs-at x g v (no _) =
      cong odd (eval-substAt j (out ξ v) S x g (keepᴾ x g) (eval-S x g))

    phaseᴾ : ∀ x g →
             pow M ∣ (eval (substAt j (phase ξ) S) x g -
                      eval (phase ξ) x (insertᵃ j (keepᴾ x g) g))
    phaseᴾ x g = subst (pow M ∣_)
      (sym (trans (cong (λ t → t - eval (phase ξ) x (insertᵃ j (keepᴾ x g) g))
                        (eval-substAt j (phase ξ) S x g (keepᴾ x g) (eval-S x g)))
                  (+-inverseʳ (eval (phase ξ) x (insertᵃ j (keepᴾ x g) g)))))
      i∣0

  -- The substitution is a restriction step.

  restrictᴾ-step : Restricts ξ w j (restrictᴾ ξ w j)
  restrictᴾ-step = record
    { keep   = keepᴾ
    ; miss   = out-miss
    ; outs   = λ x g v → outs-at x g v (v Fin.≟ w)
    ; solves = λ x g → trans (outs-at x g w (w Fin.≟ w)) (out-keep x g)
    ; phase≡ = phaseᴾ
    }

  restrictᴾ-↝ : ξ ↝ restrictᴾ ξ w j
  restrictᴾ-↝ = step w j restrictᴾ-step

  -- The solution, read along the paths of the reduct, is x_w ⊕ Q.

  solution-value : ∀ x g → eval S x g ≡ [ x w xor odd (eval B x g) ]ᶻ
  solution-value x g = trans (eval-S x g) (cong [_]ᶻ (keep-val x g))


------------------------------------------------------------------------
-- The reduct is unique

module _ {n k m : ℕ} {ξ : PathSum n k (suc m)} {w : Fin n}
         {j : Fin (suc m)} {ρ ρ′ : PathSum n k m}
         (r : Restricts ξ w j ρ) (r′ : Restricts ξ w j ρ′) where

  private
    module R  = Restricts r
    module R′ = Restricts r′

    -- The kept path is the one along which wire w reads x_w.

    reads′ : ∀ x g → outBit ξ x (insertᵃ j (R′.keep x g) g) w ≡ x w
    reads′ x g = trans (sym (R′.outs x g w)) (R′.solves x g)

  keep-unique : ∀ x g → R.keep x g ≡ R′.keep x g
  keep-unique x g = by (R.keep x g Bool.≟ R′.keep x g)
    where
    by : Dec (R.keep x g ≡ R′.keep x g) → R.keep x g ≡ R′.keep x g
    by (yes e) = e
    by (no ne) = contradiction
      (sym (trans (sym (reads′ x g))
             (trans (cong (λ b → outBit ξ x (insertᵃ j b g) w)
                          (≢⇒not (R.keep x g) (λ e → ne (sym e))))
                    (R.miss x g))))
      (not-≢ (x w))

  -- Phases agree modulo 1 and outputs modulo 2, coefficient by
  -- coefficient.

  restricts-unique : phase ρ ≈[ pow M ] phase ρ′ ×
                     (∀ v → out ρ v ≈[ + 2 ] out ρ′ v)
  restricts-unique =
    ≈-from-values {c = pow M} (phase ρ) (phase ρ′) (λ x g →
      subst (pow M ∣_) (shape (eval (phase ρ) x g) (eval (phase ρ′) x g)
                              (eval (phase ξ) x (insertᵃ j (R.keep x g) g)))
        (∣m∣n⇒∣m-n (R.phase≡ x g)
          (subst (λ b → pow M ∣ (eval (phase ρ′) x g -
                                 eval (phase ξ) x (insertᵃ j b g)))
                 (sym (keep-unique x g)) (R′.phase≡ x g)))) ,
    (λ v → ≈-from-values {c = + 2} (out ρ v) (out ρ′ v) (λ x g →
      odd-≡ (eval (out ρ v) x g) (eval (out ρ′ v) x g)
        (trans (R.outs x g v)
          (trans (cong (λ b → outBit ξ x (insertᵃ j b g) v) (keep-unique x g))
                 (sym (R′.outs x g v))))))
    where
    shape : ∀ a b e → (a - e) - (b - e) ≡ a - b
    shape = solve 3 (λ a b e → (a :- e) :- (b :- e) := a :- b) refl

-- So a restriction step checked semantically has, coefficient by
-- coefficient, the paper's substitution as its reduct.

restricts≈restrictᴾ : {ξ : PathSum n k (suc m)} {w : Fin n}
                      {j : Fin (suc m)} {ρ : PathSum n k m} →
                      Pivot ξ w j → Restricts ξ w j ρ →
                      phase ρ ≈[ pow M ] phase (restrictᴾ ξ w j) ×
                      (∀ v → out ρ v ≈[ + 2 ] out (restrictᴾ ξ w j) v)
restricts≈restrictᴾ {ξ = ξ} {w} {j} piv r =
  restricts-unique r (restrictᴾ-step ξ w j piv)


------------------------------------------------------------------------
-- The procedure

-- No output has a pivot left.

NoPivot : PathSum n k m → Set
NoPivot {m = zero}  ρ = ⊤
NoPivot {m = suc m} ρ = ∀ w j → ¬ Pivot ρ w j

record Restriction {n k m : ℕ} (ξ : PathSum n k m) : Set where
  field
    left  : ℕ
    final : PathSum n k left
    chain : ξ ↝* final
    stuck : NoPivot final

find? : (ξ : PathSum n k (suc m)) →
        (∃ λ w → ∃ λ j → Pivot ξ w j) ⊎ (∀ w j → ¬ Pivot ξ w j)
find? ξ with any? (λ w → any? (λ j → pivot? ξ w j))
... | yes found = inj₁ found
... | no  none  = inj₂ (λ w j p → none (w , j , p))

-- Substitute while some output has a pivot.

restriction : (ξ : PathSum n k m) → Restriction ξ
restriction {m = zero}  ξ = record
  { left = zero ; final = ξ ; chain = εʳ ; stuck = tt }
restriction {n} {k} {suc m} ξ = by (find? ξ)
  where
  by : (∃ λ w → ∃ λ j → Pivot ξ w j) ⊎ (∀ w j → ¬ Pivot ξ w j) →
       Restriction ξ
  by (inj₁ (w , j , p)) = record
    { left  = Restriction.left rest
    ; final = Restriction.final rest
    ; chain = restrictᴾ-↝ ξ w j p ◅ʳ Restriction.chain rest
    ; stuck = Restriction.stuck rest
    }
    where
    rest : Restriction (restrictᴾ ξ w j)
    rest = restriction (restrictᴾ ξ w j)
  by (inj₂ none) = record
    { left = suc m ; final = ξ ; chain = εʳ ; stuck = none }


------------------------------------------------------------------------
-- Outputs free of path variables

-- An output congruent to x_w modulo 2 reads x_w on every path.

≈μ⇒Solved : (ρ : PathSum n k m) (w : Fin n) →
            out ρ w ≈[ + 2 ] μ x[ w ] → Solved ρ w
≈μ⇒Solved ρ w h x g = trans
  (odd-cong (eval (out ρ w) x g) (eval (μ x[ w ]) x g)
            (eval-≈ {d = + 2} (out ρ w) (μ x[ w ]) h x g))
  (trans (cong odd (eval-μᴾ x[ w ] x g)) (odd-[] (x w)))

-- An output free of path variables is x_w modulo 2, or it reads ¬x_w
-- on every path from some input.

settle-or-refute : (ρ : PathSum n k m) (w : Fin n) →
                   (∀ j → NoVar (+ 2) y[ j ] (out ρ w)) →
                   out ρ w ≈[ + 2 ] μ x[ w ] ⊎
                   (∃ λ (x : Assign n) → ∀ y → outBit ρ x y w ≡ not (x w))
settle-or-refute {n} {m = m} ρ w noy = by (even-or-odd-input D noD)
  where
  D : Poly n m
  D = out ρ w -ᴾ μ x[ w ]

  noD : ∀ j → NoVar (+ 2) y[ j ] D
  noD j γ y∈γ = subst ((+ 2) ∣_)
    (cong (λ t → out ρ w γ - t)
          (sym (Absent-μ x[ w ] y[ j ] ∉⊥ γ y∈γ)))
    (subst ((+ 2) ∣_) (sym (minus-0 (out ρ w γ))) (noy j γ y∈γ))

  by : D ≈[ + 2 ] 0ᴾ ⊎
       ∃ (λ (x : Assign n) → ∀ (y : Assign m) → ¬ ((+ 2) ∣ eval D x y)) →
       out ρ w ≈[ + 2 ] μ x[ w ] ⊎
       (∃ λ (x : Assign n) → ∀ y → outBit ρ x y w ≡ not (x w))
  by (inj₁ D≈0)      = inj₁ (λ γ →
    subst ((+ 2) ∣_) (minus-0 (D γ)) (D≈0 γ))
  by (inj₂ (x , isOdd)) = inj₂ (x , λ y → ≢⇒not (x w) (λ e →
    isOdd y (subst ((+ 2) ∣_)
      (sym (trans (eval-−ᴾ (out ρ w) (μ x[ w ]) x y)
                  (cong (λ t → eval (out ρ w) x y - t) (eval-μᴾ x[ w ] x y))))
      (odd-≡ (eval (out ρ w) x y) [ x w ]ᶻ
             (trans e (sym (odd-[] (x w))))))))

-- Hence an output left free of path variables that is not x_w refutes
-- the identity, with no well-formedness.

restriction-refutes-syntactic :
  (ξ : PathSum n k m) (ρ : PathSum n k′ m′) → ξ ⇝* ρ → (w : Fin n) →
  (∀ j → NoVar (+ 2) y[ j ] (out ρ w)) → ¬ (out ρ w ≈[ + 2 ] μ x[ w ]) →
  ¬ (ξ ≋ idPS)
restriction-refutes-syntactic ξ ρ steps w noy ne = by (settle-or-refute ρ w noy)
  where
  by : out ρ w ≈[ + 2 ] μ x[ w ] ⊎
       (∃ λ x → ∀ y → outBit ρ x y w ≡ not (x w)) → ¬ (ξ ≋ idPS)
  by (inj₁ eq)         = contradiction eq ne
  by (inj₂ (x , miss)) = restriction-refutes ξ ρ steps w x miss
