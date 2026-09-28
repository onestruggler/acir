------------------------------------------------------------------------
-- Presentations of groups
--
-- Following the values of a path-sum through [HH] and [Elim], when
-- they depend on the inputs
--
-- PathSum.HiddenShift.Track follows a path-sum known only by its values
-- through the rules [HH] and [Elim] of figure 2 (Amy, QPL 2018): the
-- phase is ½F modulo 1 and the outputs are G modulo 2, F and G Boolean
-- functions of the path variables.  That suffices for the hidden shift
-- circuit on |0⟩, whose values do not depend on the input.  The circuit
-- of figure 3(b) holds the shift in a register of its own, whose
-- inputs stay symbolic: its phase along a path depends on them (the
-- oracle reads the data register shifted by the shift register), and
-- so do the quotients of its rules (the variable d_i is replaced by
-- a_i ⊕ s_i, s_i an input variable).  This module is Track with F, G
-- and the quotient's values q depending on the input x as well
-- (Tracksˣ): the premises of [HH] are the same statements at every x
-- (hh-premiseˣ, out-premiseˣ), proved by the same Möbius inversion,
-- which ranges over the inputs and the path variables alike; the
-- reducts read F and G at y_j = 0 and y_i = q x y (hh-tracksˣ,
-- elim-tracksˣ); and [HH] at y_j followed by [Elim] of y_i is a
-- two-step chain whose only premises are the [HH]'s (hh-elimˣ).  With
-- F, G and q constant in x it is Track's statement.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.TrackX (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; -_; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣n⇒∣m*n)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Vec.Base using (_∷_; here)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using (PathSum; phase; out; y₀; tail-part)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Sign M₀ using (odd-≡)
open import PathSum.HiddenShift.Track M₀ using (eval-/ʸ; eval-∖ʸ; absent-/ʸ)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Polynomial using
  (Poly; y[_]; μ; _+ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; IsBit-if; ≈-from-values)
open import PathSum.Polynomial.Product using (eval-μᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-·ᴾ)
open import PathSum.Polynomial.Substitution using
  (Absent; Absent⇒NoVar; substᴾ; substᴾ-absent; eval-substᴾ-≔)
open import PathSum.Reorder using (insertᵃ; front; frontᴾ; _/ʸ_)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (at; plain)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_; elimAtᶠ)
open import PathSum.Full.Canonical M using (pow∣½·2)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½; elim-reduct)
open import PathSum.Reduction.General M using (hhᴳ; hhᴳ-reduct)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- A path-sum known by its values

-- The phase is ½F modulo 1 and the outputs are G modulo 2, at every
-- input and every path.

record Tracksˣ (ξ : PathSum n k m) (F : Assign n → Assign m → Bool)
               (G : Fin n → Assign n → Assign m → Bool) : Set where
  field
    phase-atˣ : ∀ x y → pow M ∣ (eval (phase ξ) x y - ½ * [ F x y ]ᶻ)
    out-atˣ   : ∀ w x y → odd (eval (out ξ w) x y) ≡ G w x y

open Tracksˣ public


------------------------------------------------------------------------
-- The premises of [HH], from values

private
  -- Half of an even number is a multiple of 2^M.

  half-even : ∀ t → (+ 2) ∣ t → pow M ∣ (½ * t)
  half-even t (divides r eq) =
    subst (pow M ∣_) (sym (trans (cong (½ *_) eq) (swap ½ r)))
          (∣n⇒∣m*n r pow∣½·2)
    where
    swap : ∀ h r → h * (r * (+ 2)) ≡ r * (h * (+ 2))
    swap = solve 2 (λ h r → h :* (r :* con (+ 2)) := r :* (h :* con (+ 2)))
                   refl

  -- Four bits whose sums modulo 2 agree differ by an even number.

  bits-even : ∀ a b c d → a xor b ≡ c xor d →
              (+ 2) ∣ (([ a ]ᶻ - [ b ]ᶻ) - ([ c ]ᶻ + [ d ]ᶻ))
  bits-even false false false false _ = divides 0ℤ refl
  bits-even false false true  true  _ = divides (- (+ 1)) refl
  bits-even false true  true  false _ = divides (- (+ 1)) refl
  bits-even false true  false true  _ = divides (- (+ 1)) refl
  bits-even true  false true  false _ = divides 0ℤ refl
  bits-even true  false false true  _ = divides 0ℤ refl
  bits-even true  true  false false _ = divides 0ℤ refl
  bits-even true  true  true  true  _ = divides (- (+ 1)) refl
  bits-even false false false true  ()
  bits-even false false true  false ()
  bits-even false true  false false ()
  bits-even false true  true  true  ()
  bits-even true  false false false ()
  bits-even true  false true  true  ()
  bits-even true  true  false true  ()
  bits-even true  true  true  false ()

-- [HH] at y_j with y_i ← Q: the quotient of the phase by y_j is
-- ½(y_i + Q) modulo 1 when, at every input, the derivative of F in y_j
-- is y_i ⊕ q.

hh-premiseˣ : (ξ : PathSum n k (suc m)) {F : Assign n → Assign (suc m) → Bool}
              {G : Fin n → Assign n → Assign (suc m) → Bool} →
              Tracksˣ ξ F G →
              (j : Fin (suc m)) (i : Fin m) (Q : Poly n m)
              (q : Assign n → Assign m → Bool) →
              (∀ x y → eval Q x y ≡ [ q x y ]ᶻ) →
              (∀ x y → F x (insertᵃ j true y) xor F x (insertᵃ j false y) ≡
                       y i xor q x y) →
              (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))
hh-premiseˣ ξ {F} tr j i Q q hq dF =
  ≈-from-values (phase ξ /ʸ j) (½ ·ᴾ (μ y[ i ] +ᴾ Q)) value
  where
  value : ∀ x y → pow M ∣ (eval (phase ξ /ʸ j) x y -
                           eval (½ ·ᴾ (μ y[ i ] +ᴾ Q)) x y)
  value x y = subst (pow M ∣_)
    (sym (trans (cong₂ _-_ (eval-/ʸ (phase ξ) j x y) rhs)
                (shape a b ½ A B c d)))
    (∣m∣n⇒∣m+n
      (∣m∣n⇒∣m-n (phase-atˣ tr x (insertᵃ j true y))
                 (phase-atˣ tr x (insertᵃ j false y)))
      (half-even ((A - B) - (c + d))
        (bits-even (F x (insertᵃ j true y)) (F x (insertᵃ j false y)) (y i)
                   (q x y) (dF x y))))
    where
    a b A B c d : ℤ
    a = eval (phase ξ) x (insertᵃ j true y)
    b = eval (phase ξ) x (insertᵃ j false y)
    A = [ F x (insertᵃ j true y) ]ᶻ
    B = [ F x (insertᵃ j false y) ]ᶻ
    c = [ y i ]ᶻ
    d = [ q x y ]ᶻ

    rhs : eval (½ ·ᴾ (μ y[ i ] +ᴾ Q)) x y ≡ ½ * (c + d)
    rhs = trans (eval-·ᴾ ½ (μ y[ i ] +ᴾ Q) x y)
      (cong (½ *_) (trans (eval-+ᴾ (μ y[ i ]) Q x y)
                          (cong₂ _+_ (eval-μᴾ y[ i ] x y) (hq x y))))

    shape : ∀ a b h A B c d →
            (a - b) - h * (c + d) ≡
            ((a - h * A) - (b - h * B)) + h * ((A - B) - (c + d))
    shape = solve 7 (λ a b h A B c d →
      (a :- b) :- h :* (c :+ d) :=
      ((a :- h :* A) :- (b :- h :* B)) :+ h :* ((A :- B) :- (c :+ d))) refl

-- y_j is absent from the outputs, modulo 2, when G does not depend on
-- it at any input.

out-premiseˣ : (ξ : PathSum n k (suc m))
               {F : Assign n → Assign (suc m) → Bool}
               {G : Fin n → Assign n → Assign (suc m) → Bool} →
               Tracksˣ ξ F G → (j : Fin (suc m)) →
               (∀ w x y → G w x (insertᵃ j true y) ≡
                          G w x (insertᵃ j false y)) →
               ∀ w → NoVar (+ 2) y₀ (out (front j ξ) w)
out-premiseˣ ξ tr j dG w (α , _ ∷ s) here =
  values⇒coefficientsᵐ (+ 2) (out ξ w /ʸ j) value (α , s)
  where
  value : ∀ x y → (+ 2) ∣ eval (out ξ w /ʸ j) x y
  value x y = subst ((+ 2) ∣_) (sym (eval-/ʸ (out ξ w) j x y))
    (odd-≡ (eval (out ξ w) x (insertᵃ j true y))
           (eval (out ξ w) x (insertᵃ j false y))
           (trans (out-atˣ tr w x (insertᵃ j true y))
             (trans (dG w x y) (sym (out-atˣ tr w x (insertᵃ j false y))))))


------------------------------------------------------------------------
-- The values of the reducts

-- [HH] at y_j with y_i ← Q reads F and G at y_j = 0, y_i = q x y.

hh-tracksˣ : (ξ : PathSum n k (suc m))
             {F : Assign n → Assign (suc m) → Bool}
             {G : Fin n → Assign n → Assign (suc m) → Bool} →
             Tracksˣ ξ F G →
             (j : Fin (suc m)) (i : Fin m) (Q : Poly n m)
             (q : Assign n → Assign m → Bool) →
             (∀ x y → eval Q x y ≡ [ q x y ]ᶻ) →
             Tracksˣ (hhᴳ-reduct (front j ξ) i Q)
                     (λ x y → F x (insertᵃ j false (y [ i ≔ q x y ])))
                     (λ w x y → G w x (insertᵃ j false (y [ i ≔ q x y ])))
hh-tracksˣ ξ {F} {G} tr j i Q q hq = record
  { phase-atˣ = λ x y →
      subst (λ t → pow M ∣
                     (t - ½ * [ F x (insertᵃ j false (y [ i ≔ q x y ])) ]ᶻ))
            (sym (value (phase ξ) x y))
            (phase-atˣ tr x (insertᵃ j false (y [ i ≔ q x y ])))
  ; out-atˣ = λ w x y →
      trans (cong odd (value (out ξ w) x y))
            (out-atˣ tr w x (insertᵃ j false (y [ i ≔ q x y ])))
  }
  where
  value : ∀ P x y → eval (substᴾ (tail-part (frontᴾ j P)) y[ i ] Q) x y ≡
                    eval P x (insertᵃ j false (y [ i ≔ q x y ]))
  value P x y = trans
    (eval-substᴾ-≔ (tail-part (frontᴾ j P)) i Q x y (q x y) (sym (hq x y)))
    (eval-∖ʸ P j x (y [ i ≔ q x y ]))

-- [Elim] at y_j reads them at y_j = 0.

elim-tracksˣ : (ξ : PathSum n (suc (suc k)) (suc m))
               {F : Assign n → Assign (suc m) → Bool}
               {G : Fin n → Assign n → Assign (suc m) → Bool} →
               Tracksˣ ξ F G → (j : Fin (suc m)) →
               Tracksˣ (elim-reduct (front j ξ))
                       (λ x y → F x (insertᵃ j false y))
                       (λ w x y → G w x (insertᵃ j false y))
elim-tracksˣ ξ {F} tr j = record
  { phase-atˣ = λ x y →
      subst (λ t → pow M ∣ (t - ½ * [ F x (insertᵃ j false y) ]ᶻ))
            (sym (eval-∖ʸ (phase ξ) j x y))
            (phase-atˣ tr x (insertᵃ j false y))
  ; out-atˣ = λ w x y →
      trans (cong odd (eval-∖ʸ (out ξ w) j x y))
            (out-atˣ tr w x (insertᵃ j false y))
  }


------------------------------------------------------------------------
-- [HH] followed by [Elim] of the substituted variable

-- The two steps, and the values of the result: F and G read at y_j = 0
-- and y_i = q x y, the other variables in their order.

hh-elimˣ : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
           {F : Assign n → Assign (suc (suc m)) → Bool}
           {G : Fin n → Assign n → Assign (suc (suc m)) → Bool} →
           Tracksˣ ξ F G →
           (j : Fin (suc (suc m))) (i : Fin (suc m)) (Q : Poly n (suc m))
           (q : Assign n → Assign (suc m) → Bool) →
           (∀ x y → eval Q x y ≡ [ q x y ]ᶻ) → Absent y[ i ] Q →
           (∀ x y → F x (insertᵃ j true y) xor F x (insertᵃ j false y) ≡
                    y i xor q x y) →
           (∀ w x y → G w x (insertᵃ j true y) ≡ G w x (insertᵃ j false y)) →
           (ξ ⟶ᶠ* elim-reduct (front i (hhᴳ-reduct (front j ξ) i Q))) ×
           Tracksˣ (elim-reduct (front i (hhᴳ-reduct (front j ξ) i Q)))
             (λ x y → F x (insertᵃ j false (insertᵃ i false y
                                   [ i ≔ q x (insertᵃ i false y) ])))
             (λ w x y → G w x (insertᵃ j false (insertᵃ i false y
                                       [ i ≔ q x (insertᵃ i false y) ])))
hh-elimˣ ξ tr j i Q q hq absQ dF dG =
  (step₁ ◅ᶠ step₂ ◅ᶠ εᶠ) , elim-tracksˣ ζ (hh-tracksˣ ξ tr j i Q q hq) i
  where
  ζ : PathSum _ _ _
  ζ = hhᴳ-reduct (front j ξ) i Q

  bQ : BoolValued Q
  bQ x y = subst IsBit (sym (hq x y)) (IsBit-if (q x y))

  step₁ : ξ ⟶ᶠ ζ
  step₁ = at j (plain (hhᴳ (front j ξ) i Q bQ absQ
                           (hh-premiseˣ ξ tr j i Q q hq dF)
                           (out-premiseˣ ξ tr j dG)))

  step₂ : ζ ⟶ᶠ elim-reduct (front i ζ)
  step₂ = elimAtᶠ ζ i
    (absent-/ʸ (phase ζ) i
      (substᴾ-absent (tail-part (frontᴾ j (phase ξ))) y[ i ] Q absQ))
    (λ w → Absent⇒NoVar {v = y[ i ]}
      (substᴾ-absent (tail-part (frontᴾ j (out ξ w))) y[ i ] Q absQ))
