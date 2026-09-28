------------------------------------------------------------------------
-- Presentations of groups
--
-- Following the values of a path-sum through [HH] and [Elim]
--
-- The rules of figure 2 (Amy, QPL 2018) are stated coefficient by
-- coefficient, but a path-sum whose polynomials are built by
-- composition (definition 2.6, PathSum.Compose) -- the hidden shift
-- circuit is five of them -- has coefficients that do not compute.
-- What is known of it is its values: its phase modulo 1 and its
-- outputs modulo 2 at every assignment to the input and path
-- variables.  This module follows those values through [HH] and
-- [Elim] at any path variable (PathSum.Full's _⟶ᶠ_), and obtains the
-- rules' premises from them by Möbius inversion (PathSum.Mobius), so
-- that a chain of rules can be built for a path-sum known only by its
-- values.
--
-- Tracks ξ F G says that the phase of ξ is ½F modulo 1 and its
-- outputs are G modulo 2, at every point; F and G are Boolean
-- functions of the path variables (the phases met here are halves: a
-- Hadamard contributes ½x·y, an oracle ½f).  Then:
--
-- * [HH] at y_j with y_i ← Q applies when the derivative of F in y_j --
--   F with y_j set, xor F with y_j clear -- is y_i ⊕ q, q being the
--   value of Q, and G does not depend on y_j (hh-premise, out-premise).
--   The quotient of the phase by y_j is its value at y_j = 1 less its
--   value at y_j = 0, which is ½(y_i + Q) modulo 1 exactly when the
--   two parities differ by y_i ⊕ q.  The reduct has F and G read at
--   y_j = 0 and y_i = q (hh-tracks).
-- * [Elim] at y_j keeps F and G read at y_j = 0 (elim-tracks).  After
--   an [HH] its premises need no values: the substituted variable is
--   absent from the reduct, coefficient by coefficient
--   (PathSum.Polynomial.Substitution.substᴾ-absent), so its quotient is
--   0 and it is absent from the outputs.  [HH] at y_j followed by
--   [Elim] of y_i is therefore a two-step chain whose only premises
--   are the [HH]'s (hh-elim).
--
-- Nothing here is about the hidden shift; PathSum.HiddenShift.Exists
-- uses it to reduce the circuit on |0⟩ to no path variables.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Track (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (inside)
open import Data.Integer.Base using (ℤ; 0ℤ; -_; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣n⇒∣m*n)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Vec.Base using (_∷_; insertAt; here)
open import Data.Vec.Properties using (insertAt-lookup; lookup⇒[]=)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using
  (PathSum; phase; out; y₀; head-part; tail-part)
open import PathSum.Cyclotomic M₀ using (extend)
open import PathSum.Denotation M₀ using (Assign; eval-true; eval-false)
open import PathSum.HiddenShift.Sign M₀ using (odd-≡)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Polynomial using
  (Poly; y[_]; 0ᴾ; μ; _+ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; IsBit-if; ≈-from-values)
open import PathSum.Polynomial.Product using (eval-μᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-·ᴾ; i∣0)
open import PathSum.Polynomial.Substitution using
  (Absent; Absent⇒NoVar; substᴾ; substᴾ-absent; eval-substᴾ-≔)
open import PathSum.Reorder using
  (insertᵃ; front; frontᴾ; _/ʸ_; eval-front)

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
-- point.

record Tracks (ξ : PathSum n k m) (F : Assign m → Bool)
              (G : Fin n → Assign m → Bool) : Set where
  field
    phase-at : ∀ x y → pow M ∣ (eval (phase ξ) x y - ½ * [ F y ]ᶻ)
    out-at   : ∀ w x y → odd (eval (out ξ w) x y) ≡ G w y

open Tracks public


------------------------------------------------------------------------
-- Values at a renumbered variable

-- The quotient by the head variable is the value with it set less the
-- value with it clear.

eval-head : (R : Poly n (suc m)) (x : Assign n) (y : Assign m) →
            eval (head-part R) x y ≡
            eval R x (extend true y) - eval R x (extend false y)
eval-head R x y = sym (trans
  (cong₂ _-_ (eval-true R x y) (eval-false R x y))
  (shape (eval (head-part R) x y) (eval (tail-part R) x y)))
  where
  shape : ∀ h t → (h + t) - t ≡ h
  shape = solve 2 (λ h t → (h :+ t) :- t := h) refl

-- With y_j moved to the front and set to b, a polynomial is read with
-- y_j = b.

eval-at : (j : Fin (suc m)) (P : Poly n (suc m)) (b : Bool)
          (x : Assign n) (y : Assign m) →
          eval (frontᴾ j P) x (extend b y) ≡ eval P x (insertᵃ j b y)
eval-at j P b x y = eval-front j P x (extend b y)

-- So the quotient by y_j is a difference of two values, and the part
-- free of y_j is the value at y_j = 0.

eval-/ʸ : (P : Poly n (suc m)) (j : Fin (suc m)) (x : Assign n)
          (y : Assign m) →
          eval (P /ʸ j) x y ≡
          eval P x (insertᵃ j true y) - eval P x (insertᵃ j false y)
eval-/ʸ P j x y = trans (eval-head (frontᴾ j P) x y)
  (cong₂ _-_ (eval-at j P true x y) (eval-at j P false x y))

eval-∖ʸ : (P : Poly n (suc m)) (j : Fin (suc m)) (x : Assign n)
          (y : Assign m) →
          eval (tail-part (frontᴾ j P)) x y ≡ eval P x (insertᵃ j false y)
eval-∖ʸ P j x y =
  trans (sym (eval-false (frontᴾ j P) x y)) (eval-at j P false x y)


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
-- ½(y_i + Q) modulo 1 when the derivative of F in y_j is y_i ⊕ q.

hh-premise : (ξ : PathSum n k (suc m)) {F : Assign (suc m) → Bool}
             {G : Fin n → Assign (suc m) → Bool} → Tracks ξ F G →
             (j : Fin (suc m)) (i : Fin m) (Q : Poly n m)
             (q : Assign m → Bool) → (∀ x y → eval Q x y ≡ [ q y ]ᶻ) →
             (∀ y → F (insertᵃ j true y) xor F (insertᵃ j false y) ≡
                    y i xor q y) →
             (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))
hh-premise ξ {F} tr j i Q q hq dF =
  ≈-from-values (phase ξ /ʸ j) (½ ·ᴾ (μ y[ i ] +ᴾ Q)) value
  where
  value : ∀ x y → pow M ∣ (eval (phase ξ /ʸ j) x y -
                           eval (½ ·ᴾ (μ y[ i ] +ᴾ Q)) x y)
  value x y = subst (pow M ∣_)
    (sym (trans (cong₂ _-_ (eval-/ʸ (phase ξ) j x y) rhs)
                (shape a b ½ A B c d)))
    (∣m∣n⇒∣m+n
      (∣m∣n⇒∣m-n (phase-at tr x (insertᵃ j true y))
                 (phase-at tr x (insertᵃ j false y)))
      (half-even ((A - B) - (c + d))
        (bits-even (F (insertᵃ j true y)) (F (insertᵃ j false y)) (y i)
                   (q y) (dF y))))
    where
    a b A B c d : ℤ
    a = eval (phase ξ) x (insertᵃ j true y)
    b = eval (phase ξ) x (insertᵃ j false y)
    A = [ F (insertᵃ j true y) ]ᶻ
    B = [ F (insertᵃ j false y) ]ᶻ
    c = [ y i ]ᶻ
    d = [ q y ]ᶻ

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
-- it: the quotient of an output by y_j has even values.

out-premise : (ξ : PathSum n k (suc m)) {F : Assign (suc m) → Bool}
              {G : Fin n → Assign (suc m) → Bool} → Tracks ξ F G →
              (j : Fin (suc m)) →
              (∀ w y → G w (insertᵃ j true y) ≡ G w (insertᵃ j false y)) →
              ∀ w → NoVar (+ 2) y₀ (out (front j ξ) w)
out-premise ξ tr j dG w (α , _ ∷ s) here =
  values⇒coefficientsᵐ (+ 2) (out ξ w /ʸ j) value (α , s)
  where
  value : ∀ x y → (+ 2) ∣ eval (out ξ w /ʸ j) x y
  value x y = subst ((+ 2) ∣_) (sym (eval-/ʸ (out ξ w) j x y))
    (odd-≡ (eval (out ξ w) x (insertᵃ j true y))
           (eval (out ξ w) x (insertᵃ j false y))
           (trans (out-at tr w x (insertᵃ j true y))
             (trans (dG w y) (sym (out-at tr w x (insertᵃ j false y))))))


------------------------------------------------------------------------
-- The values of the reducts

-- [HH] at y_j with y_i ← Q reads F and G at y_j = 0, y_i = q.

hh-tracks : (ξ : PathSum n k (suc m)) {F : Assign (suc m) → Bool}
            {G : Fin n → Assign (suc m) → Bool} → Tracks ξ F G →
            (j : Fin (suc m)) (i : Fin m) (Q : Poly n m)
            (q : Assign m → Bool) → (∀ x y → eval Q x y ≡ [ q y ]ᶻ) →
            Tracks (hhᴳ-reduct (front j ξ) i Q)
                   (λ y → F (insertᵃ j false (y [ i ≔ q y ])))
                   (λ w y → G w (insertᵃ j false (y [ i ≔ q y ])))
hh-tracks ξ {F} {G} tr j i Q q hq = record
  { phase-at = λ x y →
      subst (λ t → pow M ∣ (t - ½ * [ F (insertᵃ j false (y [ i ≔ q y ])) ]ᶻ))
            (sym (value (phase ξ) x y))
            (phase-at tr x (insertᵃ j false (y [ i ≔ q y ])))
  ; out-at = λ w x y →
      trans (cong odd (value (out ξ w) x y))
            (out-at tr w x (insertᵃ j false (y [ i ≔ q y ])))
  }
  where
  value : ∀ P x y → eval (substᴾ (tail-part (frontᴾ j P)) y[ i ] Q) x y ≡
                    eval P x (insertᵃ j false (y [ i ≔ q y ]))
  value P x y = trans
    (eval-substᴾ-≔ (tail-part (frontᴾ j P)) i Q x y (q y) (sym (hq x y)))
    (eval-∖ʸ P j x (y [ i ≔ q y ]))

-- [Elim] at y_j reads them at y_j = 0.

elim-tracks : (ξ : PathSum n (suc (suc k)) (suc m))
              {F : Assign (suc m) → Bool}
              {G : Fin n → Assign (suc m) → Bool} → Tracks ξ F G →
              (j : Fin (suc m)) →
              Tracks (elim-reduct (front j ξ))
                     (λ y → F (insertᵃ j false y))
                     (λ w y → G w (insertᵃ j false y))
elim-tracks ξ {F} tr j = record
  { phase-at = λ x y →
      subst (λ t → pow M ∣ (t - ½ * [ F (insertᵃ j false y) ]ᶻ))
            (sym (eval-∖ʸ (phase ξ) j x y))
            (phase-at tr x (insertᵃ j false y))
  ; out-at = λ w x y →
      trans (cong odd (eval-∖ʸ (out ξ w) j x y))
            (out-at tr w x (insertᵃ j false y))
  }


------------------------------------------------------------------------
-- [HH] followed by [Elim] of the substituted variable

-- A variable absent from a polynomial has quotient 0.

absent-/ʸ : ∀ {c} (P : Poly n (suc m)) (i : Fin (suc m)) →
            Absent y[ i ] P → (P /ʸ i) ≈[ c ] 0ᴾ
absent-/ʸ {c = c} P i abs (α , s) =
  subst (λ t → c ∣ (t - 0ℤ))
        (sym (abs (α , insertAt s i inside)
                  (lookup⇒[]= i (insertAt s i inside)
                              (insertAt-lookup s i inside))))
        i∣0

-- The two steps, and the values of the result: F and G read at y_j = 0
-- and y_i = q, the other variables in their order.

hh-elim : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
          {F : Assign (suc (suc m)) → Bool}
          {G : Fin n → Assign (suc (suc m)) → Bool} → Tracks ξ F G →
          (j : Fin (suc (suc m))) (i : Fin (suc m)) (Q : Poly n (suc m))
          (q : Assign (suc m) → Bool) →
          (∀ x y → eval Q x y ≡ [ q y ]ᶻ) → Absent y[ i ] Q →
          (∀ y → F (insertᵃ j true y) xor F (insertᵃ j false y) ≡
                 y i xor q y) →
          (∀ w y → G w (insertᵃ j true y) ≡ G w (insertᵃ j false y)) →
          (ξ ⟶ᶠ* elim-reduct (front i (hhᴳ-reduct (front j ξ) i Q))) ×
          Tracks (elim-reduct (front i (hhᴳ-reduct (front j ξ) i Q)))
            (λ y → F (insertᵃ j false (insertᵃ i false y
                                         [ i ≔ q (insertᵃ i false y) ])))
            (λ w y → G w (insertᵃ j false (insertᵃ i false y
                                             [ i ≔ q (insertᵃ i false y) ])))
hh-elim ξ tr j i Q q hq absQ dF dG =
  (step₁ ◅ᶠ step₂ ◅ᶠ εᶠ) , elim-tracks ζ (hh-tracks ξ tr j i Q q hq) i
  where
  ζ : PathSum _ _ _
  ζ = hhᴳ-reduct (front j ξ) i Q

  bQ : BoolValued Q
  bQ x y = subst IsBit (sym (hq x y)) (IsBit-if (q y))

  step₁ : ξ ⟶ᶠ ζ
  step₁ = at j (plain (hhᴳ (front j ξ) i Q bQ absQ
                           (hh-premise ξ tr j i Q q hq dF)
                           (out-premise ξ tr j dG)))

  step₂ : ζ ⟶ᶠ elim-reduct (front i ζ)
  step₂ = elimAtᶠ ζ i
    (absent-/ʸ (phase ζ) i
      (substᴾ-absent (tail-part (frontᴾ j (phase ξ))) y[ i ] Q absQ))
    (λ w → Absent⇒NoVar {v = y[ i ]}
      (substᴾ-absent (tail-part (frontᴾ j (out ξ w))) y[ i ] Q absQ))
