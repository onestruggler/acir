------------------------------------------------------------------------
-- Presentations of groups
--
-- Substituting an arbitrary polynomial for a variable
--
-- The rules [HH] and [Case] of figure 2 in Amy's "Towards Large-scale
-- Functional Verification of Universal Quantum Circuits" (QPL 2018)
-- replace a path variable by a Boolean-valued quotient Q, written
-- P[y_i ← Q].  PathSum.Polynomial defines that substitution only for
-- the lifting of a Z₂-linear form, liftXor c S.  Here it is defined
-- for any polynomial L: writing P = (P ∖ᵛ v) + v · (P /ᵛ v), with both
-- parts free of v, the result is (P ∖ᵛ v) + (P /ᵛ v) · L, and its
-- coefficients are spelled out exactly as those of `subst`, with L β
-- where `subst` has liftXor c S β.  So the old substitution is the new
-- one at a lifted linear form *by definition* (subst≡substᴾ is refl):
-- a reduct of the linear [HH] is literally a reduct of the general one,
-- and relating the two rules needs no fact about substitution.
--
-- What substitution means is stated through evaluation: eval-substᴾ
-- (the value is that of P ∖ᵛ v plus L's value times that of P /ᵛ v),
-- eval-substᴾ-fixed (where the assignment already gives v the value of
-- L, substituting changes nothing) and eval-substᴾ-≔ (substituting
-- for a path variable is evaluating at the assignment updated there).
-- The paper's side condition "y_i does not appear in Q" is Absent:
-- every coefficient of a monomial containing y_i vanishes exactly, the
-- hypothesis PathSum.Polynomial.Properties.eval-off takes.  It is kept
-- by substitution (substᴾ-absent) and by the ring operations.
--
-- There is no counterpart here of lemma 2.13 (substituting does not
-- raise the order of a phase polynomial).  The paper states it for
-- linear Q only, and rightly: it fails beyond, ¼y having order 2 while
-- ¼y[y ← x₁x₂] = ¼x₁x₂ has order 3.  So the general rules are not
-- order-preserving, and lemma 4.3 stays with the linear calculus.
--
-- Finally, the pieces the rule [Case] is stated with, which involves
-- the first two path variables y₀ and y₁ at once: the four quarters of
-- a polynomial in them, the part free of y₁ with y₁ removed (drop₁),
-- and substitution for the head variable, substHead R Q, the paper's
-- R[y₀ ← Q] for a Q that cannot mention y₀ because it lives in one path
-- variable fewer.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Substitution where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (*-zeroˡ; *-zeroʳ; *-comm)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (head-part; tail-part)
open import PathSum.Polynomial using
  (Mon; Poly; Var; y[_]; _∈ᵐ_; _∈ᵐ?_; _∪ᵐ_; _≟ᵐ_; ⟪_⟫; 1ᵐ;
   _+ᴾ_; _-ᴾ_; _·ᴾ_; κ; μ; Σmon; eval; subst; NoVar; liftXor)
open import PathSum.Polynomial.Properties using
  (Σmon-cong; Σmon-0; eval-ext; eval-+ᴾ; eval-split; eval-off; ∈ᵐ-∪;
   v∉1ᵐ; valᵛ; _∖ᵛ_; _/ᵛ_; i∣0)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ)

import Relation.Binary.PropositionalEquality as Eq

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Absence of a variable

-- v does not occur in P: every coefficient of a monomial containing it
-- is 0.  Exact, not modulo anything -- the rules substitute Q for a
-- Boolean variable, so Q must not depend on it at all.

Absent : Var n m → Poly n m → Set
Absent v P = ∀ γ → v ∈ᵐ γ → P γ ≡ 0ℤ

-- Absence implies absence modulo any c.

Absent⇒NoVar : ∀ {c} {v : Var n m} {P : Poly n m} →
               Absent v P → NoVar c v P
Absent⇒NoVar {c = c} abs γ v∈γ = Eq.subst (c ∣_) (sym (abs γ v∈γ)) i∣0


------------------------------------------------------------------------
-- General substitution

-- The coefficient of γ in the substituted part (P /ᵛ v) · L, with the
-- quotient's coefficient P (δ ∪ v) written out, as in substTerm.

substTermᴾ : Poly n m → Var n m → Poly n m → (γ δ β : Mon n m) → ℤ
substTermᴾ P v L γ δ β =
  if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
  else if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then P (δ ∪ᵐ ⟪ v ⟫) * L β
  else 0ℤ

-- P [ v ← L ].

substᴾ : Poly n m → Var n m → Poly n m → Poly n m
substᴾ P v L γ =
  (if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ)
  + Σmon (λ δ → Σmon (substTermᴾ P v L γ δ))

-- The old substitution is the instance at a lifted linear form, by
-- definition.

subst≡substᴾ : (P : Poly n m) (v : Var n m) (c : Bool) (S γ : Mon n m) →
               subst P v c S γ ≡ substᴾ P v (liftXor c S) γ
subst≡substᴾ P v c S γ = refl

-- Coefficientwise, substᴾ is what it says: the part free of v plus the
-- quotient times L.

substᴾ-≗ : (P : Poly n m) (v : Var n m) (L : Poly n m) (γ : Mon n m) →
           substᴾ P v L γ ≡ ((P ∖ᵛ v) +ᴾ ((P /ᵛ v) *ᴾ L)) γ
substᴾ-≗ P v L γ = cong ((if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ) +_)
  (Σmon-cong (λ δ → Σmon-cong (λ β →
    per ⌊ v ∈ᵐ? δ ⌋ ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ (P (δ ∪ᵐ ⟪ v ⟫)) (L β))))
  where
  per : ∀ (a b : Bool) (p l : ℤ) →
        (if a then 0ℤ else (if b then p * l else 0ℤ)) ≡
        (if b then (if a then 0ℤ else p) * l else 0ℤ)
  per true  true  p l = sym (*-zeroˡ l)
  per true  false p l = refl
  per false b     p l = refl


------------------------------------------------------------------------
-- Evaluating a substitution

eval-substᴾ : (P : Poly n m) (v : Var n m) (L : Poly n m)
              (x : Fin n → Bool) (y : Fin m → Bool) →
              eval (substᴾ P v L) x y ≡
              eval (P ∖ᵛ v) x y + (eval L x y * eval (P /ᵛ v) x y)
eval-substᴾ P v L x y = trans
  (eval-ext (substᴾ P v L) ((P ∖ᵛ v) +ᴾ ((P /ᵛ v) *ᴾ L))
            (substᴾ-≗ P v L) x y)
  (trans (eval-+ᴾ (P ∖ᵛ v) ((P /ᵛ v) *ᴾ L) x y)
         (cong (eval (P ∖ᵛ v) x y +_)
               (trans (eval-*ᴾ (P /ᵛ v) L x y)
                      (*-comm (eval (P /ᵛ v) x y) (eval L x y)))))

-- Where the assignment already gives v the value of L, substituting
-- changes nothing: compare with eval-split.

eval-substᴾ-fixed : (P : Poly n m) (v : Var n m) (L : Poly n m)
                    (x : Fin n → Bool) (y : Fin m → Bool) →
                    (if valᵛ v x y then 1ℤ else 0ℤ) ≡ eval L x y →
                    eval (substᴾ P v L) x y ≡ eval P x y
eval-substᴾ-fixed P v L x y eq = trans
  (eval-substᴾ P v L x y)
  (sym (trans (eval-split P v x y)
              (cong (λ z → eval (P ∖ᵛ v) x y + (z * eval (P /ᵛ v) x y))
                    eq)))

-- The two parts of a split are free of the variable split at.

∖ᵛ-absent : (P : Poly n m) (v : Var n m) → Absent v (P ∖ᵛ v)
∖ᵛ-absent P v γ v∈γ with v ∈ᵐ? γ
... | yes _   = refl
... | no  v∉γ = contradiction v∈γ v∉γ

/ᵛ-absent : (P : Poly n m) (v : Var n m) → Absent v (P /ᵛ v)
/ᵛ-absent P v δ v∈δ with v ∈ᵐ? δ
... | yes _   = refl
... | no  v∉δ = contradiction v∈δ v∉δ

-- Substituting for a path variable is evaluating at the assignment
-- that gives the variable the value of L (read at the original
-- assignment).  Nothing is assumed of L: the value of L enters only
-- through the substituted variable.

eval-substᴾ-≔ : (P : Poly n m) (j : Fin m) (L : Poly n m)
                (x : Fin n → Bool) (y : Fin m → Bool) (b : Bool) →
                (if b then 1ℤ else 0ℤ) ≡ eval L x y →
                eval (substᴾ P y[ j ] L) x y ≡ eval P x (y [ j ≔ b ])
eval-substᴾ-≔ P j L x y b eq = trans
  (eval-substᴾ P y[ j ] L x y)
  (sym (trans (eval-split P y[ j ] x (y [ j ≔ b ]))
    (cong₂ (λ u w → u + w)
      (off (P ∖ᵛ y[ j ]) (∖ᵛ-absent P y[ j ]))
      (cong₂ _*_
        (trans (cong (λ c → if c then 1ℤ else 0ℤ) (≔-here y j b)) eq)
        (off (P /ᵛ y[ j ]) (/ᵛ-absent P y[ j ]))))))
  where
  off : (R : Poly _ _) → Absent y[ j ] R →
        eval R x (y [ j ≔ b ]) ≡ eval R x y
  off R abs = eval-off R j abs x (y [ j ≔ b ]) y
    (λ i i≢j → ≔-there y b i≢j)


------------------------------------------------------------------------
-- Absence is preserved

-- By substitution, when L is free of the substituted variable: the
-- only splittings that survive put the variable in the part read by L.

substᴾ-absent : (P : Poly n m) (v : Var n m) (L : Poly n m) →
                Absent v L → Absent v (substᴾ P v L)
substᴾ-absent {n} {m} P v L absL γ v∈γ = cong₂ _+_ first
  (trans (Σmon-cong {g = λ _ → 0ℤ} (λ δ →
           trans (Σmon-cong {g = λ _ → 0ℤ} (each δ)) (Σmon-0 {n} {m})))
         (Σmon-0 {n} {m}))
  where
  first : (if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ) ≡ 0ℤ
  first with v ∈ᵐ? γ
  ... | yes _ = refl
  ... | no ¬p = contradiction v∈γ ¬p

  each : ∀ δ β → substTermᴾ P v L γ δ β ≡ 0ℤ
  each δ β with v ∈ᵐ? δ
  ... | yes _ = refl
  ... | no v∉δ with (δ ∪ᵐ β) ≟ᵐ γ
  ...   | no  _  = refl
  ...   | yes eq = trans
          (cong (P (δ ∪ᵐ ⟪ v ⟫) *_)
            (absL β (∈ᵐ-∪ v δ β v∉δ (Eq.subst (v ∈ᵐ_) (sym eq) v∈γ))))
          (*-zeroʳ (P (δ ∪ᵐ ⟪ v ⟫)))

-- By the ring operations.

Absent-+ᴾ : {v : Var n m} {A B : Poly n m} →
            Absent v A → Absent v B → Absent v (A +ᴾ B)
Absent-+ᴾ absA absB γ v∈γ = cong₂ _+_ (absA γ v∈γ) (absB γ v∈γ)

Absent--ᴾ : {v : Var n m} {A B : Poly n m} →
            Absent v A → Absent v B → Absent v (A -ᴾ B)
Absent--ᴾ absA absB γ v∈γ = cong₂ _-_ (absA γ v∈γ) (absB γ v∈γ)

Absent-·ᴾ : (z : ℤ) {v : Var n m} {A : Poly n m} →
            Absent v A → Absent v (z ·ᴾ A)
Absent-·ᴾ z absA γ v∈γ = trans (cong (z *_) (absA γ v∈γ)) (*-zeroʳ z)

Absent-κ : (z : ℤ) (v : Var n m) → Absent v (κ z)
Absent-κ z v γ v∈γ with γ ≟ᵐ 1ᵐ
... | yes refl = contradiction v∈γ (v∉1ᵐ v)
... | no  _    = refl

Absent-μ : (u v : Var n m) → ¬ (v ∈ᵐ ⟪ u ⟫) → Absent v (μ u)
Absent-μ u v v∉u γ v∈γ with γ ≟ᵐ ⟪ u ⟫
... | yes refl = contradiction v∈γ v∉u
... | no  _    = refl

-- A monomial δ ∪ β containing v has v in δ or in β, and the factor on
-- that side vanishes.

Absent-*ᴾ : {v : Var n m} {A B : Poly n m} →
            Absent v A → Absent v B → Absent v (A *ᴾ B)
Absent-*ᴾ {n} {m} {v} {A} {B} absA absB γ v∈γ = trans
  (Σmon-cong {g = λ _ → 0ℤ} (λ δ →
    trans (Σmon-cong {g = λ _ → 0ℤ} (each δ)) (Σmon-0 {n} {m})))
  (Σmon-0 {n} {m})
  where
  each : ∀ δ β → (if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then A δ * B β else 0ℤ) ≡ 0ℤ
  each δ β with (δ ∪ᵐ β) ≟ᵐ γ
  ... | no  _  = refl
  ... | yes eq with v ∈ᵐ? δ
  ...   | yes v∈δ = trans (cong (_* B β) (absA δ v∈δ)) (*-zeroˡ (B β))
  ...   | no  v∉δ = trans
          (cong (A δ *_)
            (absB β (∈ᵐ-∪ v δ β v∉δ (Eq.subst (v ∈ᵐ_) (sym eq) v∈γ))))
          (*-zeroʳ (A δ))


------------------------------------------------------------------------
-- The first two path variables

-- The quarters of a polynomial in y₀ (first index) and y₁ (second),
-- P = q₀₀ + y₁ q₀₁ + y₀ q₁₀ + y₀ y₁ q₁₁: each coefficient of P is,
-- definitionally, a coefficient of one of them.

q₀₀ q₀₁ q₁₀ q₁₁ : Poly n (suc (suc m)) → Poly n m
q₀₀ P = tail-part (tail-part P)
q₀₁ P = head-part (tail-part P)
q₁₀ P = tail-part (head-part P)
q₁₁ P = head-part (head-part P)

-- The part of P free of y₁, with y₁ removed: a polynomial in y₀ and
-- the remaining path variables, whose tail is q₀₀ and whose head is
-- q₁₀.

drop₁ : Poly n (suc (suc m)) → Poly n (suc m)
drop₁ P (α , b ∷ β) = P (α , b ∷ outside ∷ β)

-- R[y₀ ← Q]: Q cannot mention y₀, having one path variable fewer.

substHead : Poly n (suc m) → Poly n m → Poly n m
substHead R Q = tail-part R +ᴾ (Q *ᴾ head-part R)

eval-substHead : (R : Poly n (suc m)) (Q : Poly n m)
                 (x : Fin n → Bool) (y : Fin m → Bool) →
                 eval (substHead R Q) x y ≡
                 eval (tail-part R) x y + (eval Q x y * eval (head-part R) x y)
eval-substHead R Q x y = trans (eval-+ᴾ (tail-part R) (Q *ᴾ head-part R) x y)
  (cong (eval (tail-part R) x y +_) (eval-*ᴾ Q (head-part R) x y))
