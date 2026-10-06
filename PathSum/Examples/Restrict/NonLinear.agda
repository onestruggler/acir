------------------------------------------------------------------------
-- Presentations of groups
--
-- A restriction step whose solution is not linear: the miter of a
-- Toffoli circuit against its specification, where the target's
-- x₃ ⊕ x₁x₂ reaches an output
--
-- At M₀ = 0, with the instances of PathSum.Examples.Restrict.
--
-- In the miter ⟦ tof† ⟧ ∘ᴾ spec of PathSum.Examples.Restrict the
-- specification's non-linear output x₃ ⊕ x₁x₂ goes straight into a
-- Hadamard of tof† on the target, so it ends up in the phase and the
-- miter's outputs are linear.  Here the circuit is the same Toffoli
-- gate followed by a tail that is the identity -- CNOT from the target
-- to c₂, H, H on c₂, CNOT again (C₂).  The tail is contrived, there
-- only to make the miter's output non-linear.  In C₂† the tail comes first, so on wire c₂ the
-- specification's target is added to a path variable: the miter's
-- output on c₂ is y ⊕ x₃ ⊕ x₁x₂, a pivot whose Q = x₃ ⊕ x₁x₂ is not
-- linear (pivot₂, checked as PathSum.Restrict.Pivot's Pivot by
-- computation).  The route of section 4.1:
--
--  1. restrict the target, y₀ ← x₃ (restricts₁, through
--     PathSum.Restrict.Spec.restricts-after), leaving ρ₁: three path
--     variables, outputs x₁, y₁ ⊕ x₃ ⊕ x₁x₂ and x₃, phase
--     ½[y₂(y₁ + x₃ + x₂ + x₁x₂) + x₁y₀(y₁ + x₃)];
--  2. restrict c₂ by the non-linear substitution y₁ ← x₂ ⊕ x₃ ⊕ x₁x₂
--     (restricts₂), after which the phase is 0 modulo 1 and every
--     output reads its input -- by PathSum.Restrict.Pivot's
--     restricts≈restrictᴾ the reduct written here is, coefficient by
--     coefficient, the paper's substitution of the lifted solution
--     (restricts₂-is-substitution);
--  3. [Elim] twice; what is left is the identity, so ⟦ C₂ ⟧ ≋ spec
--     (padded-by-restriction).
--
-- The reducts ρ₁ and ρ₂ are written out (ρ₁'s phase was read off the
-- miter's values at the kept paths by Möbius inversion, outside Agda)
-- and checked against the semantic conditions of a step, by
-- computation at every point.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Restrict.NonLinear where

open import Data.Bool.Base using (Bool; true; false; not; _xor_; _∧_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_; ∣m∣n⇒∣m-n)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (toWitness)

open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there; ≔-cong)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS; head-part)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Examples.Base using
  (_⋆_; x₁; x₂; x₃; y₁; y₂; y₃; y₄)
open import PathSum.Linear using
  (Lin; valᴸ; varᴸ; liftᴸ; _⊕ᴸ_; valᴸ-var; valᴸ-⊕)
open import PathSum.Order 3 using (pow)
open import PathSum.Polynomial using
  (Poly; Var; μ; x[_]; y[_]; 0ᴾ; _+ᴾ_; _∪ᵐ_; eval; _≈[_]_; NoVar)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Decidable using
  (all-points?; by-eval; NoVar?)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-cong; eval-≈; valᵛ; i∣0)
open import PathSum.Polynomial.Substitution using (Absent-μ; Absent⇒NoVar)
open import PathSum.Reorder using (insertᵃ)

import PathSum.Examples.Restrict as E

open E using (c₁; c₂; t; spec; by-restriction)
open E.D using (Assign; outBit; _≋_)

open +-*-Solver using (solve; con; _:+_; _:-_; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The circuit: the Toffoli gate, then an identity tail on c₂

tail : E.K.Circuit 3
tail = E.K.CNOT t c₂ (λ ()) ∷ E.K.H c₂ ∷ E.K.H c₂ ∷ E.K.CNOT t c₂ (λ ()) ∷ []

C₂ : E.K.Circuit 3
C₂ = E.C ++ tail

-- ⟦ C₂† ⟧'s outputs: x′₁, y₂ ⊕ x′₃ and y₀ (in its own inputs x′).

out-c₁ : out E.K.⟦ C₂ E.KA.† ⟧ c₁ ≡ liftᴸ (varᴸ x[ c₁ ])
out-c₁ = refl

out-c₂ : out E.K.⟦ C₂ E.KA.† ⟧ c₂ ≡
         liftᴸ (varᴸ y[ suc (suc zero) ] ⊕ᴸ varᴸ x[ t ])
out-c₂ = refl

out-t : out E.K.⟦ C₂ E.KA.† ⟧ t ≡ liftᴸ (varᴸ y[ zero ])
out-t = refl

private
  -- The Toffoli function, the one the specification computes.

  F : Assign 3 → Assign 3
  F = E.TG.toffoli c₁ c₂ t

  F-c₁ : ∀ x → F x c₁ ≡ x c₁
  F-c₁ x = ≔-there x {t} {c₁} (x t xor (x c₁ ∧ x c₂)) (λ ())

  F-t : ∀ x → F x t ≡ x t xor (x c₁ ∧ x c₂)
  F-t x = ≔-here x t (x t xor (x c₁ ∧ x c₂))

  F-≗ : ∀ {x x′ : Assign 3} → (∀ i → x i ≡ x′ i) → ∀ w → F x w ≡ F x′ w
  F-≗ {x} {x′} x≗ w =
    trans (≔-cong t (x t xor (x c₁ ∧ x c₂)) x≗ w)
          (cong (λ b → (x′ [ t ≔ b ]) w)
                (cong₂ _xor_ (x≗ t) (cong₂ _∧_ (x≗ c₁) (x≗ c₂))))

  read : (w : Fin 3) (l : Lin 3 4) → out E.K.⟦ C₂ E.KA.† ⟧ w ≡ liftᴸ l →
         (x′ : Assign 3) (Y : Assign 4) →
         outBit E.K.⟦ C₂ E.KA.† ⟧ x′ Y w ≡ valᴸ l x′ Y
  read w l eq x′ Y = E.Am.outBit-liftᴸ E.K.⟦ C₂ E.KA.† ⟧ x′ Y w l eq

  outBit-≗ : ∀ {k m} (ξ : PathSum 3 k m) {x x′ : Assign 3} {y y′ : Assign m}
             (w : Fin 3) → (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
             outBit ξ x y w ≡ outBit ξ x′ y′ w
  outBit-≗ ξ {x} {x′} {y} {y′} w x≗ y≗ =
    cong odd (eval-cong (out ξ w) {x} {x′} {y} {y′} x≗ y≗)

  -- The outputs of the reducts are free of y₀ when they are inputs.

  outs-internal : ∀ {k m} (ρ : PathSum 3 k (suc m)) →
                  (∀ w → out ρ w ≡ μ x[ w ]) →
                  ∀ w → NoVar (+ 2) y[ zero ] (out ρ w)
  outs-internal ρ eq w = subst (NoVar (+ 2) y[ zero ]) (sym (eq w))
    (Absent⇒NoVar {c = + 2} {v = y[ zero ]} {P = μ x[ w ]}
                  (Absent-μ x[ w ] y[ zero ] ∉⊥))


------------------------------------------------------------------------
-- Step 1: the target, y₀ ← x₃

-- ½[y₂(y₁ + x₃ + x₂ + x₁x₂) + x₁y₀(y₁ + x₃)], in eighths, with the
-- path variables after y₀ renumbered from 0 (Examples.Base's y₁ is
-- variable 0).

P₁ : Poly 3 3
P₁ = (+ 4) ⋆ (y₂ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (x₃ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (x₂ ∪ᵐ y₃) +ᴾ
     (+ 4) ⋆ (x₁ ∪ᵐ y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₃ ∪ᵐ y₁) +ᴾ
     (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₃)

-- Wire c₂ reads y₁ ⊕ x₃ ⊕ x₁x₂.

f₁ : Poly 3 3
f₁ = (+ 1) ⋆ y₂ +ᴾ (+ 1) ⋆ x₃ +ᴾ (+ 1) ⋆ (x₁ ∪ᵐ x₂)

ρ₁ : PathSum 3 4 3
ρ₁ = ⟨ P₁ , outs ⟩
  where
  outs : Fin 3 → Poly 3 3
  outs zero             = μ x[ zero ]
  outs (suc zero)       = f₁
  outs (suc (suc zero)) = μ x[ suc (suc zero) ]

-- ⟦ C₂† ⟧'s own phase, modulo 1 (read off its values outside Agda and
-- checked here coefficient by coefficient): the ⅛ terms of its T gates
-- add up to halves.

P† : Poly 3 4
P† = (+ 4) ⋆ (y₃ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (x₃ ∪ᵐ y₄) +ᴾ
     (+ 4) ⋆ (x₃ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (x₂ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₂ ∪ᵐ y₃) +ᴾ
     (+ 4) ⋆ (x₁ ∪ᵐ x₃ ∪ᵐ y₂)

phase† : phase E.K.⟦ C₂ E.KA.† ⟧ ≈[ pow 3 ] P†
phase† = by-eval (phase E.K.⟦ C₂ E.KA.† ⟧) (pow 3) P†

-- Checked at every point: f₁'s value, and the phase.

private
  f₁-val : ∀ (x : Assign 3) (g : Assign 3) →
           outBit ρ₁ x g c₂ ≡ g (suc zero) xor (x t xor (x c₁ ∧ x c₂))
  f₁-val = toWitness
    {a? = all-points? {B = λ x g → outBit ρ₁ x g c₂ ≡
                                    g (suc zero) xor (x t xor (x c₁ ∧ x c₂))}
            (λ {x} {x′} {g} {g′} x≗ g≗ e → trans
               (sym (outBit-≗ ρ₁ c₂ x≗ g≗))
               (trans e (cong₂ _xor_ (g≗ (suc zero))
                  (cong₂ _xor_ (x≗ t) (cong₂ _∧_ (x≗ c₁) (x≗ c₂))))))
            (λ x g → outBit ρ₁ x g c₂ ≟ᵇ
                     g (suc zero) xor (x t xor (x c₁ ∧ x c₂)))} tt

  E₁ : Assign 3 → Assign 3 → ℤ
  E₁ x g = eval P₁ x g - (0ℤ + eval P† (F x) (insertᵃ zero (x t) g))

  E₁-resp : ∀ {x x′ : Assign 3} {g g′ : Assign 3} →
            (∀ i → x i ≡ x′ i) → (∀ j → g j ≡ g′ j) →
            pow 3 ∣ E₁ x g → pow 3 ∣ E₁ x′ g′
  E₁-resp {x} {x′} {g} {g′} x≗ g≗ = subst (pow 3 ∣_)
    (cong₂ _-_ (eval-cong P₁ x≗ g≗)
      (cong (λ e → 0ℤ + e)
        (eval-cong P†
          {F x} {F x′} {insertᵃ zero (x t) g} {insertᵃ zero (x′ t) g′}
          (F-≗ x≗) ins-≗)))
    where
    ins-≗ : ∀ i → insertᵃ zero (x t) g i ≡ insertᵃ zero (x′ t) g′ i
    ins-≗ zero    = x≗ t
    ins-≗ (suc i) = g≗ i

  phase₁′ : ∀ (x : Assign 3) (g : Assign 3) → pow 3 ∣ E₁ x g
  phase₁′ = toWitness
    {a? = all-points? {B = λ x g → pow 3 ∣ E₁ x g} E₁-resp
                      (λ x g → pow 3 ∣? E₁ x g)} tt

  -- Back to the circuit's phase, which agrees with P† modulo 1.

  phase₁ : ∀ (x : Assign 3) (g : Assign 3) →
           pow 3 ∣ (eval P₁ x g -
                    (0ℤ + eval (phase E.K.⟦ C₂ E.KA.† ⟧) (F x)
                                 (insertᵃ zero (x t) g)))
  phase₁ x g = subst (pow 3 ∣_) (shape (eval P₁ x g) b′ b)
    (∣m∣n⇒∣m-n (phase₁′ x g)
      (eval-≈ {d = pow 3} (phase E.K.⟦ C₂ E.KA.† ⟧) P† phase† (F x)
              (insertᵃ zero (x t) g)))
    where
    b b′ : ℤ
    b  = eval P† (F x) (insertᵃ zero (x t) g)
    b′ = eval (phase E.K.⟦ C₂ E.KA.† ⟧) (F x) (insertᵃ zero (x t) g)

    shape : ∀ a b′ b → (a - (0ℤ + b)) - (b′ - b) ≡ a - (0ℤ + b′)
    shape = solve 3 (λ a b′ b → (a :- (con 0ℤ :+ b)) :- (b′ :- b) :=
                                a :- (con 0ℤ :+ b′)) refl

restricts₁ : E.R.Restricts (E.K.⟦ C₂ E.KA.† ⟧ ∘ᴾ spec) t zero ρ₁
restricts₁ = E.S.restricts-after E.K.⟦ C₂ E.KA.† ⟧ spec F (λ _ → 0ℤ)
  (E.TG.fun-toffoliˢ c₁ c₂ t) (λ x → eval-0ᴾ {3} {0} x E.CL.none)
  t zero ρ₁ (λ x g → x t) miss outs solves phase₁
  where
  miss : ∀ (x : Assign 3) (g : Assign 3) →
         outBit E.K.⟦ C₂ E.KA.† ⟧ (F x) (insertᵃ zero (not (x t)) g) t ≡
         not (x t)
  miss x g = trans (read t (varᴸ y[ zero ]) out-t (F x)
                         (insertᵃ zero (not (x t)) g))
                   (valᴸ-var y[ zero ] (F x) (insertᵃ zero (not (x t)) g))

  outs : ∀ (x : Assign 3) (g : Assign 3) v → outBit ρ₁ x g v ≡
         outBit E.K.⟦ C₂ E.KA.† ⟧ (F x) (insertᵃ zero (x t) g) v
  outs x g zero = trans (E.D.outBit-μ ρ₁ x g zero x[ zero ] refl)
    (sym (trans (read c₁ (varᴸ x[ c₁ ]) out-c₁ (F x) (insertᵃ zero (x t) g))
                (trans (valᴸ-var x[ c₁ ] (F x) (insertᵃ zero (x t) g))
                       (F-c₁ x))))
  outs x g (suc zero) = trans (f₁-val x g)
    (sym (trans (read c₂ (varᴸ y[ suc (suc zero) ] ⊕ᴸ varᴸ x[ t ]) out-c₂
                      (F x) (insertᵃ zero (x t) g))
           (trans (valᴸ-⊕ (varᴸ y[ suc (suc zero) ]) (varᴸ x[ t ])
                          (F x) (insertᵃ zero (x t) g))
             (cong₂ _xor_
               (valᴸ-var y[ suc (suc zero) ] (F x) (insertᵃ zero (x t) g))
               (trans (valᴸ-var x[ t ] (F x) (insertᵃ zero (x t) g))
                      (F-t x))))))
  outs x g (suc (suc zero)) = trans (E.D.outBit-μ ρ₁ x g t x[ t ] refl)
    (sym (trans (read t (varᴸ y[ zero ]) out-t (F x) (insertᵃ zero (x t) g))
                (valᴸ-var y[ zero ] (F x) (insertᵃ zero (x t) g))))

  solves : ∀ (x : Assign 3) (g : Assign 3) → outBit ρ₁ x g t ≡ x t
  solves x g = E.D.outBit-μ ρ₁ x g t x[ t ] refl


------------------------------------------------------------------------
-- Step 2: wire c₂, y₁ ← x₂ ⊕ x₃ ⊕ x₁x₂

-- The output on c₂ is y₁ ⊕ Q with Q = x₃ ⊕ x₁x₂ not mentioning y₁:
-- the paper's hypothesis, as a coefficient condition.

pivot₂ : E.P.Pivot ρ₁ c₂ (suc zero)
pivot₂ = toWitness {a? = E.P.pivot? ρ₁ c₂ (suc zero)} tt

-- What is left: the phase 0 modulo 1, every output its input.

ρ₂ : PathSum 3 4 2
ρ₂ = ⟨ 0ᴾ , (λ w → μ x[ w ]) ⟩

private
  keep₂ : Assign 3 → Assign 2 → Bool
  keep₂ x g = x c₂ xor (x t xor (x c₁ ∧ x c₂))

  keep₂-≗ : ∀ {x x′ : Assign 3} → (∀ i → x i ≡ x′ i) →
            ∀ (g : Assign 2) → keep₂ x g ≡ keep₂ x′ g
  keep₂-≗ x≗ g = cong₂ _xor_ (x≗ c₂)
    (cong₂ _xor_ (x≗ t) (cong₂ _∧_ (x≗ c₁) (x≗ c₂)))

  ins₂-≗ : ∀ {g g′ : Assign 2} {b b′ : Bool} → b ≡ b′ → (∀ j → g j ≡ g′ j) →
           ∀ i → insertᵃ (suc zero) b g i ≡ insertᵃ (suc zero) b′ g′ i
  ins₂-≗ e g≗ zero             = g≗ zero
  ins₂-≗ e g≗ (suc zero)       = e
  ins₂-≗ e g≗ (suc (suc zero)) = g≗ (suc zero)

  miss₂ : ∀ (x : Assign 3) (g : Assign 2) →
          outBit ρ₁ x (insertᵃ (suc zero) (not (keep₂ x g)) g) c₂ ≡ not (x c₂)
  miss₂ = toWitness
    {a? = all-points?
      {B = λ x g → outBit ρ₁ x (insertᵃ (suc zero) (not (keep₂ x g)) g) c₂ ≡
                   not (x c₂)}
      (λ {x} {x′} {g} {g′} x≗ g≗ e → trans
         (sym (outBit-≗ ρ₁ c₂ x≗ (ins₂-≗ (cong not (keep₂-≗ x≗ g)) g≗)))
         (trans e (cong not (x≗ c₂))))
      (λ x g → outBit ρ₁ x (insertᵃ (suc zero) (not (keep₂ x g)) g) c₂ ≟ᵇ
               not (x c₂))} tt

  keeps₂ : ∀ (x : Assign 3) (g : Assign 2) →
           outBit ρ₁ x (insertᵃ (suc zero) (keep₂ x g) g) c₂ ≡ x c₂
  keeps₂ = toWitness
    {a? = all-points?
      {B = λ x g → outBit ρ₁ x (insertᵃ (suc zero) (keep₂ x g) g) c₂ ≡ x c₂}
      (λ {x} {x′} {g} {g′} x≗ g≗ e → trans
         (sym (outBit-≗ ρ₁ c₂ x≗ (ins₂-≗ (keep₂-≗ x≗ g) g≗)))
         (trans e (x≗ c₂)))
      (λ x g → outBit ρ₁ x (insertᵃ (suc zero) (keep₂ x g) g) c₂ ≟ᵇ x c₂)} tt

  E₂ : Assign 3 → Assign 2 → ℤ
  E₂ x g = eval 0ᴾ x g - eval P₁ x (insertᵃ (suc zero) (keep₂ x g) g)

  phase₂ : ∀ (x : Assign 3) (g : Assign 2) → pow 3 ∣ E₂ x g
  phase₂ = toWitness
    {a? = all-points? {B = λ x g → pow 3 ∣ E₂ x g}
      (λ {x} {x′} {g} {g′} x≗ g≗ → subst (pow 3 ∣_)
         (cong₂ _-_ (eval-cong 0ᴾ x≗ g≗)
           (eval-cong P₁ {x} {x′}
              {insertᵃ (suc zero) (keep₂ x g) g}
              {insertᵃ (suc zero) (keep₂ x′ g′) g′} x≗
              (ins₂-≗ (keep₂-≗ x≗ g) g≗))))
      (λ x g → pow 3 ∣? E₂ x g)} tt

restricts₂ : E.R.Restricts ρ₁ c₂ (suc zero) ρ₂
restricts₂ = record
  { keep   = keep₂
  ; miss   = miss₂
  ; outs   = outs
  ; solves = λ x g → E.D.outBit-μ ρ₂ x g c₂ x[ c₂ ] refl
  ; phase≡ = phase₂
  }
  where
  outs : ∀ (x : Assign 3) (g : Assign 2) v → outBit ρ₂ x g v ≡
         outBit ρ₁ x (insertᵃ (suc zero) (keep₂ x g) g) v
  outs x g zero = trans (E.D.outBit-μ ρ₂ x g zero x[ zero ] refl)
    (sym (E.D.outBit-μ ρ₁ x (insertᵃ (suc zero) (keep₂ x g) g) zero
                       x[ zero ] refl))
  outs x g (suc zero) = trans (E.D.outBit-μ ρ₂ x g c₂ x[ c₂ ] refl)
    (sym (keeps₂ x g))
  outs x g (suc (suc zero)) = trans (E.D.outBit-μ ρ₂ x g t x[ t ] refl)
    (sym (E.D.outBit-μ ρ₁ x (insertᵃ (suc zero) (keep₂ x g) g) t
                       x[ t ] refl))

-- ρ₂ is the paper's substitution y₁ ← lift(x₂ ⊕ x₃ ⊕ x₁x₂), coefficient
-- by coefficient.

restricts₂-is-substitution :
  phase ρ₂ ≈[ pow 3 ] phase (E.P.restrictᴾ ρ₁ c₂ (suc zero)) ×
  (∀ v → out ρ₂ v ≈[ + 2 ] out (E.P.restrictᴾ ρ₁ c₂ (suc zero)) v)
restricts₂-is-substitution = E.P.restricts≈restrictᴾ
  {ξ = ρ₁} {w = c₂} {j = suc zero} {ρ = ρ₂} pivot₂ restricts₂


------------------------------------------------------------------------
-- Steps 3 and 4: [Elim] twice

elim₂ : ρ₂ E.Rd.⟶ E.Rd.elim-reduct ρ₂
elim₂ = E.Rd.elim ρ₂ (λ _ → i∣0) (outs-internal ρ₂ (λ _ → refl))

ρ₃ : PathSum 3 2 1
ρ₃ = E.Rd.elim-reduct ρ₂

elim₃ : ρ₃ E.Rd.⟶ E.Rd.elim-reduct ρ₃
elim₃ = E.Rd.elim ρ₃ (λ _ → i∣0) noy
  where
  noy : ∀ w → NoVar (+ 2) y[ zero ] (out ρ₃ w)
  noy zero = toWitness {a? = NoVar? (+ 2) y[ zero ] (out ρ₃ zero)} tt
  noy (suc zero) = toWitness {a? = NoVar? (+ 2) y[ zero ] (out ρ₃ (suc zero))} tt
  noy (suc (suc zero)) =
    toWitness {a? = NoVar? (+ 2) y[ zero ] (out ρ₃ (suc (suc zero)))} tt

ρ₄ : PathSum 3 0 0
ρ₄ = E.Rd.elim-reduct ρ₃

chain : (E.K.⟦ C₂ E.KA.† ⟧ ∘ᴾ spec) E.R.⇝* ρ₄
chain = E.R.restrict (E.R.step t zero restricts₁) E.R.◅⇝
        (E.R.restrict (E.R.step c₂ (suc zero) restricts₂) E.R.◅⇝
        (E.R.rule (E.F.⟶⇒⟶ᶠ elim₂) E.R.◅⇝
        (E.R.rule (E.F.⟶⇒⟶ᶠ elim₃) E.R.◅⇝ E.R.ε⇝)))

-- What is left is the identity: the padded circuit meets the
-- specification.

padded-by-restriction : E.K.⟦ C₂ ⟧ ≋ spec
padded-by-restriction = by-restriction C₂ spec ρ₄ chain
  (refl , outs₄ , by-eval (phase ρ₄) (pow 3) 0ᴾ)
  where
  outs₄ : ∀ w → out ρ₄ w ≈[ + 2 ] μ x[ w ]
  outs₄ zero             = by-eval (out ρ₄ zero) (+ 2) (μ x[ zero ])
  outs₄ (suc zero)       = by-eval (out ρ₄ (suc zero)) (+ 2) (μ x[ suc zero ])
  outs₄ (suc (suc zero)) =
    by-eval (out ρ₄ (suc (suc zero))) (+ 2) (μ x[ suc (suc zero) ])
