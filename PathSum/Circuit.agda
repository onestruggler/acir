------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford circuits and the path-sums corollary 4.4 reduces
-- (Amy, QPL 2018, sections 4.1 and 4.3)
--
-- Corollary 4.4 does not apply lemma 4.3 to the path-sum of a circuit
-- but to its isometry restriction ξ|f(x,y)=x of section 4.1: the sum
-- over those paths that carry x back to x.  That restriction has the
-- identity for its output signature, so all of its path variables are
-- internal.  It is reified by solving f (x , y) = x for y, which over
-- the generators below is immediate -- every output is a single
-- variable, and the variable a Hadamard puts on a wire is forced to
-- be x_w exactly when no later Hadamard touches that wire.
--
-- Interpreting a circuit with that solution already substituted is
-- what ⟦_⟧ᴿ does, and it is what turns the two hypotheses of
-- corollary 4.4 into theorems: the outputs are the inputs, so every
-- path variable is internal, and the phase is a sum of terms ¼ u and
-- ½ u v, so it has order at most two.
--
-- The gates are
--
--    S w    : |x⟩ ↦ i^(x_w) |x⟩                    phase  ¼ x_w
--    CZ w v : |x⟩ ↦ (-1)^(x_w x_v) |x⟩             phase  ½ x_w x_v
--    H w    : |x⟩ ↦ 1/√2 Σ_y (-1)^(x_w y) |x[w←y]⟩ phase  ½ x_w y
--
-- and {H , S , CZ} generates the Clifford group up to Paulis and
-- global phase.  The normalisation of ⟦ C ⟧ᴿ counts every Hadamard,
-- a restricted sum keeping the normalisation of the sum it restricts,
-- while its path variables count only the Hadamards that are not the
-- last on their wire.
--
-- What is not formalised is the step from ⟦ C ⟧ᴿ back to the circuit:
-- lemma 4.1, that a well-formed path-sum is the identity exactly when
-- its restriction is, holds only for isometries, and the denotation
-- of PathSum.Denotation -- a matrix entry in Z[ζ], carrying no norm
-- -- cannot say that an operator is one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Circuit (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∨_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside; ⊥; _∈_)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣-refl)
open import Data.Integer.Properties using (*-identityʳ; *-zeroʳ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; suc; _+_; _≤_)
open import Data.Product.Base using (_,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base
open import PathSum.Order M
open import PathSum.Polynomial
open import PathSum.Polynomial.Properties
open import PathSum.Reduction M using (¼; ½)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ
import Data.Vec.Base as Vec
import Relation.Binary.PropositionalEquality as Eq

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Circuits

data Gate (n : ℕ) : Set where
  H  : Fin n → Gate n
  S  : Fin n → Gate n
  CZ : Fin n → Fin n → Gate n

Circuit : ℕ → Set
Circuit n = List (Gate n)

-- The normalisation of the path-sum of a circuit: one factor of 1/√2
-- for each Hadamard.

norm : Circuit n → ℕ
norm []            = 0
norm (H _ ∷ C)     = suc (norm C)
norm (S _ ∷ C)     = norm C
norm (CZ _ _ ∷ C)  = norm C

-- Whether a later gate is a Hadamard on the same wire.  The variable
-- a Hadamard introduces survives the restriction exactly when this is
-- true of the gates after it.

hasH : Fin n → Circuit n → Bool
hasH w []            = false
hasH w (H v ∷ C)     = ⌊ w Fin.≟ v ⌋ ∨ hasH w C
hasH w (S _ ∷ C)     = hasH w C
hasH w (CZ _ _ ∷ C)  = hasH w C


------------------------------------------------------------------------
-- Interpretation states

-- A prefix of a circuit is interpreted by a phase polynomial together
-- with the signature giving the current value of each wire.  Over
-- these gates a wire always holds a single variable: its input, or
-- the variable of the last Hadamard applied to it.

record State (n m : ℕ) : Set where
  constructor state
  field
    poly : Poly n m
    sig  : Fin n → Var n m

open State public

init : State n 0
init = state 0ᴾ x[_]

-- Redirecting one wire of a signature.

infixl 6 _[_↦_]

_[_↦_] : (Fin n → Var n m) → Fin n → Var n m → (Fin n → Var n m)
(σ [ w ↦ u ]) v = if ⌊ v Fin.≟ w ⌋ then u else σ v

private
  ⌊≢⌋ : {v w : Fin n} → ¬ (v ≡ w) → ⌊ v Fin.≟ w ⌋ ≡ false
  ⌊≢⌋ {v = v} {w} v≢w with v Fin.≟ w
  ... | yes p = contradiction p v≢w
  ... | no  _ = refl


------------------------------------------------------------------------
-- Adding a term to the phase

-- The monic polynomial of a monomial; μ v is mono ⟪ v ⟫.

mono : Mon n m → Poly n m
mono δ γ = if ⌊ γ ≟ᵐ δ ⌋ then 1ℤ else 0ℤ

-- A fresh path variable is taken at the head, so the variables
-- already in play move up by one.

wkVar : Var n m → Var n (suc m)
wkVar x[ i ] = x[ i ]
wkVar y[ j ] = y[ suc j ]

wkPoly : Poly n m → Poly n (suc m)
wkPoly P (α , inside  Vec.∷ β) = 0ℤ
wkPoly P (α , outside Vec.∷ β) = P (α , β)


------------------------------------------------------------------------
-- The gates

-- S contributes ¼ times the variable on its wire.

stepS : Fin n → State n m → State n m
stepS w st = state (poly st +ᴾ (¼ ·ᴾ mono ⟪ sig st w ⟫)) (sig st)

-- CZ contributes ½ times the product of the two variables.

stepCZ : Fin n → Fin n → State n m → State n m
stepCZ w v st =
  state (poly st +ᴾ (½ ·ᴾ mono (⟪ sig st w ⟫ ∪ᵐ ⟪ sig st v ⟫))) (sig st)

-- A Hadamard contributes ½ times the product of the variable on its
-- wire with the variable it puts there.  That variable is a fresh
-- path variable, unless the restriction has forced it to be x_w --
-- which is the case exactly when no later Hadamard touches the wire.

allocH : Fin n → State n m → State n (suc m)
allocH w st =
  state (wkPoly (poly st) +ᴾ
          (½ ·ᴾ mono (⟪ wkVar (sig st w) ⟫ ∪ᵐ ⟪ y[ zero ] ⟫)))
        ((λ v → wkVar (sig st v)) [ w ↦ y[ zero ] ])

finalH : Fin n → State n m → State n m
finalH w st =
  state (poly st +ᴾ (½ ·ᴾ mono (⟪ sig st w ⟫ ∪ᵐ ⟪ x[ w ] ⟫)))
        (sig st [ w ↦ x[ w ] ])

stepH : Bool → Fin n → State n m → ∃ (State n)
stepH true  w st = suc _ , allocH w st
stepH false w st = _ , finalH w st


------------------------------------------------------------------------
-- The restricted path-sum of a circuit

run : Circuit n → State n m → ∃ (State n)
run []            st = _ , st
run (H w ∷ C)     st = run C (proj₂ (stepH (hasH w C) w st))
run (S w ∷ C)     st = run C (stepS w st)
run (CZ w v ∷ C)  st = run C (stepCZ w v st)

paths : Circuit n → ℕ
paths {n} C = proj₁ (run C (init {n}))

⟦_⟧ᴿ : (C : Circuit n) → PathSum n (norm C) (paths C)
⟦_⟧ᴿ {n} C = ⟨ poly result , (λ w → μ (sig result w)) ⟩
  where
  result : State n (paths C)
  result = proj₂ (run C init)

-- The empty circuit is the identity path-sum.

⟦[]⟧ᴿ : ⟦ [] ⟧ᴿ ≡ idPS {n}
⟦[]⟧ᴿ = refl


------------------------------------------------------------------------
-- Every path variable of ⟦ C ⟧ᴿ is internal

-- After the last Hadamard on a wire the wire holds its own input, so
-- once the whole circuit is interpreted every wire does.

private
  run-sig : (C : Circuit n) (st : State n m) →
            (∀ w → hasH w C ≡ false → sig st w ≡ x[ w ]) →
            ∀ w → sig (proj₂ (run C st)) w ≡ x[ w ]
  run-sig []            st h w = h w refl
  run-sig (S v ∷ C)     st h = run-sig C (stepS v st) h
  run-sig (CZ v u ∷ C)  st h = run-sig C (stepCZ v u st) h
  run-sig (H v ∷ C)     st h with hasH v C in eq
  ... | true  = run-sig C (allocH v st) alloc-h
    where
    alloc-h : ∀ w → hasH w C ≡ false → sig (allocH v st) w ≡ x[ w ]
    alloc-h w noH with w Fin.≟ v
    ... | yes refl = contradiction (trans (sym eq) noH) λ ()
    ... | no  w≢v  =
      cong wkVar (h w (trans (cong (_∨ hasH w C) (⌊≢⌋ w≢v)) noH))
  ... | false = run-sig C (finalH v st) final-h
    where
    final-h : ∀ w → hasH w C ≡ false → sig (finalH v st) w ≡ x[ w ]
    final-h w noH with w Fin.≟ v
    ... | yes refl = refl
    ... | no  w≢v  = h w (trans (cong (_∨ hasH w C) (⌊≢⌋ w≢v)) noH)

  NoVar-x : (i : Fin n) (j : Fin m) → NoVar (+ 2) y[ j ] (μ {n} {m} x[ i ])
  NoVar-x i j (α , β) j∈β with (α , β) ≟ᵐ ⟪ x[ i ] ⟫
  ... | no  _ = i∣0
  ... | yes p = contradiction (Eq.subst (j ∈_) (cong proj₂ p) j∈β) ∉⊥

⟦⟧ᴿ-Internal : (C : Circuit n) → Internal ⟦ C ⟧ᴿ
⟦⟧ᴿ-Internal C j w =
  Eq.subst (NoVar (+ 2) y[ j ])
           (sym (cong μ (run-sig C init (λ _ _ → refl) w)))
           (NoVar-x w j)


------------------------------------------------------------------------
-- The phase of ⟦ C ⟧ᴿ is of order at most two

private
  Ord≤-mono : {c : ℤ} (δ : Mon n m) → pow (val 2 ∥ δ ∥) ∣ c →
              Ord≤ 2 (c ·ᴾ mono δ)
  Ord≤-mono {c = c} δ h γ with γ ≟ᵐ δ
  ... | yes γ≡δ = Eq.subst (pow (val 2 ∥ γ ∥) ∣_) (sym (*-identityʳ c))
                    (Eq.subst (λ z → pow (val 2 ∥ z ∥) ∣ c) (sym γ≡δ) h)
  ... | no  _   = Eq.subst (pow (val 2 ∥ γ ∥) ∣_) (sym (*-zeroʳ c)) i∣0

  -- A quarter on a variable, and a half on a product of two: the two
  -- shapes a Clifford gate contributes, and both are of order two.

  Ord≤-¼ : (u : Var n m) → Ord≤ 2 (¼ ·ᴾ mono ⟪ u ⟫)
  Ord≤-¼ u = Ord≤-mono ⟪ u ⟫
    (Eq.subst (λ z → pow (val 2 z) ∣ ¼) (sym (∥⟪v⟫∥≡1 u)) ∣-refl)

  Ord≤-½ : (u v : Var n m) → Ord≤ 2 (½ ·ᴾ mono (⟪ u ⟫ ∪ᵐ ⟪ v ⟫))
  Ord≤-½ u v = Ord≤-mono (⟪ u ⟫ ∪ᵐ ⟪ v ⟫) (pow-∣ (val-mono 2 deg))
    where
    deg : ∥ ⟪ u ⟫ ∪ᵐ ⟪ v ⟫ ∥ ≤ 2
    deg = ℕ.≤-trans (∥∪ᵐ∥≤ ⟪ u ⟫ ⟪ v ⟫)
            (ℕ.≤-reflexive (cong₂ _+_ (∥⟪v⟫∥≡1 u) (∥⟪v⟫∥≡1 v)))

  wkPoly-Ord≤ : {d : ℕ} {P : Poly n m} → Ord≤ d P → Ord≤ d (wkPoly P)
  wkPoly-Ord≤ ordP (α , inside  Vec.∷ β) = i∣0
  wkPoly-Ord≤ ordP (α , outside Vec.∷ β) = ordP (α , β)

  run-Ord : (C : Circuit n) (st : State n m) → Ord≤ 2 (poly st) →
            Ord≤ 2 (poly (proj₂ (run C st)))
  run-Ord []            st ord = ord
  run-Ord (S v ∷ C)     st ord =
    run-Ord C (stepS v st) (Ord≤-+ ord (Ord≤-¼ (sig st v)))
  run-Ord (CZ v u ∷ C)  st ord =
    run-Ord C (stepCZ v u st) (Ord≤-+ ord (Ord≤-½ (sig st v) (sig st u)))
  run-Ord (H v ∷ C)     st ord with hasH v C
  ... | true  = run-Ord C (allocH v st)
    (Ord≤-+ (wkPoly-Ord≤ ord) (Ord≤-½ (wkVar (sig st v)) y[ zero ]))
  ... | false = run-Ord C (finalH v st)
    (Ord≤-+ ord (Ord≤-½ (sig st v) x[ v ]))

⟦⟧ᴿ-Ord≤ : (C : Circuit n) → Ord≤ 2 (phase ⟦ C ⟧ᴿ)
⟦⟧ᴿ-Ord≤ C = run-Ord C init Ord≤-0ᴾ
