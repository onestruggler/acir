------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, CNOT, R_k, R_k†} and their path-sums (Amy, QPL
-- 2018, definition 2.9 and proposition 2.14)
--
-- Definition 2.9 interprets a circuit by composing the path-sums of
-- its gates,
--
--    ⟦H⟧     = |x⟩ ↦ 1/√2 Σ_y e^(2πi xy/2) |y⟩
--    ⟦R_k⟧   = |x⟩ ↦ e^(2πi x/2^k) |x⟩
--    ⟦R_k†⟧  = |x⟩ ↦ e^(2πi (-x)/2^k) |x⟩
--    ⟦CNOT⟧  = |x₁ x₂⟩ ↦ |x₁ (x₁ ⊕ x₂)⟩
--    ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧ .
--
-- As in PathSum.Circuit, the composition is carried out by running
-- an interpretation state through the circuit, left to right: a phase
-- polynomial, and on each wire the Z₂-linear form it currently holds
-- (PathSum.Linear).  A Hadamard adds ½ f_w y₀ to the phase, f_w being
-- the lifting of the form on its wire and y₀ a fresh path variable
-- that it then puts on the wire; R_k adds 2^(M-k) f_w (numerators are
-- over 2^M); CNOT adds the form on its control to the form on its
-- target.  run-++ is the law ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧ at the level of
-- these states.  Definition 2.6 appends fresh path variables; here
-- they are prepended, which is a renaming.  Relating ⟦_⟧ to the
-- composition of path-sums of definition 2.6 as path-sums is not done
-- here, nor is proposition 2.10: this module, like PathSum.Circuit,
-- mentions no amplitudes.
--
-- Two departures from the paper.  CNOT carries a proof that its
-- control and target differ, which the paper leaves implicit (CNOT c c
-- would zero the wire and is not unitary).  And R k is interpreted by
-- the exponent 2^(M ∸ k), which is the gate R_k exactly when k ≤ M
-- (Rk-order, Rk-primitive); for k > M it silently denotes R_M, so M
-- has to be chosen at least the largest k in the circuit.
--
-- Proposition 2.14 says that the phase polynomial of the path-sum of a
-- Clifford+R_k circuit has degree at most k, arguing that every gate
-- has a phase polynomial of order at most k.  That overlooks the
-- Hadamard: its phase ½ x y has order 1 + 2 - 1 = 2 whatever k is.
-- The statement is therefore false for k = 1 -- the one-gate circuit H
-- is a counterexample, for the order and for the degree alike
-- (prop-2-14-needs-2, prop-2-14-deg-needs-2, prop-2-14-false-at-1) --
-- and what holds is the bound max(2, k): prop-2-14 proves that the
-- order is at most 2 ⊔ level C, level C being the largest k of an R_k
-- or R_k† in C, and prop-2-14-k is the paper's statement under the
-- hypothesis 2 ≤ k.  The order (definition 2.11, PathSum.Order) is
-- what the proof is about; degree follows only modulo the integers,
-- as the paper's "without loss of generality ... coefficients in D/Z"
-- allows, since the phase of ⟦ C ⟧ does contain integral terms of high
-- degree (R_3 on x₁ ⊕ x₂ ⊕ x₃ ⊕ x₄ contributes -x₁x₂x₃x₄).  So Deg≤
-- asks only that coefficients of degree above d vanish modulo 2^M, and
-- Ord≤⇒Deg≤ derives it from the order.
--
-- The outputs are linear: each is the lifting of a Z₂-linear form, so
-- every coefficient of degree at least 2 is even (out-linear).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.CRK.Circuit (M : ℕ) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside; ∣_∣)
open import Data.Integer.Base using (1ℤ; +_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣-trans; ∣⇒∣ᵤ)
open import Data.Integer.Properties using (+-identityˡ; *-identityʳ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using
  (zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s)
open import Data.Product.Base using (_,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.Linear using
  (Lin; varᴸ; liftᴸ; _⊕ᴸ_; wkLin; mul-y₀; liftXor-linear)
open import PathSum.Order M using
  (Ord≤; pow; val; pow-∣; pow-+; Ord≤-+; Ord≤-∸; Ord≤-0ᴾ; Ord≤-liftXor)
open import PathSum.Polynomial using
  (Poly; Mon; ∥_∥; x[_]; y[_]; 0ᴾ; _+ᴾ_; _-ᴾ_; _·ᴾ_)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reduction M using (½)

import Data.Fin.Properties as Fin
import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

private
  variable
    d d′ n m : ℕ
    P : Poly n m


------------------------------------------------------------------------
-- Circuits

data Gate (n : ℕ) : Set where
  H    : Fin n → Gate n
  CNOT : (c t : Fin n) → c ≢ t → Gate n
  R    : ℕ → Fin n → Gate n
  R†   : ℕ → Fin n → Gate n

Circuit : ℕ → Set
Circuit n = List (Gate n)

-- The normalisation of the path-sum of a circuit: one factor of 1/√2
-- for each Hadamard.

norm : Circuit n → ℕ
norm []                = 0
norm (H _ ∷ C)         = suc (norm C)
norm (CNOT _ _ _ ∷ C)  = norm C
norm (R _ _ ∷ C)       = norm C
norm (R† _ _ ∷ C)      = norm C

-- The level of a circuit: the largest k of an R_k or R_k† in it.

level : Circuit n → ℕ
level []                = 0
level (H _ ∷ C)         = level C
level (CNOT _ _ _ ∷ C)  = level C
level (R k _ ∷ C)       = k ⊔ level C
level (R† k _ ∷ C)      = k ⊔ level C


------------------------------------------------------------------------
-- Interpretation states

-- A prefix of a circuit is interpreted by a phase polynomial together
-- with the linear form each wire holds.

record State (n m : ℕ) : Set where
  constructor state
  field
    poly : Poly n m
    sig  : Fin n → Lin n m

open State public

init : State n 0
init = state 0ᴾ (λ w → varᴸ x[ w ])

-- Redirecting one wire of a signature.

infixl 6 _[_↦_]

_[_↦_] : (Fin n → Lin n m) → Fin n → Lin n m → (Fin n → Lin n m)
(σ [ w ↦ u ]) v = if ⌊ v Fin.≟ w ⌋ then u else σ v

↦-here : (σ : Fin n → Lin n m) (w : Fin n) (u : Lin n m) →
         (σ [ w ↦ u ]) w ≡ u
↦-here σ w u with w Fin.≟ w
... | yes _ = refl
... | no ¬p = contradiction refl ¬p

↦-there : (σ : Fin n → Lin n m) {v w : Fin n} (u : Lin n m) → v ≢ w →
          (σ [ w ↦ u ]) v ≡ σ v
↦-there σ {v} {w} u v≢w with v Fin.≟ w
... | yes p = contradiction p v≢w
... | no  _ = refl


------------------------------------------------------------------------
-- The gates

-- R_k adds 2^(M-k) times the lifted form on its wire to the phase,
-- and R_k† subtracts it.

stepR : ℕ → Fin n → State n m → State n m
stepR k w st = state (poly st +ᴾ (pow (M ∸ k) ·ᴾ liftᴸ (sig st w))) (sig st)

stepR† : ℕ → Fin n → State n m → State n m
stepR† k w st = state (poly st -ᴾ (pow (M ∸ k) ·ᴾ liftᴸ (sig st w))) (sig st)

-- CNOT adds the form on the control to the form on the target.

stepCNOT : Fin n → Fin n → State n m → State n m
stepCNOT c t st = state (poly st) (sig st [ t ↦ (sig st t ⊕ᴸ sig st c) ])

-- A Hadamard allocates a fresh path variable y₀, adds ½ times the
-- product of y₀ with the lifted form on its wire, and puts y₀ there.

stepH : Fin n → State n m → State n (suc m)
stepH w st =
  state (wkPoly (poly st) +ᴾ mul-y₀ (½ ·ᴾ liftᴸ (sig st w)))
        ((λ v → wkLin (sig st v)) [ w ↦ varᴸ y[ zero ] ])


------------------------------------------------------------------------
-- The path-sum of a circuit

run : Circuit n → State n m → ∃ (State n)
run []                 st = _ , st
run (H w ∷ C)          st = run C (stepH w st)
run (CNOT c t _ ∷ C)   st = run C (stepCNOT c t st)
run (R k w ∷ C)        st = run C (stepR k w st)
run (R† k w ∷ C)       st = run C (stepR† k w st)

paths : Circuit n → ℕ
paths {n} C = proj₁ (run C (init {n}))

-- Definition 2.9.

⟦_⟧ : (C : Circuit n) → PathSum n (norm C) (paths C)
⟦_⟧ {n} C = ⟨ poly result , (λ w → liftᴸ (sig result w)) ⟩
  where
  result : State n (paths C)
  result = proj₂ (run C init)

-- One path variable for each Hadamard, so the normalisation is 1/√2^m
-- with m the number of path variables, as definition 2.1 has it.

paths≡norm : (C : Circuit n) → paths C ≡ norm C
paths≡norm {n} C = trans (count C (init {n})) (ℕ.+-identityʳ (norm C))
  where
  count : ∀ {m} (C : Circuit n) (st : State n m) →
          proj₁ (run C st) ≡ norm C + m
  count []                st = refl
  count (H w ∷ C)         st =
    trans (count C (stepH w st)) (ℕ.+-suc (norm C) _)
  count (CNOT c t _ ∷ C)  st = count C (stepCNOT c t st)
  count (R k w ∷ C)       st = count C (stepR k w st)
  count (R† k w ∷ C)      st = count C (stepR† k w st)

-- ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧: running a concatenation runs the second
-- circuit from the state the first leaves.

run-++ : (C D : Circuit n) (st : State n m) →
         run (C ++ D) st ≡ run D (proj₂ (run C st))
run-++ []                D st = refl
run-++ (H w ∷ C)         D st = run-++ C D (stepH w st)
run-++ (CNOT c t _ ∷ C)  D st = run-++ C D (stepCNOT c t st)
run-++ (R k w ∷ C)       D st = run-++ C D (stepR k w st)
run-++ (R† k w ∷ C)      D st = run-++ C D (stepR† k w st)


------------------------------------------------------------------------
-- The phase of R_k

-- R k multiplies by ζ^(2^(M-k)), where ζ = e^(2πi/2^M).  When k ≤ M
-- this is e^(2πi/2^k): its 2^k-th power is 1, and its 2^(k-1)-th
-- power is ζ^½ = -1, so it is a primitive 2^k-th root of unity.

Rk-order : ∀ {k} → k ≤ M → pow (M ∸ k) * pow k ≡ pow M
Rk-order {k} k≤M = trans (pow-+ (M ∸ k) k) (cong pow (ℕ.m∸n+n≡m k≤M))

Rk-primitive : ∀ {k} → 1 ≤ k → k ≤ M → pow (M ∸ k) * pow (k ∸ 1) ≡ ½
Rk-primitive {suc k} (s≤s z≤n) k≤M =
  trans (pow-+ (M ∸ suc k) k) (cong pow (sym shift))
  where
  shift : M ∸ 1 ≡ (M ∸ suc k) + k
  shift = trans (cong (_∸ 1) (sym (ℕ.m∸n+n≡m k≤M)))
                (ℕ.+-∸-assoc (M ∸ suc k) (s≤s z≤n))


------------------------------------------------------------------------
-- Order and degree

-- The order bound weakens.

Ord≤-weaken : d ≤ d′ → Ord≤ d P → Ord≤ d′ P
Ord≤-weaken d≤d′ ordP γ = ∣-trans
  (pow-∣ (ℕ.∸-monoʳ-≤ M (ℕ.∸-monoˡ-≤ ∥ γ ∥ (s≤s d≤d′))))
  (ordP γ)

-- Multiplying by a fresh variable raises the degree of every term by
-- one, and so the order by one.

Ord≤-mul-y₀ : Ord≤ d P → Ord≤ (suc d) (mul-y₀ P)
Ord≤-mul-y₀ {d = d} {P = P} ordP (α , inside ∷ β) =
  Eq.subst (λ s → pow (val (suc d) s) ∣ P (α , β))
           (sym (ℕ.+-suc ∣ α ∣ ∣ β ∣)) (ordP (α , β))
Ord≤-mul-y₀ ordP (α , outside ∷ β) = i∣0

-- Reading a polynomial with one more path variable does not change
-- its terms.

Ord≤-wkPoly : Ord≤ d P → Ord≤ d (wkPoly P)
Ord≤-wkPoly ordP (α , inside  ∷ β) = i∣0
Ord≤-wkPoly ordP (α , outside ∷ β) = ordP (α , β)

-- The degree of a phase polynomial, read in D/Z as the paper allows:
-- every coefficient of degree above d is an integer, i.e. its
-- numerator over 2^M vanishes modulo 2^M.

Deg≤ : ℕ → Poly n m → Set
Deg≤ d P = ∀ γ → d < ∥ γ ∥ → pow M ∣ P γ

-- A term (a/2^b) x^α with a odd and b ≥ 1 has order b + |α| - 1 ≥ |α|,
-- so a polynomial of order at most d has degree at most d.

Ord≤⇒Deg≤ : Ord≤ d P → Deg≤ d P
Ord≤⇒Deg≤ {d = d} {P = P} ordP γ d<γ =
  Eq.subst (λ e → pow (M ∸ e) ∣ P γ) (ℕ.m≤n⇒m∸n≡0 d<γ) (ordP γ)


------------------------------------------------------------------------
-- Proposition 2.14, with the bound it actually has

-- Every gate adds a term of order at most max(2, k): the Hadamard's
-- ½ f_w y₀ has order 2, R_k's 2^(M-k) f_w has order k, and CNOT adds
-- nothing.

private
  run-Ord : ∀ d → 2 ≤ d → (C : Circuit n) (st : State n m) →
            level C ≤ d → Ord≤ d (poly st) →
            Ord≤ d (poly (proj₂ (run C st)))
  run-Ord d 2≤d []               st lv ord = ord
  run-Ord d 2≤d (H w ∷ C)        st lv ord = run-Ord d 2≤d C (stepH w st) lv
    (Ord≤-+ (Ord≤-wkPoly ord)
      (Ord≤-weaken 2≤d
        (Ord≤-mul-y₀ (Ord≤-liftXor 1 (proj₁ (sig st w)) (proj₂ (sig st w))))))
  run-Ord d 2≤d (CNOT c t _ ∷ C) st lv ord =
    run-Ord d 2≤d C (stepCNOT c t st) lv ord
  run-Ord d 2≤d (R k w ∷ C)      st lv ord =
    run-Ord d 2≤d C (stepR k w st) (ℕ.m⊔n≤o⇒n≤o k (level C) lv)
      (Ord≤-+ ord
        (Ord≤-weaken (ℕ.m⊔n≤o⇒m≤o k (level C) lv)
          (Ord≤-liftXor k (proj₁ (sig st w)) (proj₂ (sig st w)))))
  run-Ord d 2≤d (R† k w ∷ C)     st lv ord =
    run-Ord d 2≤d C (stepR† k w st) (ℕ.m⊔n≤o⇒n≤o k (level C) lv)
      (Ord≤-∸ ord
        (Ord≤-weaken (ℕ.m⊔n≤o⇒m≤o k (level C) lv)
          (Ord≤-liftXor k (proj₁ (sig st w)) (proj₂ (sig st w)))))

prop-2-14 : (C : Circuit n) → Ord≤ (2 ⊔ level C) (phase ⟦ C ⟧)
prop-2-14 C = run-Ord (2 ⊔ level C) (ℕ.m≤m⊔n 2 (level C)) C init
                      (ℕ.m≤n⊔m 2 (level C)) Ord≤-0ᴾ

prop-2-14-deg : (C : Circuit n) → Deg≤ (2 ⊔ level C) (phase ⟦ C ⟧)
prop-2-14-deg C = Ord≤⇒Deg≤ (prop-2-14 C)

-- The paper's statement, for k ≥ 2.

prop-2-14-k : ∀ k → 2 ≤ k → (C : Circuit n) → level C ≤ k →
              Ord≤ k (phase ⟦ C ⟧)
prop-2-14-k k 2≤k C lv = Ord≤-weaken (ℕ.⊔-lub 2≤k lv) (prop-2-14 C)

prop-2-14-k-deg : ∀ k → 2 ≤ k → (C : Circuit n) → level C ≤ k →
                  Deg≤ k (phase ⟦ C ⟧)
prop-2-14-k-deg k 2≤k C lv = Ord≤⇒Deg≤ (prop-2-14-k k 2≤k C lv)


------------------------------------------------------------------------
-- The paper's bound fails at k = 1

-- One Hadamard has phase ½ x₀ y₀, a term of degree 2 whose coefficient
-- is not an integer.  (Only M ≥ 1 is needed, so that ½ is not an
-- integer.)

private
  γ₀ : Mon 1 1
  γ₀ = inside ∷ [] , inside ∷ []

  phase-at : phase ⟦ H {1} zero ∷ [] ⟧ γ₀ ≡ ½
  phase-at = trans (+-identityˡ (½ * 1ℤ)) (*-identityʳ ½)

  -- 2^(e+1) does not divide 2^e.
  pow-∤ : ∀ e → ¬ (pow (suc e) ∣ pow e)
  pow-∤ e h = ℕ.<⇒≱ (ℕ.^-monoʳ-< 2 (s≤s (s≤s z≤n)) (ℕ.n<1+n e))
                    (ℕDiv.∣⇒≤ {{ℕ.m^n≢0 2 e}} (∣⇒∣ᵤ h))

  suc∸1 : ∀ {k} → 1 ≤ k → suc (k ∸ 1) ≡ k
  suc∸1 (s≤s z≤n) = refl

prop-2-14-deg-needs-2 : 1 ≤ M → ¬ Deg≤ 1 (phase ⟦ H {1} zero ∷ [] ⟧)
prop-2-14-deg-needs-2 1≤M deg = pow-∤ (M ∸ 1)
  (Eq.subst (λ e → pow e ∣ ½) (sym (suc∸1 1≤M))
    (Eq.subst (pow M ∣_) phase-at (deg γ₀ (s≤s (s≤s z≤n)))))

prop-2-14-needs-2 : 1 ≤ M → ¬ Ord≤ 1 (phase ⟦ H {1} zero ∷ [] ⟧)
prop-2-14-needs-2 1≤M ord = prop-2-14-deg-needs-2 1≤M (Ord≤⇒Deg≤ ord)

-- So proposition 2.14 as stated, for circuits over {H, CNOT, R_1} and
-- read as weakly as possible (degree modulo the integers), is false.

prop-2-14-false-at-1 :
  1 ≤ M → ¬ (∀ (C : Circuit 1) → level C ≤ 1 → Deg≤ 1 (phase ⟦ C ⟧))
prop-2-14-false-at-1 1≤M claim =
  prop-2-14-deg-needs-2 1≤M (claim (H zero ∷ []) z≤n)


------------------------------------------------------------------------
-- The outputs are linear

-- Every output is the lifting of a Z₂-linear form, so modulo 2 only
-- its constant and linear terms survive.

out-linear : (C : Circuit n) (w : Fin n) (γ : Mon n (paths C)) →
             2 ≤ ∥ γ ∥ → (+ 2) ∣ out ⟦ C ⟧ w γ
out-linear {n} C w γ =
  liftXor-linear (proj₁ (sig result w)) (proj₂ (sig result w)) γ
  where
  result : State n (paths C)
  result = proj₂ (run C init)
