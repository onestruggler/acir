------------------------------------------------------------------------
-- Presentations of groups
--
-- Irreducible path-sums for all of figure 2, and every path-sum
-- reduces to one
--
-- Proposition 3.2 (Amy, QPL 2018) says that every sequence of rewrites
-- "terminates with an irreducible path-sum".  PathSum.Full proves that
-- every sequence of steps of _⟶ᶠ_ -- all four rules of figure 2, at
-- any internal variable, [Case] at any pair -- is finite (⟶ᶠ-SN).  This
-- module proves the other half, constructively, as PathSum.Anywhere.
-- Match does for the linear rules: whether some rule applies to a
-- path-sum is decidable (stepᶠ?), so every path-sum reduces to one to
-- which none applies (normal-formᶠ), and irreducibility is decidable
-- (irreducibleᶠ?).  The same holds for the head calculus _⟶ᴳ_ of
-- PathSum.Reduction.General alone (headᴳ?, normal-formᴳ).
--
-- The rules quantify over quotients, and it is not enough to try
-- finitely many: [ω], [HH] and [Case] apply when *some* Boolean-valued
-- Q (and X, Q′) satisfies their premises, and there are infinitely
-- many polynomials.  PathSum.Full.Canonical computes one candidate per
-- rule from the phase and proves that it works whenever any quotient
-- does; so a rule applies iff it applies with its candidate, which is
-- a coefficient-wise check over all 2^(n+m) monomials.  All four rules
-- are decided, [Case] included.
--
-- At one path-sum the search tries every rule at the head of every
-- double renumbering front j′ (front j ξ).  That covers every
-- derivation of a step of _⟶ᶠ_ (at j ∘ at j′ literally, and the other
-- three shapes because front zero changes no premise: headᴳ-zero), so
-- when it fails, no rule applies at any variable or pair.  Irreducibleᶠ
-- is stronger than PathSum.Anywhere.Match's Irreducible, which only
-- rules out the linear rules (Irreducibleᶠ⇒Irreducible).
--
-- What is not formalised: the paper's claim that rules are matched,
-- and path-sums normalised, in polynomial time.  This search takes
-- exponential time (every monomial, every variable, every pair), and
-- the lift behind each candidate folds over every monomial.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.Match (M : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (any?; all?)
open import Data.Integer.Base using (0ℤ; 1ℤ; +_)
open import Data.Integer.Properties using (_≟_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; map′; _×?_; _→?_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; phase; out; head-part)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; Var; y[_]; _∈ᵐ?_; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Polynomial.Product using (_*ᴾ_)
open import PathSum.Polynomial.Boolean using (BoolValued; BoolValued⇔idem)
open import PathSum.Polynomial.Substitution using
  (Absent; q₁₀; q₀₁; q₁₁)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; _⟶ᴳ*_; εᴳ; _◅ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; ⟶ᴳ-dec)
open import PathSum.Reorder using (front; NoVar-front; NoVar-front-suc)
open import PathSum.Anywhere M using
  (plain; at; SN; sn; SN-by-<)
open import PathSum.Anywhere.Match M using
  (allMon?; _≈?[_]_; NoVar?; Internal₀; Internal₀?; ElimQ; ElimQ?;
   Irreducible)
open import PathSum.Full M using
  (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_; ⟶ᵍ⇒⟶ᶠ; ⟶ᶠ-SN)
open import PathSum.Full.Canonical M using
  (ωQuot; BoolValued-ωQuot; ωQuot-complete;
   hhQuot; BoolValued-hhQuot; Absent-hhQuot; hhQuot-complete;
   caseX; caseQ; caseQ′; BoolValued-caseX; BoolValued-caseQ;
   BoolValued-caseQ′; case-complete)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The premises of the head rules

-- Other than the normalisation each rule consumes and the absence of
-- y₀ from the outputs (Anywhere.Match.Internal₀): the quotient of the
-- phase by y₀ is 0 ([Elim], Anywhere.Match.ElimQ), ¼ + ½Q ([ω]) or
-- ½(y_i + Q) with Q free of y_i ([HH]), for some Boolean-valued Q.
-- [Case] asks for a second path variable y₁, absent from the outputs
-- too, the y₀y₁ quarter ½, and X, Q and Q′ decomposing the other two
-- quarters.

ΩQᴳ : PathSum n k (suc m) → Set
ΩQᴳ {n = n} {m = m} ξ = ∃ λ (Q : Poly n m) →
  BoolValued Q × head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q))

HHQᴳ : PathSum n k (suc m) → Set
HHQᴳ {n = n} {m = m} ξ = ∃ λ (i : Fin m) → ∃ λ (Q : Poly n m) →
  BoolValued Q × Absent y[ i ] Q ×
  head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))

Internal₁ : PathSum n k (suc (suc m)) → Set
Internal₁ {n} ξ = ∀ (w : Fin n) → NoVar (+ 2) y[ suc zero ] (out ξ w)

CaseQᴳ : PathSum n k (suc (suc m)) → Set
CaseQᴳ {n = n} {m = m} ξ =
  ∃ λ (X : Poly n m) → ∃ λ (Q : Poly n m) → ∃ λ (Q′ : Poly n m) →
  BoolValued X × BoolValued Q × BoolValued Q′ ×
  q₁₀ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) ×
  q₀₁ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′))

CaseAll : PathSum n k (suc (suc m)) → Set
CaseAll ξ = Internal₁ ξ × q₁₁ (phase ξ) ≈[ pow M ] κ ½ × CaseQᴳ ξ


------------------------------------------------------------------------
-- Deciding them

-- Each quantified premise holds iff it holds at the canonical
-- quotients of PathSum.Full.Canonical, which is a finite check.

ΩQᴳ? : (ξ : PathSum n k (suc m)) → Dec (ΩQᴳ ξ)
ΩQᴳ? ξ = map′
  (λ eq → ωQuot H , BoolValued-ωQuot H , eq)
  (λ (Q , _ , eq) → ωQuot-complete H Q eq)
  (H ≈?[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ ωQuot H)))
  where
  H = head-part (phase ξ)

HHQᴳ? : (ξ : PathSum n k (suc m)) → Dec (HHQᴳ ξ)
HHQᴳ? ξ = map′
  (λ (i , eq) →
     i , hhQuot y[ i ] H , BoolValued-hhQuot y[ i ] H ,
     Absent-hhQuot y[ i ] H , eq)
  (λ (i , Q , _ , absQ , eq) → i , hhQuot-complete y[ i ] H Q absQ eq)
  (any? (λ i → H ≈?[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ hhQuot y[ i ] H))))
  where
  H = head-part (phase ξ)

Internal₁? : (ξ : PathSum n k (suc (suc m))) → Dec (Internal₁ ξ)
Internal₁? ξ = all? (λ w → NoVar? (+ 2) y[ suc zero ] (out ξ w))

CaseQᴳ? : (ξ : PathSum n k (suc (suc m))) → Dec (CaseQᴳ ξ)
CaseQᴳ? ξ = map′
  (λ (e₁₀ , e₀₁) →
     caseX A , caseQ A , caseQ′ A B ,
     BoolValued-caseX A , BoolValued-caseQ A , BoolValued-caseQ′ A B ,
     e₁₀ , e₀₁)
  (λ (X , Q , Q′ , _ , _ , _ , e₁₀ , e₀₁) → case-complete A B X Q Q′ e₁₀ e₀₁)
  ((A ≈?[ pow M ] ((¼ ·ᴾ caseX A) +ᴾ (½ ·ᴾ caseQ A))) ×?
   (B ≈?[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ caseX A)) +ᴾ (½ ·ᴾ caseQ′ A B))))
  where
  A = q₁₀ (phase ξ)
  B = q₀₁ (phase ξ)

CaseAll? : (ξ : PathSum n k (suc (suc m))) → Dec (CaseAll ξ)
CaseAll? ξ = Internal₁? ξ ×? (q₁₁ (phase ξ) ≈?[ pow M ] κ ½) ×? CaseQᴳ? ξ

-- The side conditions on a given quotient are decidable as well --
-- being Boolean-valued is being idempotent coefficient by coefficient
-- (Polynomial.Boolean.BoolValued⇔idem) -- although the matcher never
-- needs them: the canonical quotients satisfy them by construction.

BoolValued? : (Q : Poly n m) → Dec (BoolValued Q)
BoolValued? Q = map′ (Equivalence.from (BoolValued⇔idem Q))
                     (Equivalence.to (BoolValued⇔idem Q))
                     (allMon? (λ γ → ((Q *ᴾ Q) -ᴾ Q) γ ≟ 0ℤ))

Absent? : (v : Var n m) (Q : Poly n m) → Dec (Absent v Q)
Absent? v Q = allMon? (λ γ → (v ∈ᵐ? γ) →? (Q γ ≟ 0ℤ))


------------------------------------------------------------------------
-- Whether a head rule applies

HeadStepᴳ : PathSum n k m → Set
HeadStepᴳ {n} ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ζ : PathSum n k′ m′) → ξ ⟶ᴳ ζ

-- Every head rule needs y₀ internal; which of the others can apply
-- depends on the normalisation ([HH] always, [ω] from 1, [Elim] and
-- [Case] from 2) and on the number of path variables ([Case] from 2).

private
  internal₀ : {ξ : PathSum n k (suc m)} {ζ : PathSum n k′ m′} →
              ξ ⟶ᴳ ζ → Internal₀ ξ
  internal₀ (elimᴳ _ _ o)                   = o
  internal₀ (ωᴳ _ _ _ _ o)                  = o
  internal₀ (hhᴳ _ _ _ _ _ _ o)             = o
  internal₀ (caseᴳ _ _ _ _ _ _ _ _ _ _ o _) = o

  stuck₀ : {ξ : PathSum n 0 (suc m)} {ζ : PathSum n k′ m′} →
           ¬ HHQᴳ ξ → ¬ (ξ ⟶ᴳ ζ)
  stuck₀ ¬h (hhᴳ _ i Q bQ absQ eq _) = ¬h (i , Q , bQ , absQ , eq)

  stuck₁ : {ξ : PathSum n 1 (suc m)} {ζ : PathSum n k′ m′} →
           ¬ ΩQᴳ ξ → ¬ HHQᴳ ξ → ¬ (ξ ⟶ᴳ ζ)
  stuck₁ ¬ω ¬h (ωᴳ _ Q bQ eq _)          = ¬ω (Q , bQ , eq)
  stuck₁ ¬ω ¬h (hhᴳ _ i Q bQ absQ eq _)  = ¬h (i , Q , bQ , absQ , eq)

  -- One path variable: [Case] cannot apply.
  stuck₂ : {ξ : PathSum n (suc (suc k)) 1} {ζ : PathSum n k′ m′} →
           ¬ ElimQ ξ → ¬ ΩQᴳ ξ → ¬ HHQᴳ ξ → ¬ (ξ ⟶ᴳ ζ)
  stuck₂ ¬e ¬ω ¬h (elimᴳ _ eq _)           = ¬e eq
  stuck₂ ¬e ¬ω ¬h (ωᴳ _ Q bQ eq _)         = ¬ω (Q , bQ , eq)
  stuck₂ ¬e ¬ω ¬h (hhᴳ _ i Q bQ absQ eq _) = ¬h (i , Q , bQ , absQ , eq)

  stuck₃ : {ξ : PathSum n (suc (suc k)) (suc (suc m))}
           {ζ : PathSum n k′ m′} →
           ¬ ElimQ ξ → ¬ ΩQᴳ ξ → ¬ HHQᴳ ξ → ¬ CaseAll ξ → ¬ (ξ ⟶ᴳ ζ)
  stuck₃ ¬e ¬ω ¬h ¬c (elimᴳ _ eq _)           = ¬e eq
  stuck₃ ¬e ¬ω ¬h ¬c (ωᴳ _ Q bQ eq _)         = ¬ω (Q , bQ , eq)
  stuck₃ ¬e ¬ω ¬h ¬c (hhᴳ _ i Q bQ absQ eq _) = ¬h (i , Q , bQ , absQ , eq)
  stuck₃ ¬e ¬ω ¬h ¬c
         (caseᴳ _ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ _ o₁) =
    ¬c (o₁ , e₁₁ , X , Q , Q′ , bX , bQ , bQ′ , e₁₀ , e₀₁)

  by-case : (ξ : PathSum n (suc (suc k)) (suc m)) → Internal₀ ξ →
            ¬ ElimQ ξ → ¬ ΩQᴳ ξ → ¬ HHQᴳ ξ → Dec (HeadStepᴳ ξ)
  by-case {m = zero}  ξ o ¬e ¬ω ¬h =
    no λ (_ , _ , _ , s) → stuck₂ ¬e ¬ω ¬h s
  by-case {m = suc m} ξ o ¬e ¬ω ¬h = case CaseAll? ξ of λ where
    (yes (o₁ , e₁₁ , X , Q , Q′ , bX , bQ , bQ′ , e₁₀ , e₀₁)) →
      yes (_ , _ , _ , caseᴳ ξ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ o o₁)
    (no ¬c) → no λ (_ , _ , _ , s) → stuck₃ ¬e ¬ω ¬h ¬c s

  by-norm : (ξ : PathSum n k (suc m)) → Internal₀ ξ → ¬ HHQᴳ ξ →
            Dec (HeadStepᴳ ξ)
  by-norm {k = zero}        ξ o ¬h = no λ (_ , _ , _ , s) → stuck₀ ¬h s
  by-norm {k = suc zero}    ξ o ¬h = case ΩQᴳ? ξ of λ where
    (yes (Q , bQ , eq)) → yes (_ , _ , _ , ωᴳ ξ Q bQ eq o)
    (no ¬ω)             → no λ (_ , _ , _ , s) → stuck₁ ¬ω ¬h s
  by-norm {k = suc (suc k)} ξ o ¬h = case ΩQᴳ? ξ of λ where
    (yes (Q , bQ , eq)) → yes (_ , _ , _ , ωᴳ ξ Q bQ eq o)
    (no ¬ω)             → case ElimQ? ξ of λ where
      (yes eq) → yes (_ , _ , _ , elimᴳ ξ eq o)
      (no ¬e)  → by-case ξ o ¬e ¬ω ¬h

-- Some head rule applies, or none does.

headᴳ? : (ξ : PathSum n k m) → Dec (HeadStepᴳ ξ)
headᴳ? {m = zero}  ξ = no λ { (_ , _ , _ , ()) }
headᴳ? {m = suc m} ξ = case Internal₀? ξ of λ where
  (no ¬o) → no λ (_ , _ , _ , s) → ¬o (internal₀ s)
  (yes o) → case HHQᴳ? ξ of λ where
    (yes (i , Q , bQ , absQ , eq)) →
      yes (_ , _ , _ , hhᴳ ξ i Q bQ absQ eq o)
    (no ¬h) → by-norm ξ o ¬h


------------------------------------------------------------------------
-- Proposition 3.2 for the head calculus

-- No rule of figure 2 applies at the head (y₀, and (y₀ , y₁) for
-- [Case]).

Irreducibleᴳ : PathSum n k m → Set
Irreducibleᴳ {n} ξ = ∀ {k′ m′} {ζ : PathSum n k′ m′} → ¬ (ξ ⟶ᴳ ζ)

-- Rewrite at the head while a rule applies; every rule removes a path
-- variable (Reduction.General.⟶ᴳ-dec), so this stops.

normal-formᴳ : (ξ : PathSum n k m) →
               ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                 (ξ ⟶ᴳ* ξ′) × Irreducibleᴳ ξ′
normal-formᴳ {n = n} ξ = go ξ (SN-by-< {R = _⟶ᴳ_} ⟶ᴳ-dec ξ)
  where
  NF : ∀ {k m} → PathSum n k m → Set
  NF ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
           (ξ ⟶ᴳ* ξ′) × Irreducibleᴳ ξ′

  go : ∀ {k m} (ξ : PathSum n k m) → SN _⟶ᴳ_ ξ → NF ξ
  go ξ (sn next) with headᴳ? ξ
  ... | no ¬s                  = _ , _ , ξ , εᴳ , λ s → ¬s (_ , _ , _ , s)
  ... | yes (_ , _ , ζ , s) with go ζ (next s)
  ...   | k′ , m′ , ξ′ , steps , irr = k′ , m′ , ξ′ , s ◅ᴳ steps , irr


------------------------------------------------------------------------
-- A head step survives front zero

-- front zero ξ is ξ with nothing moved: the quarters of its phase are,
-- coefficient by coefficient, those of ξ, by definition, and only the
-- absence of y₀ and y₁ from the outputs needs converting.

headᴳ-zero : {χ : PathSum n k (suc m)} →
             HeadStepᴳ χ → HeadStepᴳ (front zero χ)
headᴳ-zero {χ = χ} (_ , _ , _ , elimᴳ _ eq o) =
  _ , _ , _ ,
  elimᴳ (front zero χ) eq (λ w → NoVar-front zero (out χ w) (o w))
headᴳ-zero {χ = χ} (_ , _ , _ , ωᴳ _ Q bQ eq o) =
  _ , _ , _ ,
  ωᴳ (front zero χ) Q bQ eq (λ w → NoVar-front zero (out χ w) (o w))
headᴳ-zero {χ = χ} (_ , _ , _ , hhᴳ _ i Q bQ absQ eq o) =
  _ , _ , _ ,
  hhᴳ (front zero χ) i Q bQ absQ eq
      (λ w → NoVar-front zero (out χ w) (o w))
headᴳ-zero {χ = χ}
           (_ , _ , _ , caseᴳ _ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ o₀ o₁) =
  _ , _ , _ ,
  caseᴳ (front zero χ) X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁
        (λ w → NoVar-front zero (out χ w) (o₀ w))
        (λ w → NoVar-front-suc zero zero (out χ w) (o₁ w))


------------------------------------------------------------------------
-- Irreducible path-sums

-- No rule of figure 2 applies at any path variable, nor [Case] at any
-- pair.

Irreducibleᶠ : PathSum n k m → Set
Irreducibleᶠ {n} ξ = ∀ {k′ m′} {ζ : PathSum n k′ m′} → ¬ (ξ ⟶ᶠ ζ)

-- In particular none of the linear rules does.

Irreducibleᶠ⇒Irreducible : {ξ : PathSum n k m} →
                           Irreducibleᶠ ξ → Irreducible ξ
Irreducibleᶠ⇒Irreducible irr s = irr (⟶ᵍ⇒⟶ᶠ s)

-- Irreducibility is a statement about the head rules at every double
-- renumbering.

Irreducibleᶠ⇒head : (ξ : PathSum n k (suc m)) → Irreducibleᶠ ξ →
                    ∀ j j′ → ¬ HeadStepᴳ (front j′ (front j ξ))
Irreducibleᶠ⇒head ξ irr j j′ (_ , _ , _ , s) = irr (at j (at j′ s))

private
  none : (ξ : PathSum n k (suc m)) →
         ¬ (∃ λ j → ∃ λ j′ → HeadStepᴳ (front j′ (front j ξ))) →
         Irreducibleᶠ ξ
  none ξ ¬any (plain (plain s)) =
    ¬any (zero , zero ,
          headᴳ-zero {χ = front zero ξ}
            (headᴳ-zero {χ = ξ} (_ , _ , _ , s)))
  none ξ ¬any (plain (at j s))  =
    ¬any (j , zero , headᴳ-zero {χ = front j ξ} (_ , _ , _ , s))
  none ξ ¬any (at j (plain s))  =
    ¬any (j , zero , headᴳ-zero {χ = front j ξ} (_ , _ , _ , s))
  none ξ ¬any (at j (at j′ s))  = ¬any (j , j′ , _ , _ , _ , s)

head⇒Irreducibleᶠ : (ξ : PathSum n k (suc m)) →
                    (∀ j j′ → ¬ HeadStepᴳ (front j′ (front j ξ))) →
                    Irreducibleᶠ ξ
head⇒Irreducibleᶠ ξ h = none ξ (λ (j , j′ , s) → h j j′ s)

-- Either some rule applies, or none does: try every head rule at
-- every double renumbering.

stepᶠ? : (ξ : PathSum n k m) →
         (∃ λ k′ → ∃ λ m′ → ∃ λ (ζ : PathSum n k′ m′) → ξ ⟶ᶠ ζ) ⊎
         Irreducibleᶠ ξ
stepᶠ? {m = zero}  ξ = inj₂ λ { (plain (plain ())) }
stepᶠ? {m = suc m} ξ
  with any? (λ j → any? (λ j′ → headᴳ? (front j′ (front j ξ))))
... | yes (j , j′ , _ , _ , _ , s) = inj₁ (_ , _ , _ , at j (at j′ s))
... | no ¬any                      = inj₂ (none ξ ¬any)

irreducibleᶠ? : (ξ : PathSum n k m) → Dec (Irreducibleᶠ ξ)
irreducibleᶠ? ξ with stepᶠ? ξ
... | inj₁ (_ , _ , _ , s) = no λ irr → irr s
... | inj₂ irr             = yes irr


------------------------------------------------------------------------
-- Proposition 3.2: every path-sum reduces to an irreducible one

-- Rewrite while a rule applies; the recursion is on strong
-- normalisation (PathSum.Full.⟶ᶠ-SN), so it stops.

normal-formᶠ : (ξ : PathSum n k m) →
               ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                 (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′
normal-formᶠ {n = n} ξ = go ξ (⟶ᶠ-SN ξ)
  where
  NF : ∀ {k m} → PathSum n k m → Set
  NF ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
           (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′

  go : ∀ {k m} (ξ : PathSum n k m) → SN _⟶ᶠ_ ξ → NF ξ
  go ξ (sn next) with stepᶠ? ξ
  ... | inj₂ irr              = _ , _ , ξ , εᶠ , irr
  ... | inj₁ (_ , _ , ζ , s) with go ζ (next s)
  ...   | k′ , m′ , ξ′ , steps , irr = k′ , m′ , ξ′ , s ◅ᶠ steps , irr
