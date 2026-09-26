------------------------------------------------------------------------
-- Presentations of groups
--
-- The results for circuits over {H, CNOT, R_k, R_k†} (Amy, QPL 2018,
-- lemma 2.5, definition 2.9, propositions 2.10 and 2.14, lemma 4.1,
-- and corollary 4.4's characterisation for the Clifford ones)
--
-- PathSum.Theorems states the results of the path-sum calculus for
-- Clifford circuits over {H, S, CZ}.  This module states those of the
-- Clifford+R_k fragment of section 2.2, over the paper's own gate set
-- {H, CNOT, R_k} together with the R_k† of definition 2.9.
-- Definition 2.9 is PathSum.CRK.Circuit's ⟦_⟧, which runs an
-- interpretation state -- a phase, and a Z₂-linear form on each wire --
-- through the circuit.  Lemma 2.5 for those forms (PathSum.Linear)
-- gives the values of their liftings, which is what the outputs of
-- ⟦ C ⟧ are.  Proposition 2.10 (PathSum.CRK.Semantics) is that ⟦ C ⟧
-- computes the product of the gate matrices, and its columns have unit
-- norm in the trace form, so lemma 4.1 applies to it: ⟦ C ⟧ is the
-- identity exactly when its isometry restriction is, which is to say
-- exactly when every diagonal entry of the circuit's matrix is 1.
--
-- Proposition 2.14 is stated as it holds.  The paper bounds the degree
-- of the phase polynomial by k, arguing that every gate has a phase of
-- order at most k; but the Hadamard's phase ½ x y has order 2 whatever
-- k is.  So the bound is max(2, k) (prop-2-14), the paper's form needs
-- 2 ≤ k (prop-2-14-k), and at k = 1 the one-gate circuit H refutes it,
-- for the order and for the degree alike (prop-2-14-needs-2,
-- prop-2-14-deg-needs-2, prop-2-14-false-at-1).  The degree bound holds
-- only modulo the integers, as the paper's "coefficients in D/Z"
-- permits: the phase of ⟦ C ⟧ can have integral terms of higher degree.
--
-- Two departures, as in PathSum.CRK.Circuit: CNOT carries a proof that
-- its control and target differ, which the paper leaves implicit; and
-- R k denotes R_k only when k ≤ M = 3 + M₀ -- for larger k it is read
-- as R_M, on both sides of proposition 2.10 alike (Rk-order,
-- Rk-primitive).
--
-- Corollary 4.4 by the paper's route -- after a CNOT the outputs of
-- ⟦ C ⟧ are sums of variables, so reifying its isometry restriction
-- needs Gaussian elimination -- is PathSum.Gauss.Corollary.  This
-- package has the other route, for the Clifford circuits here (level
-- at most 2): PathSum.CRK.Compile compiles the circuit to {H, S, CZ},
-- whose path-sum is equivalent to ⟦ C ⟧, and reduces the compiled
-- circuit's restriction (corollary-4-4-compiled and its two
-- companions).
--
-- Elsewhere: ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧ with the path-sum composition of
-- definition 2.6 is PathSum.Compose.CRK, and unitarity of ⟦ C ⟧ is
-- PathSum.CRK.Unitarity.  Not formalised for these circuits: corollary
-- 2.15 and every complexity claim.  Whether ⟦ C ⟧ is the identity is decided
-- for every circuit (circuit-decidable), but by an exhaustive search
-- over the diagonal of the circuit's matrix -- an elementary fact, not
-- the reduction of corollary 4.4.
--
-- Each section's banner names the modules its results come from;
-- results proved here from them are stated with their proofs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _≤_; _∸_; _⊔_; _^_; z≤n; s≤s)

module PathSum.CRK.Theorems (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; if_then_else_; _xor_)
open import Data.Fin.Base using (Fin; zero)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (0ℤ; +_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (≤-reflexive; _≟_)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; same-≗)
open import PathSum.AssignSum using (Σᶻ)
open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.CRK.Circuit M using
  (H; Circuit; norm; level; State; run; paths; ⟦_⟧; Deg≤)
open import PathSum.CRK.Compile M₀ using (compile)
open import PathSum.CRK.Semantics M₀ using (applyᴬ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale; scale-map)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.Isometry M₀ using (WellFormed; Restriction-id)
open import PathSum.Linear using (Lin; parᵐ; valᴸ; liftᴸ)
open import PathSum.Norm M₀ using (‖_‖²)
open import PathSum.Order M using (Ord≤; pow)
open import PathSum.Polynomial using
  (Mon; ∥_∥; eval; liftXor; μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Reduction M using (½; _⟶*_)

import PathSum.Circuit
import PathSum.CircuitAmp
import PathSum.CRK.Circuit
import PathSum.CRK.Compile
import PathSum.CRK.Semantics
import PathSum.Decide
import PathSum.Isometry
import PathSum.Linear

private
  module Circ = PathSum.Circuit M
  module CAmp = PathSum.CircuitAmp M₀
  module Cmp  = PathSum.CRK.Compile M₀
  module Crk  = PathSum.CRK.Circuit M
  module Sem  = PathSum.CRK.Semantics M₀
  module Dcd  = PathSum.Decide M₀
  module Isom = PathSum.Isometry M₀
  module Lnr  = PathSum.Linear

  variable
    n m k′ : ℕ


------------------------------------------------------------------------
-- Lemma 2.5 for linear forms (PathSum.Linear)

-- The lifting of the form c ⊕ ⨁S takes the form's value, and every
-- coefficient of degree at least 2 is even: modulo 2 it is linear.

eval-liftXor : (c : Bool) (S : Mon n m) (x : Fin n → Bool)
               (y : Fin m → Bool) →
               eval (liftXor c S) x y ≡ [ c xor parᵐ S x y ]ᶻ
eval-liftXor = Lnr.eval-liftXor

eval-liftᴸ : (l : Lin n m) (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (liftᴸ l) x y ≡ [ valᴸ l x y ]ᶻ
eval-liftᴸ = Lnr.eval-liftᴸ

liftXor-linear : (c : Bool) (S γ : Mon n m) → 2 ≤ ∥ γ ∥ →
                 (+ 2) ∣ liftXor c S γ
liftXor-linear = Lnr.liftXor-linear


------------------------------------------------------------------------
-- Definition 2.9 (PathSum.CRK.Circuit)

-- One path variable for each Hadamard, so the normalisation is
-- 1/√2^m for m path variables, as definition 2.1 has it.

paths≡norm : (C : Circuit n) → paths C ≡ norm C
paths≡norm = Crk.paths≡norm

-- ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧, at the level of the interpretation.

run-++ : (C D : Circuit n) (st : State n m) →
         run (C ++ D) st ≡ run D (proj₂ (run C st))
run-++ = Crk.run-++

-- R k multiplies by ζ^(2^(M-k)), a primitive 2^k-th root of unity when
-- k ≤ M.

Rk-order : ∀ {k} → k ≤ M → pow (M ∸ k) * pow k ≡ pow M
Rk-order = Crk.Rk-order

Rk-primitive : ∀ {k} → 1 ≤ k → k ≤ M → pow (M ∸ k) * pow (k ∸ 1) ≡ ½
Rk-primitive = Crk.Rk-primitive

-- "Each of the outputs of a canonical path-sum is linear": every
-- coefficient of degree at least 2 is even.

out-linear : (C : Circuit n) (w : Fin n) (γ : Mon n (paths C)) →
             2 ≤ ∥ γ ∥ → (+ 2) ∣ out ⟦ C ⟧ w γ
out-linear = Crk.out-linear


------------------------------------------------------------------------
-- Proposition 2.10 (PathSum.CRK.Semantics)

-- The entry of ⟦ C ⟧ from x to z is the z-th amplitude of the column
-- the gates of C produce from the basis column δ x, each acting by its
-- own matrix: both unnormalised by the same √2^(norm C).

prop-2-10 : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴬ C (δ x) z
prop-2-10 = Sem.prop-2-10

-- Once divided by √2^(norm C), every column has norm 1 in the trace
-- form of PathSum.Norm.

circuit-unit-columns : (C : Circuit n) (x : Assign n) →
                       Σᶻ (λ z → ‖ amp ⟦ C ⟧ x z ‖²) ≡ + (2 ^ norm C)
circuit-unit-columns = Sem.⟦⟧-unit-columns


------------------------------------------------------------------------
-- Lemma 4.1 at a circuit (PathSum.CRK.Semantics, PathSum.Isometry)

-- ⟦ C ⟧ satisfies the column bound lemma 4.1 asks for.

circuit-WellFormed : (C : Circuit n) → WellFormed ⟦ C ⟧
circuit-WellFormed C x = ≤-reflexive (Sem.⟦⟧-unit-columns C x)

-- "⟦ C ⟧ is the identity" means what it should: the circuit's matrix,
-- computed gate by gate, is the identity matrix.  (idPS's entries are
-- the basis columns, as those of PathSum.Circuit's starting state
-- are.)

circuit-≋-id : (C : Circuit n) →
               (⟦ C ⟧ ≋ idPS ⇔
                (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)))
circuit-≋-id C = mk⇔
  (λ eq x z i → trans (sym (Sem.prop-2-10 C x z i))
    (trans (eq x z i) (scale-map (norm C) (CAmp.ampˢ-init x z) i)))
  (λ eq x z i → trans (Sem.prop-2-10 C x z i)
    (trans (eq x z i) (sym (scale-map (norm C) (CAmp.ampˢ-init x z) i))))

-- Lemma 4.1: ⟦ C ⟧ is the identity exactly when its isometry
-- restriction is.

lemma-4-1-circuit : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ Restriction-id ⟦ C ⟧)
lemma-4-1-circuit C = Isom.lemma-4-1 ⟦ C ⟧ (circuit-WellFormed C)

-- Read through proposition 2.10: the circuit is the identity exactly
-- when every diagonal entry of its matrix is 1, once normalised.

identity-iff-diagonal : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔ (∀ x → applyᴬ C (δ x) x ≐ scale (norm C) (zpow 0ℤ)))
identity-iff-diagonal C = mk⇔
  (λ eq x i → trans (sym (Sem.prop-2-10 C x x i))
                    (Equivalence.to (lemma-4-1-circuit C) eq x i))
  (λ d → Equivalence.from (lemma-4-1-circuit C) (λ x i →
           trans (Sem.prop-2-10 C x x i) (d x i)))


------------------------------------------------------------------------
-- Deciding the identity, elementarily (PathSum.Decide)

-- Equality of amplitudes is decidable coordinate by coordinate, and
-- the diagonal has finitely many entries.  This is a finite search,
-- not the reduction of corollary 4.4.

private
  ≐? : (a b : Amp) → Dec (a ≐ b)
  ≐? a b = all? (λ i → a i ≟ b i)

  Diag : Circuit n → Assign n → Set
  Diag C x = applyᴬ C (δ x) x ≐ scale (norm C) (zpow 0ℤ)

  δ-≗ : {x x′ z z′ : Assign n} → (∀ i → x i ≡ x′ i) →
        (∀ i → z i ≡ z′ i) → δ x z ≐ δ x′ z′
  δ-≗ {x = x} {x′} {z} {z′} x≗ z≗ i =
    cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
         (same-≗ {x = x} {x′ = x′} {z = z} {z′ = z′} x≗ z≗)

  diag-≗ : (C : Circuit n) {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
           Diag C x → Diag C x′
  diag-≗ C {x} {x′} x≗ d i = trans (sym (moved i)) (d i)
    where
    moved : applyᴬ C (δ x) x ≐ applyᴬ C (δ x′) x′
    moved j = trans
      (Sem.applyᴬ-cong C {δ x} {δ x′}
        (λ z → δ-≗ {x = x} {x′} {z} {z} x≗ (λ _ → refl)) x j)
      (Sem.applyᴬ-resp C {δ x′}
        (λ z z′ zz → δ-≗ {x = x′} {x′} {z} {z′} (λ _ → refl) zz) x x′ x≗ j)

circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidable C = settle (Dcd.search (Diag C)
  (λ x → ≐? (applyᴬ C (δ x) x) (scale (norm C) (zpow 0ℤ))) (diag-≗ C))
  where
  settle : (∀ x → Diag C x) ⊎ ∃ (λ x → ¬ Diag C x) → Dec (⟦ C ⟧ ≋ idPS)
  settle (inj₁ all)       = yes (Equivalence.from (identity-iff-diagonal C) all)
  settle (inj₂ (x , bad)) =
    no (λ eq → bad (Equivalence.to (identity-iff-diagonal C) eq x))


------------------------------------------------------------------------
-- Proposition 2.14, with the bound it actually has (PathSum.CRK.Circuit)

-- The order of the phase is at most max(2, k), k the largest R_k in the
-- circuit; the degree, read modulo the integers, likewise.

prop-2-14 : (C : Circuit n) → Ord≤ (2 ⊔ level C) (phase ⟦ C ⟧)
prop-2-14 = Crk.prop-2-14

prop-2-14-deg : (C : Circuit n) → Deg≤ (2 ⊔ level C) (phase ⟦ C ⟧)
prop-2-14-deg = Crk.prop-2-14-deg

-- The paper's statement, which needs 2 ≤ k.

prop-2-14-k : ∀ k → 2 ≤ k → (C : Circuit n) → level C ≤ k →
              Ord≤ k (phase ⟦ C ⟧)
prop-2-14-k = Crk.prop-2-14-k

prop-2-14-k-deg : ∀ k → 2 ≤ k → (C : Circuit n) → level C ≤ k →
                  Deg≤ k (phase ⟦ C ⟧)
prop-2-14-k-deg = Crk.prop-2-14-k-deg

-- At k = 1 it fails: one Hadamard has phase ½ x y, of order and degree
-- 2.

prop-2-14-needs-2 : ¬ Ord≤ 1 (phase ⟦ H {1} zero ∷ [] ⟧)
prop-2-14-needs-2 = Crk.prop-2-14-needs-2 (s≤s z≤n)

prop-2-14-deg-needs-2 : ¬ Deg≤ 1 (phase ⟦ H {1} zero ∷ [] ⟧)
prop-2-14-deg-needs-2 =
  Crk.prop-2-14-deg-needs-2 (s≤s z≤n)

prop-2-14-false-at-1 :
  ¬ (∀ (C : Circuit 1) → level C ≤ 1 → Deg≤ 1 (phase ⟦ C ⟧))
prop-2-14-false-at-1 =
  Crk.prop-2-14-false-at-1 (s≤s z≤n)


------------------------------------------------------------------------
-- Corollary 4.4 for the Clifford circuits, through {H, S, CZ}
-- (PathSum.CRK.Compile, PathSum.Corollary)

-- A circuit of level at most 2 compiles to one over {H, S, CZ} whose
-- path-sum is equivalent to its own: CNOT c t becomes H_t ; CZ ; H_t,
-- twice CNOT, and the extra normalisation pays for the factor.

compile-≋ : (C : Circuit n) → level C ≤ 2 → ⟦ C ⟧ ≋ Circ.⟦ compile C ⟧
compile-≋ = Cmp.compile-≋

-- Reducing the compiled circuit's restriction either refutes the
-- circuit or ends without path variables, at a path-sum whose being
-- the identity is exactly the circuit's.  This is not the paper's
-- route, which reduces the restriction of ⟦ C ⟧ itself.

corollary-4-4-compiled : (C : Circuit n) → level C ≤ 2 →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     (Circ.⟦ compile C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-compiled = Cmp.corollary-4-4-compiled

-- Whatever such chain ends without path variables, ⟦ C ⟧ is the
-- identity exactly when that endpoint is syntactically |x⟩ ↦ |x⟩.

corollary-4-4-any-compiled : (C : Circuit n) → level C ≤ 2 →
  {ξ′ : PathSum n k′ 0} → Circ.⟦ compile C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-any-compiled = Cmp.corollary-4-4-any-compiled

corollary-4-4-syntactic-compiled : (C : Circuit n) → level C ≤ 2 →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (Circ.⟦ compile C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic-compiled = Cmp.corollary-4-4-syntactic-compiled
