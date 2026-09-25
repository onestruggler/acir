------------------------------------------------------------------------
-- Presentations of groups
--
-- The results of the path-sum calculus, at the denotation in Z[ζ]
--
-- PathSum.Clifford proves section 4.3 over the semantic interface of
-- PathSum.Semantics, and PathSum.Denotation builds a value of that
-- interface out of the cyclotomic integers.  Instantiating the one at
-- the other is what makes the section unconditional; this module
-- states the results in that form.  Lemma 4.1 (PathSum.Isometry) and
-- proposition 2.10 over {H, S, CZ} (PathSum.CircuitSemantics) then
-- carry corollary 4.4 from the restricted path-sum it reduces back to
-- the circuit itself, and PathSum.Syntactic shows the end of the
-- reduction is a syntactic test: a Clifford circuit is the identity
-- exactly when its restriction reduces to a path-sum with no
-- normalisation and the identity's polynomials -- the content of
-- corollary 4.4's proof (corollary-4-4-any, corollary-4-4-syntactic).
-- The corollary's own statement, decidability in polynomial time, is
-- not formalised.
--
-- Around that core: all four rules of figure 2, [Case] included and
-- with Boolean-valued quotients, at the first path variables
-- (PathSum.Reduction.General), and the linear [Elim], [ω] and [HH] at
-- any internal path variable (PathSum.Anywhere) -- each calculus sound,
-- and no chain longer than the path variables it starts with; lemma 2.5
-- for every Boolean polynomial; definition 2.4 (PathSum.PartialIsometry),
-- under which lemma 4.1 holds as the paper states it, with circuits
-- over {H, S, CZ} proved isometries; equivalence of two such circuits,
-- decided through the miter; and the paper's own gate set
-- {H, CNOT, R_k}: definition 2.9, propositions 2.10 and 2.14, and the
-- characterisation of corollary 4.4 for its Clifford circuits, reached
-- by compiling them to {H, S, CZ}.
--
-- Two statements of the paper are false as printed.  What is proved is
-- the corrected statement, next to a checked counterexample: lemma 4.2
-- needs Q odd at some input, not merely non-zero (Q = 2x₁ has ½y₀Q
-- integral), and proposition 2.14's bound is max(2, k), not k (a
-- Hadamard's phase ½xy has order 2 whatever k is).
--
-- Not formalised: the polynomial time bounds (proposition 3.2,
-- corollaries 2.15 and 4.4); [Case] and Boolean-valued quotients at a
-- path variable other than the first; the Gaussian elimination by which
-- the paper's proof of corollary 4.4 reifies the restriction of a
-- circuit with CNOT (the corollary is reached another way for those);
-- composition of path-sums (definition 2.6, proposition 2.7) and
-- remark 2.8; constant inputs; equivalence of circuits with CNOT or
-- R_k; and UU† = I, so no path-sum is claimed unitary -- ⟦ C ⟧ is
-- proved an isometry.
--
-- Each section's banner names the modules its results come from;
-- results proved here from them are stated with their proofs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _<_)

module PathSum.Theorems (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (_+_; _^_; _≤_; _⊔_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (⊥)
open import Data.Integer.Base using (0ℤ; +_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.List.Base using (_++_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; no; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.AssignSum using (Σᶻ)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Cyclotomic M₀ using (_≐_; scale; scale-map)
open import PathSum.Norm M₀ using (‖_‖²)
open import PathSum.Order M
open import PathSum.Polynomial
open import PathSum.Reduction M hiding (⟶*-length)

import PathSum.Circuit
module Circ = PathSum.Circuit M

import PathSum.Reduction
module Red = PathSum.Reduction M

import PathSum.Denotation
module Den = PathSum.Denotation M₀

open Den using (Assign; hits; amp; _≋_; semantics)

import PathSum.Clifford
module Cliff = PathSum.Clifford M₀ semantics

import PathSum.Identity
module Idn = PathSum.Identity M₀

import PathSum.Isometry
module Isom = PathSum.Isometry M₀

open Isom using (WellFormed; Restriction-id)

import PathSum.CircuitAmp
module CAmp = PathSum.CircuitAmp M₀

import PathSum.CircuitSemantics
module CSem = PathSum.CircuitSemantics M₀

open CSem using (Column; δ; applyᴬ)

import PathSum.Decide
module Dcd = PathSum.Decide M₀

import PathSum.Syntactic
module Syn = PathSum.Syntactic M₀

import PathSum.Corollary
module Cor = PathSum.Corollary M₀

open import PathSum.Polynomial.Boolean using (BoolValued; liftᴮ)
import PathSum.Polynomial.Boolean
module PB = PathSum.Polynomial.Boolean

open import PathSum.Reorder using (front)

import PathSum.Anywhere
module Any = PathSum.Anywhere M
open Any using (_⟶ᵍ_; _⟶ᵍ*_; lenᵍ; SN)

import PathSum.Anywhere.Sound
module AnyS = PathSum.Anywhere.Sound M₀

import PathSum.Anywhere.Clifford
module AnyC = PathSum.Anywhere.Clifford M₀

import PathSum.Anywhere.Corollary
module AnyCor = PathSum.Anywhere.Corollary M₀

import PathSum.Anywhere.Match
module AnyM = PathSum.Anywhere.Match M
open AnyM using (Irreducible)

import PathSum.Reduction.General
module Gen = PathSum.Reduction.General M
open Gen using (_⟶ᴳ_; _⟶ᴳ*_; lenᴳ)

import PathSum.Reduction.Sound
module GenS = PathSum.Reduction.Sound M₀

import PathSum.Reduction.GeneralCorollary
module GenCor = PathSum.Reduction.GeneralCorollary M₀

import PathSum.Interference
module Intf = PathSum.Interference M₀

import PathSum.PartialIsometry
module PIso = PathSum.PartialIsometry M₀
open PIso using (Isometric; PartialIsometric)

import PathSum.Unitarity
module Unit = PathSum.Unitarity M₀

open import PathSum.Adjoint M using (_†)

import PathSum.Miter
module Mit = PathSum.Miter M₀

import PathSum.Equivalence
module Eqv = PathSum.Equivalence M₀

import PathSum.CRK.Circuit
module K = PathSum.CRK.Circuit M

import PathSum.CRK.Semantics
module KSem = PathSum.CRK.Semantics M₀

import PathSum.CRK.Compile
module KC = PathSum.CRK.Compile M₀

import PathSum.CRK.Theorems
module KT = PathSum.CRK.Theorems M₀

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Definition 2.3 is an equivalence (PathSum.Denotation)

≋-refl : {ξ : PathSum n k m} → ξ ≋ ξ
≋-refl {ξ = a} = Den.≋-refl {ξ = a}

≋-sym : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ≋ ζ → ζ ≋ ξ
≋-sym {ξ = a} {ζ = b} = Den.≋-sym {ξ = a} {ζ = b}

≋-trans : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
          {χ : PathSum n k″ m″} → ξ ≋ ζ → ζ ≋ χ → ξ ≋ χ
≋-trans {ξ = a} {ζ = b} {χ = d} =
  Den.≋-trans {ξ = a} {ζ = b} {χ = d}


------------------------------------------------------------------------
-- Lemma 2.5 for every Boolean polynomial (PathSum.Polynomial.Boolean)

-- The lifting of a polynomial over Z₂ into one over D, folded over its
-- odd monomials by the paper's recursion (P ⊕ Q lifts to P̄ + Q̄ - 2P̄Q̄),
-- is {0,1}-valued and agrees with the original modulo 2 at every point.
-- It is also the only such polynomial, which the paper leaves implicit:
-- two {0,1}-valued polynomials with the same parities everywhere have
-- the same coefficients (Möbius inversion).

lemma-2-5 : (f : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
            (+ 2) ∣ (eval (liftᴮ f) x y - eval f x y)
lemma-2-5 = PB.lemma-2-5

liftᴮ-BoolValued : (f : Poly n m) → BoolValued (liftᴮ f)
liftᴮ-BoolValued = PB.BoolValued-liftᴮ

lift-unique : (P Q : Poly n m) → BoolValued P → BoolValued Q →
              (∀ (x : Fin n → Bool) (y : Fin m → Bool) →
                 (+ 2) ∣ (eval P x y - eval Q x y)) →
              ∀ γ → P γ ≡ Q γ
lift-unique = PB.lift-unique


------------------------------------------------------------------------
-- Definition 2.9 and proposition 2.10, over {H, S, CZ}
-- (PathSum.Circuit, PathSum.CircuitSemantics, PathSum.Unitarity)

-- ⟦ C ⟧ is the path-sum of the circuit, every Hadamard allocating a
-- path variable.  Its entry from x to z is the z-th amplitude of the
-- column the gates of C produce from the basis column δ x, each
-- acting by its own matrix: the path-sum computes the circuit's
-- operator, both unnormalised by the same √2^(norm C).

prop-2-10 : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴬ C (δ x) z
prop-2-10 = CSem.prop-2-10

-- Once divided by √2^(norm C), every column of that operator has norm
-- 1 in the trace form of PathSum.Norm -- the bound lemma 4.1 asks for
-- (WellFormed).

circuit-unit-columns : (C : Circuit n) (x : Assign n) →
                       Σᶻ (λ z → ‖ amp ⟦ C ⟧ x z ‖²) ≡ + (2 ^ norm C)
circuit-unit-columns = CSem.⟦⟧-unit-columns

-- More: the columns are orthonormal in Z[ζ] itself, U†U = I with the
-- product and conjugation of PathSum.Ring, so ⟦ C ⟧ satisfies
-- definition 2.4 as a theorem.  (UU† = I, which would make it unitary,
-- is not stated.)

circuit-Isometric : (C : Circuit n) → Isometric ⟦ C ⟧
circuit-Isometric = Unit.circuit-Isometric

-- So "⟦ C ⟧ is the identity" means what it should: the circuit's
-- matrix, computed gate by gate, is the identity matrix.

circuit-≋-id : (C : Circuit n) →
               (⟦ C ⟧ ≋ idPS ⇔
                (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)))
circuit-≋-id = Cor.circuit-≋-id


------------------------------------------------------------------------
-- Definition 2.9 and propositions 2.10 and 2.14, over {H, CNOT, R_k}
-- (PathSum.CRK.Circuit, PathSum.CRK.Semantics)

-- The paper's own gate set.  Wires carry Z₂-linear forms, so CNOT
-- needs no path variable; R_k contributes x/2^k and a Hadamard ½xy.
-- The path-sum computes the circuit's matrix, and satisfies lemma
-- 4.1's bound.

prop-2-10-Rk : (C : K.Circuit n) (x z : Assign n) →
               amp K.⟦ C ⟧ x z ≐ KSem.applyᴬ C (δ x) z
prop-2-10-Rk = KT.prop-2-10

circuit-WellFormed-Rk : (C : K.Circuit n) → WellFormed K.⟦ C ⟧
circuit-WellFormed-Rk = KT.circuit-WellFormed

-- Proposition 2.14 bounds the order of the phase by the level k of the
-- R_k in the circuit.  That is false at k = 1: the Hadamard's ½xy is
-- of order 2 whatever gates surround it.  The bound is max(2, k), the
-- paper's own once k ≥ 2, and the same holds of the degree modulo the
-- integers.

prop-2-14 : (C : K.Circuit n) → Ord≤ (2 ⊔ K.level C) (phase K.⟦ C ⟧)
prop-2-14 = KT.prop-2-14

prop-2-14-k : ∀ k → 2 ≤ k → (C : K.Circuit n) → K.level C ≤ k →
              Ord≤ k (phase K.⟦ C ⟧)
prop-2-14-k = KT.prop-2-14-k

prop-2-14-deg : (C : K.Circuit n) → K.Deg≤ (2 ⊔ K.level C) (phase K.⟦ C ⟧)
prop-2-14-deg = KT.prop-2-14-deg

prop-2-14-false-at-1 :
  ¬ (∀ (C : K.Circuit 1) → K.level C ≤ 1 → K.Deg≤ 1 (phase K.⟦ C ⟧))
prop-2-14-false-at-1 = KT.prop-2-14-false-at-1


------------------------------------------------------------------------
-- Proposition 3.1 for [Elim], [ω] and [HH] (PathSum.Denotation)

-- The rules as PathSum.Reduction has them: each eliminates the first
-- path variable, and the quotients of [ω] and [HH] are Z₂-linear
-- forms -- all that lemma 4.3 needs.

⟶-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ≋ ζ
⟶-sound {ξ = a} {ζ = b} = Den.⟶-sound {ξ = a} {ζ = b}

-- All of figure 2 at the first path variables (PathSum.Reduction.General,
-- PathSum.Reduction.Sound): [ω] and [HH] with any Boolean-valued
-- quotient, and [Case], which removes two path variables at once.

⟶ᴳ-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ ζ → ξ ≋ ζ
⟶ᴳ-sound = GenS.⟶ᴳ-sound

⟶ᴳ*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ* ζ → ξ ≋ ζ
⟶ᴳ*-sound = GenS.⟶ᴳ*-sound

-- The linear rules at any internal path variable (PathSum.Anywhere,
-- PathSum.Anywhere.Sound).  A rule at y_j is the rule at the head of
-- front j ξ, which lists y_j first; renumbering the path variables
-- changes no amplitude.

front-≋ : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) → front j ξ ≋ ξ
front-≋ = AnyS.front-≋

⟶ᵍ-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ ζ → ξ ≋ ζ
⟶ᵍ-sound = AnyS.⟶ᵍ-sound

⟶ᵍ*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ* ζ → ξ ≋ ζ
⟶ᵍ*-sound = AnyS.⟶ᵍ*-sound


------------------------------------------------------------------------
-- Proposition 3.2: strong normalization (PathSum.Reduction)

-- Every rule removes exactly one path variable, so the length of a
-- chain is the number of path variables it removes -- in particular
-- no chain is longer than the path-sum has, and none is infinite.

⟶*-length : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
            (steps : ξ ⟶* ζ) → len steps + m′ ≡ m
⟶*-length = Red.⟶*-length

-- The same at any variable, where the renumbering is folded into each
-- rule (a separate reordering step, being a bijection, would loop):
-- the length is still exact, and every path-sum is strongly
-- normalising, as an inductive predicate.

⟶ᵍ*-length : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
             (steps : ξ ⟶ᵍ* ζ) → lenᵍ steps + m′ ≡ m
⟶ᵍ*-length = Any.⟶ᵍ*-length

⟶ᵍ-SN : (ξ : PathSum n k m) → SN _⟶ᵍ_ ξ
⟶ᵍ-SN = Any.⟶ᵍ-SN

-- With [Case], which removes two variables, the length is only
-- bounded.

⟶ᴳ*-bounded : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
              (steps : ξ ⟶ᴳ* ζ) → lenᴳ steps ≤ m
⟶ᴳ*-bounded = Gen.⟶ᴳ*-bounded

-- "Every sequence of rewrites terminates with an irreducible
-- path-sum": whether a rule applies somewhere is decidable, by a
-- finite search, so every path-sum reduces to one to which none does.
-- (That the search is polynomial is not formalised.)

normal-form : (ξ : PathSum n k m) →
              ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                (ξ ⟶ᵍ* ξ′) × Irreducible ξ′
normal-form = AnyM.normal-form


------------------------------------------------------------------------
-- Lemma 4.1: isometry restrictions (PathSum.Isometry,
-- PathSum.PartialIsometry)

-- Restriction-id ξ is ξ|f(x,y)=x ≡ |x⟩ ↦ |x⟩: at every x, the paths
-- carrying x back to x sum to the normalised 1.  WellFormed ξ bounds
-- the trace-form norm of every column of U_ξ by 1.

lemma-4-1 : (ξ : PathSum n k m) → WellFormed ξ →
            (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1 = Isom.lemma-4-1

-- Definition 2.4 implies that bound: a partial isometry (U†U
-- idempotent, on the unnormalised operator) is WellFormed, by
-- t² ≤ ‖G_xx‖² ≤ Σ ‖G_xx″‖² = 2^k·t for its Gram matrix G.  So lemma
-- 4.1 holds under the paper's own hypothesis; the converse fails
-- (½·id is WellFormed), so the form above is the stronger.

PartialIsometric⇒WellFormed : (ξ : PathSum n k m) → PartialIsometric ξ →
                              WellFormed ξ
PartialIsometric⇒WellFormed = PIso.PartialIsometric⇒WellFormed

lemma-4-1-partial : (ξ : PathSum n k m) → PartialIsometric ξ →
                    (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1-partial = PIso.lemma-4-1-partial


------------------------------------------------------------------------
-- Lemma 4.2: destructive interference (PathSum.Denotation)

-- For a quotient ½Q with Q a non-zero Z₂-linear form in the inputs,
-- liftXor c S; the paper allows any Boolean-valued Q, but the linear
-- case is all lemma 4.3 needs.

interference :
  (ξ : PathSum n k (suc m)) (c : Bool) (S : Mon n m) →
  head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
  (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
  proj₂ S ≡ ⊥ → ¬ (c ≡ false × S ≡ 1ᵐ) →
  ¬ (ξ ≋ idPS)
interference = Den.interference-lemma

-- For a general quotient the paper's hypothesis, "Q non-zero and
-- integer-valued", is not enough: Q = 2x₁ makes ½y₀Q an integer, the
-- two branches of y₀ add instead of cancelling, and the path-sum can be
-- the identity.  What suffices is Q odd at some input, which, Q being
-- free of path variables, is Q ≢ 0 modulo 2 coefficient by coefficient.

interferenceᴳ : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
                head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q) →
                (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
                (∀ j → NoVar (+ 2) y[ j ] Q) →
                ¬ (Q ≈[ + 2 ] 0ᴾ) →
                ¬ (ξ ≋ idPS)
interferenceᴳ = Intf.interferenceᴳ

-- For the Boolean-valued Q of section 4.2 "non-zero" does suffice.

interference-bool : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
                    head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q) →
                    (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
                    BoolValued Q → (∀ j → NoVar (+ 2) y[ j ] Q) →
                    ¬ (∀ γ → Q γ ≡ 0ℤ) →
                    ¬ (ξ ≋ idPS)
interference-bool = Intf.interference-bool

lemma-4-2-as-stated-fails :
  ∃ λ (ξ : PathSum 1 2 1) → ∃ λ (Q : Poly 1 0) →
    (head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q)) ×
    (∀ w → NoVar (+ 2) y₀ (out ξ w)) ×
    ¬ (∀ γ → Q γ ≡ 0ℤ) ×
    (ξ ≋ idPS)
lemma-4-2-as-stated-fails = Intf.lemma-4-2-as-stated-fails


------------------------------------------------------------------------
-- Lemma 4.3: Clifford progress and preservation (PathSum.Clifford)

-- The case the paper leaves implicit -- [ω] consumes one unit of
-- normalisation and [Elim] two, and nothing in the hypotheses
-- supplies them -- is discharged rather than reported: such a
-- path-sum is not the identity, so the hypothesis rules it out.

lemma-4-3 : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
            ξ ≋ idPS →
            ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m) →
              (ξ ⟶ ξ′) × Ord≤ 2 (phase ξ′)
lemma-4-3 = Cliff.lemma-4-3

-- The paper says progress is made at "some internal path variable";
-- it is made at every one (PathSum.Anywhere.Clifford), so corollary 4.4
-- holds whatever variable a strategy picks.

lemma-4-3-at : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) → Internal ξ →
               Ord≤ 2 (phase ξ) → ξ ≋ idPS →
               ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m) →
                 (front j ξ ⟶ ξ′) × Internal ξ′ × Ord≤ 2 (phase ξ′)
lemma-4-3-at = AnyC.lemma-4-3-at


------------------------------------------------------------------------
-- Corollary 4.4: a path-sum without path variables, or a refutation
-- (PathSum.Clifford)

corollary-4-4 : (ξ : PathSum n k m) → Internal ξ → Ord≤ 2 (phase ξ) →
                Cliff.Reduces ξ
corollary-4-4 = Cliff.corollary-4-4


------------------------------------------------------------------------
-- The hypotheses of corollary 4.4, at a Clifford circuit
-- (PathSum.Circuit)

-- Neither hypothesis holds of an arbitrary path-sum, and neither is
-- meant to: corollary 4.4 applies lemma 4.3 to the isometry
-- restriction of section 4.1, ⟦ C ⟧ᴿ below, whose output signature is
-- the identity.  Both are theorems of that path-sum -- every path
-- variable is internal because no output mentions one, and the phase
-- is of order two because a Clifford gate contributes ¼ u or ½ u v.

circuit-Internal : (C : Circuit n) → Internal ⟦ C ⟧ᴿ
circuit-Internal = Circ.⟦⟧ᴿ-Internal

circuit-Ord≤ : (C : Circuit n) → Ord≤ 2 (phase ⟦ C ⟧ᴿ)
circuit-Ord≤ = Circ.⟦⟧ᴿ-Ord≤

-- So the corollary applies to every Clifford circuit unconditionally.

corollary-4-4-circuit : (C : Circuit n) → Cliff.Reduces ⟦ C ⟧ᴿ
corollary-4-4-circuit = Cor.corollary-4-4-circuit


------------------------------------------------------------------------
-- Lemma 4.1 at a circuit (PathSum.CircuitSemantics, PathSum.Isometry)

-- ⟦ C ⟧ satisfies WellFormed, and ⟦ C ⟧ᴿ is its isometry restriction,
-- reified: the two have the same diagonal, and no path of ⟦ C ⟧ᴿ
-- leaves its input.  So whether the circuit is the identity is exactly
-- whether ⟦ C ⟧ᴿ is -- the question the reduction answers.

circuit-WellFormed : (C : Circuit n) → WellFormed ⟦ C ⟧
circuit-WellFormed = Cor.circuit-WellFormed

lemma-4-1-circuit : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ ⟦ C ⟧ᴿ ≋ idPS)
lemma-4-1-circuit = Cor.lemma-4-1-circuit


------------------------------------------------------------------------
-- Proposition 3.1 along a chain (PathSum.Clifford)

⟶*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶* ζ → ξ ≋ ζ
⟶*-sound = Cliff.⟶*-sound


------------------------------------------------------------------------
-- Whether a reduced path-sum is the identity (PathSum.Identity)

-- What the corollary stops short of: `done` says the path variables
-- are exhausted, not that what is left is the identity.  id-if is the
-- criterion stated coefficient by coefficient, and each refutation a
-- disproof at one input.  id-if is also necessary (id⇔syntactic
-- below); the input-by-input form id-if′, with the refutations, covers
-- every case (decide-≋-id).

id-if : (ξ : PathSum n 0 0) →
        (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) →
        phase ξ ≈[ pow M ] 0ᴾ →
        ξ ≋ idPS
id-if = Idn.id-if

not-id-out : (ξ : PathSum n k 0) (x : Assign n) →
             (∀ y → hits ξ x y x ≡ false) → ¬ (ξ ≋ idPS)
not-id-out = Idn.not-id-out

not-id-norm : (ξ : PathSum n (suc k) 0) (x : Assign n) (y : Assign 0) →
              hits ξ x y x ≡ true → ¬ (ξ ≋ idPS)
not-id-norm = Idn.not-id-norm

not-id-phase : (ξ : PathSum n 0 0) (x : Assign n) (y : Assign 0) →
               hits ξ x y x ≡ true →
               ¬ (pow M ∣ eval (phase ξ) x y) → ¬ (ξ ≋ idPS)
not-id-phase = Idn.not-id-phase


------------------------------------------------------------------------
-- The verdict, transported back to the circuit

-- A reduct is equivalent to ⟦ C ⟧ᴿ (proposition 3.1 along the chain),
-- and lemma 4.1 at the circuit carries that to ⟦ C ⟧: a reduction that
-- lands on the identity proves the circuit is the identity, a reduct
-- that is not the identity proves it is not, and whichever way
-- corollary 4.4 ends, the question about the circuit is the question
-- about its outcome.

reduct≋ : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
          (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋ = Cor.reduct≋

circuit-id : (C : Circuit n) {ξ′ : PathSum n 0 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
             phase ξ′ ≈[ pow M ] 0ᴾ →
             ⟦ C ⟧ ≋ idPS
circuit-id = Cor.circuit-id

circuit-not-id : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
                 ¬ (ξ′ ≋ idPS) → ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-id = Cor.circuit-not-id

-- Corollary 4.4 about the circuit itself: either ⟦ C ⟧ᴿ reduces to a
-- path-sum with no path variables left, whose being the identity is
-- exactly the circuit's, or the reduction has already refuted the
-- circuit.

corollary-4-4-⟦⟧ : (C : Circuit n) →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-⟦⟧ = Cor.corollary-4-4-⟦⟧


------------------------------------------------------------------------
-- The identity, syntactically (PathSum.Syntactic)

-- A path-sum without path variables is the identity exactly when it
-- has the identity's polynomials: no normalisation, outputs that are
-- the inputs modulo 2 and a phase that vanishes modulo 2^M,
-- coefficient by coefficient.  The converse of id-if goes through
-- Möbius inversion (PathSum.Mobius).

id⇔syntactic : (ξ : PathSum n k 0) →
               (ξ ≋ idPS ⇔
                (k ≡ 0 ×
                 (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) ×
                 phase ξ ≈[ pow M ] 0ᴾ))
id⇔syntactic = Syn.id⇔syntactic

-- The content of corollary 4.4's proof ("either ⟦C⟧|f(x,y)=x reduces
-- to |x⟩ ↦ |x⟩ ... or ξ′ ≢ |x⟩ ↦ |x⟩").  Reducing ⟦ C ⟧ᴿ either refutes
-- the circuit or ends at a path-sum without path variables
-- (corollary-4-4-⟦⟧), and whatever chain ends there, the circuit is the
-- identity exactly when that endpoint is syntactically |x⟩ ↦ |x⟩: no
-- normalisation, outputs the inputs modulo 2 and phase 0 modulo 1,
-- coefficient by coefficient.

corollary-4-4-any : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-any = Cor.corollary-4-4-any

-- In particular such a chain ends at the identity's polynomials
-- exactly for the identity circuits.  (The corollary's own statement,
-- decidability in polynomial time, is not formalised.)

corollary-4-4-syntactic : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic = Cor.corollary-4-4-syntactic


------------------------------------------------------------------------
-- The same verdict along the other calculi (PathSum.Anywhere.Corollary,
-- PathSum.Reduction.GeneralCorollary)

-- Nothing in the characterisation depends on reducing at the first
-- variable, or on the linear rules alone: any chain of the linear rules
-- at any variables, or of all four rules at the head, that ends without
-- path variables ends at the identity's polynomials exactly for the
-- identity circuits.

corollary-4-4-anyᵍ : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶ᵍ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᵍ = AnyCor.corollary-4-4-anyᵍ

corollary-4-4-anyᴳ : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶ᴳ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᴳ = GenCor.corollary-4-4-anyᴳ


------------------------------------------------------------------------
-- Corollary 4.4 for Clifford circuits with CNOT, by compilation
-- (PathSum.CRK.Compile)

-- A circuit over {H, CNOT, R_k, R_k†} whose R_k have k ≤ 2 is Clifford.
-- Compiled to {H, S, CZ} (CNOT as H ; CZ ; H, S† as S³) it has an
-- equivalent path-sum, so the characterisation above carries over.
-- The paper's proof reifies the restriction of ⟦ C ⟧ itself by Gaussian
-- elimination instead; that route is not the one taken here.

compile-≋ : (C : K.Circuit n) → K.level C ≤ 2 → K.⟦ C ⟧ ≋ ⟦ KC.compile C ⟧
compile-≋ = KT.compile-≋

corollary-4-4-syntactic-Rk : (C : K.Circuit n) → K.level C ≤ 2 →
  (K.⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ KC.compile C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic-Rk = KT.corollary-4-4-syntactic-compiled


------------------------------------------------------------------------
-- Equivalence of two circuits: the miter (PathSum.Miter,
-- PathSum.Equivalence)

-- Section 3's verification question is whether ⟦ C ⟧ ≡ ξ, checked
-- through the miter.  C † reverses C and inverts each gate; it undoes C
-- on both sides, up to the scalar the normalisation accounts for, with
-- no appeal to unitarity.  So two circuits are equivalent exactly when
-- the first followed by the adjoint of the second is the identity, and
-- a path-sum is the circuit's exactly when C † sends each of its
-- columns to the basis column.

miter : (C₁ C₂ : Circuit n) → (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ⟦ C₁ ++ C₂ † ⟧ ≋ idPS)
miter = Mit.miter

spec-miter : (C : Circuit n) (ξ : PathSum n k m) →
             (⟦ C ⟧ ≋ ξ ⇔
              (∀ x z → applyᴬ (C †) (amp ξ x) z ≐
                       scale (k + norm C) (δ x z)))
spec-miter = Mit.spec-miter

-- Hence equivalence of Clifford circuits is corollary 4.4 at the miter.

equivalence-syntactic : (C₁ C₂ : Circuit n) →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C₁ ++ C₂ † ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
equivalence-syntactic = Eqv.equivalence-syntactic

equivalence-decidable : (C₁ C₂ : Circuit n) → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-decidable = Eqv.equivalence-decidable


------------------------------------------------------------------------
-- A decision procedure that follows corollary 4.4 (PathSum.Decide)

-- The same test input by input: with normalisation left, a path-sum
-- without path variables is never the identity (Decide.id-no-norm);
-- without, it is the identity exactly when, at every input, its path
-- returns the input with a phase that vanishes modulo 2^M.  Every way
-- that fails is one of the refutations above.

id⇔′ : (ξ : PathSum n 0 0) →
       (ξ ≋ idPS ⇔
        ((∀ x y → hits ξ x y x ≡ true) ×
         (∀ x y → pow M ∣ eval (phase ξ) x y)))
id⇔′ = Dcd.id⇔′

decide-≋-id : (ξ : PathSum n k 0) → Dec (ξ ≋ idPS)
decide-≋-id = Dcd.decide-≋-id

-- Reduce ⟦ C ⟧ᴿ, then test what is left.  Decidability as such is
-- elementary -- the matrix has finitely many entries in Z[ζ], each
-- decidably equal to the identity's -- and the type below does not
-- record the route; what the route adds is the reduction, whose content
-- is corollary-4-4-⟦⟧ and corollary-4-4-syntactic above.  (Polynomials
-- are functions on all 2^(n+m) monomials and the test visits every
-- input, so nothing here is polynomial-time.)

circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidable = Cor.circuit-decidable

matrix-decidable : (C : Circuit n) →
  Dec (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z))
matrix-decidable = Cor.matrix-decidable
