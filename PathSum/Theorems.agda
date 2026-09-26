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
-- Around that core: lemma 2.5 for every Boolean polynomial; composition
-- of path-sums (definition 2.6), proposition 2.7's operator equation,
-- and remark 2.8 up to ≋ (PathSum.Compose); definition 2.9 over the
-- paper's own gate set {H, CNOT, R_k} with propositions 2.10 and 2.14
-- (PathSum.CRK), compositionally as well; the size half of corollary
-- 2.15, with an interpreter building the representation gate by gate
-- (PathSum.Size); section 5.2's quantum Fourier transform for every n
-- within the precision (PathSum.QFT); Z[ζ] as a commutative ring,
-- definition 2.4, and every circuit's path-sum unitary, over both gate
-- sets; all four rules of figure 2, [Case] included and with
-- Boolean-valued quotients, at any internal path variables
-- (PathSum.Full) -- sound, strongly normalising, with decidable
-- matching and irreducible normal forms; lemma 4.1 under definition
-- 2.4 and up to a global phase; lemma 4.3 at every internal variable;
-- corollary 4.4 by the paper's own route for circuits with CNOT
-- (Gaussian elimination, PathSum.Gauss) and under any rules in any
-- order (PathSum.Full.Clifford); C† as the conjugate transpose, and
-- the miter ⟦ C† ⟧ ∘ ξ against any specification, over both gate sets;
-- equivalence of two Clifford circuits decided by the paper's route,
-- and section 5.1's translation validation for circuits at any level
-- (sound, and complete for Clifford); and the paper's worked examples,
-- checked at precision M₀ = 0 (PathSum.Examples, imported below).
--
-- Statements of the paper that are false as printed, proved here in a
-- corrected form beside a checked counterexample: lemma 4.2 needs Q odd
-- at some input, not merely non-zero (Q = 2x₁ has ½y₀Q integral);
-- proposition 2.14's bound is max(2, k), not k (a Hadamard's phase ½xy
-- has order 2 whatever k is); and proposition 2.7's "well-formedness
-- is preserved" fails both for WellFormed and for definition 2.4 (it
-- holds when the second path-sum is an isometry).  Smaller slips, in
-- the module headers: definition 2.6 omits a renaming in the outputs,
-- section 4.1 substitutes Q where x_i ⊕ Q is meant, example B.1 as
-- printed is the identity rather than ω·I, and the fourth line of
-- example 3.4 does not follow from the third.  One gap is filled: the
-- proof of corollary 4.4 reduces by arbitrary rules, which needs every
-- rule to preserve order ≤ 2 -- lemma 2.13 covers only linear
-- substitutions, and PathSum.Full.Clifford supplies the rest.
--
-- Not formalised: the polynomial time bounds (proposition 3.2,
-- corollaries 2.15 and 4.4); constant inputs, beyond restricting to the
-- columns where an ancilla is |0⟩ (PathSum.Ancilla); the symmetric
-- monoidal laws of remark 2.8 beyond interchange and SWAP naturality;
-- and section 5's benchmarks as runs of the tool.
--
-- Each section's banner names the modules its results come from;
-- results proved here from them are stated with their proofs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _<_)

module PathSum.Theorems (M₀ : ℕ) where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (_+_; _*_; _∸_; _^_; _≤_; _⊔_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _-_)
  renaming (_*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.List.Base using (_++_; length)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_×_; _,_; ∃; proj₂)
open import Level using (0ℓ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; no; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.AssignSum using (Σᶻ)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Cyclotomic M₀ using (_≐_; Σᴮ; zpow; scale; scale-map)
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

open import PathSum.Ring M₀ using (_⊛_; conj)

import PathSum.Ring.Laws
module RL = PathSum.Ring.Laws M₀

import PathSum.PartialIsometry.Strict
module Strict = PathSum.PartialIsometry.Strict M₀

import PathSum.PartialIsometry.Unitary
module PU = PathSum.PartialIsometry.Unitary M₀
open PU using (Unitary)

import PathSum.CRK.Unitarity
module KU = PathSum.CRK.Unitarity M₀

open import PathSum.Compose using (_∘ᴾ_; _⊗ᴾ_)
open import PathSum.Compose.Sum M₀ using (_++ᵃ_)

import PathSum.Compose.Matrix
module Mat = PathSum.Compose.Matrix M₀

import PathSum.Compose.Laws
module Laws = PathSum.Compose.Laws M₀

import PathSum.Compose.WellFormed
module CWF = PathSum.Compose.WellFormed M₀

import PathSum.Compose.Counterexample
module CE = PathSum.Compose.Counterexample M₀

import PathSum.Compose.Clifford
module CC = PathSum.Compose.Clifford M₀

import PathSum.Compose.CRK
module CR = PathSum.Compose.CRK M₀

import PathSum.Compose.Tensor
module Tens = PathSum.Compose.Tensor M₀

import PathSum.Compose.Swap
module Swp = PathSum.Compose.Swap M₀
open Swp using (swapᴾ)

import PathSum.Full
module Fl = PathSum.Full M
open Fl using (_⟶ᶠ_; _⟶ᶠ*_; lenᶠ)

import PathSum.Full.Sound
module FlS = PathSum.Full.Sound M₀

import PathSum.Full.Match
module FlM = PathSum.Full.Match M
open FlM using (Irreducibleᶠ)

import PathSum.Full.Corollary
module FlC = PathSum.Full.Corollary M₀

import PathSum.Full.Clifford
module FlCl = PathSum.Full.Clifford M₀

import PathSum.Gauss.Corollary
module GC = PathSum.Gauss.Corollary M₀

open import PathSum.Congruence M₀ using (phasePS)

import PathSum.GlobalPhase
module GP = PathSum.GlobalPhase M₀
open GP using (Restriction-phase)

import PathSum.Adjoint.Conjugate
module AdjC = PathSum.Adjoint.Conjugate M₀

import PathSum.Miter.Compose
module MitC = PathSum.Miter.Compose M₀

import PathSum.Compose.Contraction
module Contr = PathSum.Compose.Contraction M₀

import PathSum.CRK.Adjoint
module KA = PathSum.CRK.Adjoint M

import PathSum.CRK.Conjugate
module KConj = PathSum.CRK.Conjugate M₀

import PathSum.CRK.Miter
module KM = PathSum.CRK.Miter M₀

import PathSum.CRK.Miter.Compose
module KMC = PathSum.CRK.Miter.Compose M₀

import PathSum.CRK.Equivalence
module KEq = PathSum.CRK.Equivalence M₀

import PathSum.CRK.Validation
module KVal = PathSum.CRK.Validation M₀

import PathSum.CRK.Specification
module KSpec = PathSum.CRK.Specification M₀

import PathSum.Size
module Sz = PathSum.Size M

import PathSum.Size.Sparse
module Sp = PathSum.Size.Sparse M
open Sp using (Represents; Small; terms; size)

import PathSum.Size.Interpreter
module SzI = PathSum.Size.Interpreter M
open SzI using (Denotes)

import PathSum.Size.Equivalence
module SzE = PathSum.Size.Equivalence M₀

import PathSum.Size.Interpreter.Clifford
import PathSum.Size.Interpreter.Equivalence

import PathSum.CRK.Controlled
module KCR = PathSum.CRK.Controlled M₀

import PathSum.QFT
module QFT = PathSum.QFT M₀

import PathSum.QFT.Circuit
module QC = PathSum.QFT.Circuit M₀

import PathSum.QFT.Spec
module QS = PathSum.QFT.Spec M₀

import PathSum.QFT.Unitary
module QU = PathSum.QFT.Unitary M₀

import PathSum.QFT.Relabel
module QR = PathSum.QFT.Relabel M₀

import PathSum.QFT.Count
module QCnt = PathSum.QFT.Count M₀

-- The QFT at the sizes of table 2 (their gate counts), and the
-- seven-T Toffoli's size representation, at fixed precisions.

import PathSum.Examples.QFT

-- Closed instances (the seven-T Toffoli's representation), at M₀ = 0.

import PathSum.Size.Interpreter.Example

-- The worked examples are closed facts at precision M₀ = 0; they are
-- imported, not restated, so that this root checks them too.

import PathSum.Examples

private
  variable
    n k m k′ m′ k″ m″ j l j′ l′ : ℕ
    n₁ n₂ k₁ k₂ m₁ m₂ j₁ j₂ l₁ l₂ : ℕ


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
-- Z[ζ] is a commutative ring (PathSum.Ring, PathSum.Ring.Laws)

-- The product is the negacyclic convolution of coordinates and conj
-- sends ζ to ζ⁻¹; conj is a ring automorphism and its own inverse.

⊛-comm : ∀ a b → a ⊛ b ≐ b ⊛ a
⊛-comm = RL.⊛-comm

⊛-assoc : ∀ a b c → (a ⊛ b) ⊛ c ≐ a ⊛ (b ⊛ c)
⊛-assoc = RL.⊛-assoc

conj-⊛ : ∀ a b → conj (a ⊛ b) ≐ conj a ⊛ conj b
conj-⊛ = RL.conj-⊛

ℤ[ζ] : CommutativeRing 0ℓ 0ℓ
ℤ[ζ] = RL.ℤ[ζ]


------------------------------------------------------------------------
-- Definition 2.6 and proposition 2.7: composition
-- (PathSum.Compose, PathSum.Compose.Matrix, PathSum.Compose.Laws)

-- ξ′ ∘ᴾ ξ feeds ξ′'s inputs the (lifted) outputs of ξ and concatenates
-- the path variables; the normalisations add.  Its operator is the
-- product of the two, exactly and with no hypothesis.  The laws of a
-- category hold up to ≋: the two bracketings, say, have normalisations
-- that are equal only propositionally.

prop-2-7 : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x z : Assign n) →
           amp (ξ′ ∘ᴾ ξ) x z ≐ Σᴮ (λ w → amp ξ x w ⊛ amp ξ′ w z)
prop-2-7 = Mat.prop-2-7

∘ᴾ-assoc : (ξ″ : PathSum n k″ m″) (ξ′ : PathSum n k′ m′)
           (ξ : PathSum n k m) →
           ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) ≋ (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ))
∘ᴾ-assoc = Laws.∘ᴾ-assoc

∘ᴾ-cong : (ξ′ : PathSum n k′ m′) (η′ : PathSum n j′ l′)
          (ξ : PathSum n k m) (η : PathSum n j l) →
          ξ′ ≋ η′ → ξ ≋ η → (ξ′ ∘ᴾ ξ) ≋ (η′ ∘ᴾ η)
∘ᴾ-cong = Laws.∘ᴾ-cong

-- "For any well-formed, compatible path-sums ξ, ξ′, ξ′ ∘ ξ is also well
-- formed" is false, whether well-formed means WellFormed (a path-sum
-- sending every input to |+⟩, then one sending every input to |0⟩) or
-- definition 2.4 (|0⟩⟨0| then |+⟩⟨+| is (1/√2)|+⟩⟨0|).  Compatibility
-- is vacuous here, every input being a variable.  It holds when the
-- path-sum applied second is an isometry -- the paper's footnote: in
-- practice only unitaries are composed.

WellFormed-∘-fails :
  WellFormed CE.plus × WellFormed CE.erase × ¬ WellFormed (CE.erase ∘ᴾ CE.plus)
WellFormed-∘-fails = CE.WellFormed-∘-fails

PartialIsometric-∘-fails :
  PartialIsometric CE.P₀ × PartialIsometric CE.P₊ ×
  ¬ PartialIsometric (CE.P₊ ∘ᴾ CE.P₀)
PartialIsometric-∘-fails = CE.PartialIsometric-∘-fails

Isometric-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
              Isometric ξ′ → Isometric ξ → Isometric (ξ′ ∘ᴾ ξ)
Isometric-∘ = CWF.Isometric-∘

WellFormed-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
               Isometric ξ′ → WellFormed ξ → WellFormed (ξ′ ∘ᴾ ξ)
WellFormed-∘ = CWF.WellFormed-∘

-- WellFormed, the bound lemma 4.1 needs, survives even after a partial
-- isometry (PathSum.Compose.Contraction: any map that does not
-- lengthen columns will do), although being a partial isometry does
-- not.

WellFormed-∘-partial : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) →
                       PartialIsometric ξ′ → WellFormed ξ →
                       WellFormed (ξ′ ∘ᴾ ξ)
WellFormed-∘-partial = Contr.WellFormed-∘-partial


------------------------------------------------------------------------
-- Remark 2.8: the tensor product (PathSum.Compose.Tensor,
-- PathSum.Compose.Swap)

-- The amplitude of ξ₁ ⊗ᴾ ξ₂ is the product of the two; composition and
-- tensor interchange, and SWAP is natural, up to ≋ -- the remark's
-- "strictly equal" cannot even be stated, the indices of the two sides
-- being equal only propositionally.

amp-⊗ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
        (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂) →
        amp (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
        amp ξ₁ x₁ z₁ ⊛ amp ξ₂ x₂ z₂
amp-⊗ = Tens.amp-⊗

⊗-interchange : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂) →
                ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) ≋ ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂))
⊗-interchange = Tens.⊗-interchange

swap-natural : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂) →
               (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂)) ≋ ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)
swap-natural = Swp.swap-natural


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
-- definition 2.4 as a theorem; and so are the rows, UU† = I, because
-- the transpose of U_C is U_(reverse C).  So ⟦ C ⟧ is unitary.

circuit-Isometric : (C : Circuit n) → Isometric ⟦ C ⟧
circuit-Isometric = Unit.circuit-Isometric

circuit-Unitary : (C : Circuit n) → Unitary ⟦ C ⟧
circuit-Unitary = Unit.circuit-Unitary

-- Definition 2.9's clause ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧, up to ≋
-- (PathSum.Compose.Clifford).

⟦++⟧ : (C₁ C₂ : Circuit n) → ⟦ C₁ ++ C₂ ⟧ ≋ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧)
⟦++⟧ = CC.⟦++⟧

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

-- The paper's definition proper is compositional, each gate's path-sum
-- as printed (PathSum.Compose.CRK): it agrees with the interpretation
-- above, which runs the gates on a state, and satisfies
-- ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧.  And ⟦ C ⟧ is unitary (PathSum.CRK.Unitarity),
-- as proposition 2.10's "unitary matrix U_C" requires.

⟦⟧ᶜ≋⟦⟧-Rk : (C : K.Circuit n) → CR.⟦ C ⟧ᶜ ≋ K.⟦ C ⟧
⟦⟧ᶜ≋⟦⟧-Rk = CR.⟦⟧ᶜ≋⟦⟧

⟦++⟧-Rk : (C₁ C₂ : K.Circuit n) → K.⟦ C₁ ++ C₂ ⟧ ≋ (K.⟦ C₂ ⟧ ∘ᴾ K.⟦ C₁ ⟧)
⟦++⟧-Rk = CR.⟦++⟧

circuit-Unitary-Rk : (C : K.Circuit n) → Unitary K.⟦ C ⟧
circuit-Unitary-Rk = KU.circuit-Unitary

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
-- Corollary 2.15: size (PathSum.Size, PathSum.Size.Interpreter)

-- A polynomial here is a function on all 2^(n+m) monomials, so "size"
-- is about an explicit representation (Sp.Rep): a list of terms
-- (monomial, coefficient modulo 2^M) and a Z₂-linear form per output.
-- A circuit's path-sum has one path variable per Hadamard, and its
-- phase modulo 1 has degree at most max(2, k) (proposition 2.14,
-- corrected), so the terms of degree at most that -- at most
-- (n + |C| + 1)^max(2,k) of them -- represent it.  The bound is
-- polynomial in n + |C| for fixed k; in the paper's volume n·|C| it
-- holds once n, |C| ≥ 1, and fails for the empty circuit.

corollary-2-15 : (C : K.Circuit n) →
  K.paths C ≡ K.norm C × K.paths C ≤ length C ×
  Represents K.⟦ C ⟧ (Sz.repᴷ C) × Small (2 ⊔ K.level C) (Sz.repᴷ C) ×
  length (terms (Sz.repᴷ C)) ≤ suc (n + length C) ^ (2 ⊔ K.level C) ×
  size (Sz.repᴷ C) ≤ 2 * suc (n + length C + M) ^ suc (2 ⊔ K.level C)
corollary-2-15 = Sz.corollary-2-15ᴷ

corollary-2-15-volume-degenerate : (f : ℕ → ℕ) →
  ¬ (∀ n (C : K.Circuit n) →
       ∃ λ R → Represents K.⟦ C ⟧ R × size R ≤ f (n * length C))
corollary-2-15-volume-degenerate = Sz.volume-degenerate

-- The representation is not merely congruent: read back as a
-- path-sum it is the circuit's operator.

corollary-2-15-≋ : (C : K.Circuit n) →
                   K.⟦ C ⟧ ≋ Sp.psʳ (K.norm C) (Sz.repᴷ C)
corollary-2-15-≋ = SzE.repᴷ-≋

-- "And can be computed in polynomial time", as far as it can be said
-- without a machine model: an explicit interpreter building the
-- representation gate by gate -- each R_k adding the lifting of its
-- wire's form truncated at degree k -- is correct, and every list it
-- builds has polynomially many terms.  This bounds the data, not a
-- running time; no complexity class is formalised.

sparse-interpreter-correct : (C : K.Circuit n) →
                             Denotes K.⟦ C ⟧ (SzI.interpᴷ C)
sparse-interpreter-correct = SzI.interpᴷ-correct

sparse-interpreter-length : (C : K.Circuit n) →
  length (terms (proj₂ (SzI.interpᴷ C))) ≤
  suc (n + length C) ^ suc (1 ⊔ K.level C)
sparse-interpreter-length = SzI.interpᴷ-length-poly


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

-- All of figure 2 at any internal path variables, [Case] at any pair
-- (PathSum.Full, PathSum.Full.Sound): the calculus the paper uses.

⟶ᶠ-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ ζ → ξ ≋ ζ
⟶ᶠ-sound = FlS.⟶ᶠ-sound

⟶ᶠ*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ* ζ → ξ ≋ ζ
⟶ᶠ*-sound = FlS.⟶ᶠ*-sound


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

-- The same for all of figure 2 at any variables (PathSum.Full,
-- PathSum.Full.Match).  The rules quantify over quotients; the ones
-- they need are read off the phase as canonical candidates, which work
-- whenever any quotient does, so matching is decidable.

⟶ᶠ-SN : (ξ : PathSum n k m) → SN _⟶ᶠ_ ξ
⟶ᶠ-SN = Fl.⟶ᶠ-SN

⟶ᶠ*-bounded : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
              (steps : ξ ⟶ᶠ* ζ) → lenᶠ steps ≤ m
⟶ᶠ*-bounded = Fl.⟶ᶠ*-bounded

normal-formᶠ : (ξ : PathSum n k m) →
               ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                 (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′
normal-formᶠ = FlM.normal-formᶠ


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

-- The converse fails: ½·id is WellFormed but not a partial isometry
-- (PathSum.PartialIsometry.Strict).

WellFormed-strict :
  ∃ λ (ξ : PathSum 1 2 0) → WellFormed ξ × ¬ PartialIsometric ξ
WellFormed-strict = Strict.WellFormed-strict

-- Section 3.2 and appendix B conclude (SH)³ = ω·I, a global phase, and
-- lemma 4.1 as stated covers only the identity.  It holds up to any
-- global phase ζ^e (PathSum.GlobalPhase): a WellFormed path-sum is
-- ζ^e·I exactly when every diagonal entry is the normalised ζ^e.

lemma-4-1-phase : (ξ : PathSum n k m) (e : ℤ) → WellFormed ξ →
                  (ξ ≋ phasePS e ⇔ Restriction-phase e ξ)
lemma-4-1-phase = GP.lemma-4-1-phase


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

corollary-4-4-anyᶠ : (C : Circuit n) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᶠ = FlC.corollary-4-4-anyᶠ


------------------------------------------------------------------------
-- Corollary 4.4 under any rules, in any order (PathSum.Full.Clifford)

-- The paper's proof reduces by arbitrary rewrites (proposition 3.2),
-- so it needs every rule to keep the phase of order at most 2; lemma
-- 4.3 shows that only for the step it builds, and lemma 2.13 covers
-- only linear substitutions.  At a Clifford path-sum a Boolean-valued
-- quotient of [ω] or [HH] is forced to be a linear lifting and the X of
-- [Case] a constant, so every rule keeps the invariant.  Hence: reduce
-- ⟦ C ⟧ᴿ by any rules of figure 2, in any order, until none applies;
-- the circuit is the identity exactly when what is left is |x⟩ ↦ |x⟩
-- syntactically, with no path variables.

corollary-4-4-normalᶠ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (m′ ≡ 0 × k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-normalᶠ = FlCl.corollary-4-4-normalᶠ

circuit-decidableᶠ : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidableᶠ = FlCl.circuit-decidableᶠ


------------------------------------------------------------------------
-- Corollary 4.4 for Clifford circuits with CNOT, by compilation
-- (PathSum.CRK.Compile)

-- A circuit over {H, CNOT, R_k, R_k†} whose R_k have k ≤ 2 is Clifford.
-- Compiled to {H, S, CZ} (CNOT as H ; CZ ; H, S† as S³) it has an
-- equivalent path-sum, so the characterisation above carries over.
-- The paper's proof reifies the restriction of ⟦ C ⟧ itself by Gaussian
-- elimination instead; that route is the next section.

compile-≋ : (C : K.Circuit n) → K.level C ≤ 2 → K.⟦ C ⟧ ≋ ⟦ KC.compile C ⟧
compile-≋ = KT.compile-≋

corollary-4-4-syntactic-Rk : (C : K.Circuit n) → K.level C ≤ 2 →
  (K.⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ KC.compile C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic-Rk = KT.corollary-4-4-syntactic-compiled


------------------------------------------------------------------------
-- Corollary 4.4 by Gaussian elimination, the paper's route
-- (PathSum.Gauss, PathSum.Gauss.Corollary)

-- After a CNOT the outputs are sums of variables.  Eliminating one path
-- variable per output that contains one (y_j ← f_w ⊕ x_w ⊕ y_j, which
-- makes wire w read x_w) keeps the diagonal and the order of the phase,
-- and ends either at an input whose diagonal entry vanishes -- "if no
-- such solution exists, ⟦C⟧ ≢ |x⟩ ↦ |x⟩" -- or at the reified
-- restriction GC.⟦ C ⟧ᴿ, with outputs x and only internal path
-- variables, to which lemma 4.3 applies.

not-id-gauss : (C : K.Circuit n) → GC.⟦ C ⟧ᴿ ≡ nothing →
               ¬ (K.⟦ C ⟧ ≋ idPS)
not-id-gauss = GC.not-id-gauss

corollary-4-4-gauss : (C : K.Circuit n) → K.level C ≤ 2 →
  (K.⟦ C ⟧ ≋ idPS ⇔
   ∃ λ m′ → ∃ λ (ξ : PathSum n (K.norm C) m′) →
     GC.⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
       (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-gauss = GC.corollary-4-4-gauss

decidable-gauss : (C : K.Circuit n) → K.level C ≤ 2 → Dec (K.⟦ C ⟧ ≋ idPS)
decidable-gauss = GC.decidable-gauss


------------------------------------------------------------------------
-- Corollary 4.4 up to a global phase (PathSum.GlobalPhase)

-- With lemma 4.1 at ζ^e, the same reduction decides whether a Clifford
-- circuit is the global phase ζ^e: a chain from ⟦ C ⟧ᴿ that ends
-- without path variables ends at |x⟩ ↦ ζ^e|x⟩ syntactically exactly
-- when ⟦ C ⟧ is ζ^e·I.

corollary-4-4-phase : (C : Circuit n) (e : ℤ) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ phasePS e ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] κ e))
corollary-4-4-phase = GP.corollary-4-4-phase


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

-- C† is the adjoint proper: its path-sum is the conjugate transpose of
-- C's (PathSum.Adjoint.Conjugate), over both gate sets.

circuit-adjoint : (C : Circuit n) (x z : Assign n) →
                  amp ⟦ C † ⟧ x z ≐ conj (amp ⟦ C ⟧ z x)
circuit-adjoint = AdjC.circuit-adjoint

circuit-adjoint-Rk : (C : K.Circuit n) (x z : Assign n) →
                     amp K.⟦ C KA.† ⟧ x z ≐ conj (amp K.⟦ C ⟧ z x)
circuit-adjoint-Rk = KConj.circuit-adjoint

-- The miter as section 3 writes it, a composite of path-sums
-- (PathSum.Miter.Compose): a circuit is equivalent to a path-sum ξ --
-- any ξ -- exactly when ⟦ C† ⟧ ∘ ξ is the identity; and when ξ is
-- well formed, lemma 4.1 reduces that to the miter's diagonal.

spec-miter-∘ : (C : Circuit n) (ξ : PathSum n k m) →
               (⟦ C ⟧ ≋ ξ ⇔ (⟦ C † ⟧ ∘ᴾ ξ) ≋ idPS)
spec-miter-∘ = MitC.spec-miter-∘

spec-miter-restriction : (C : Circuit n) (ξ : PathSum n k m) →
                         WellFormed ξ →
                         (⟦ C ⟧ ≋ ξ ⇔ Restriction-id (⟦ C † ⟧ ∘ᴾ ξ))
spec-miter-restriction = MitC.spec-miter-restriction

spec-miter-∘-Rk : (C : K.Circuit n) (ξ : PathSum n k m) →
                  (K.⟦ C ⟧ ≋ ξ ⇔ (K.⟦ C KA.† ⟧ ∘ᴾ ξ) ≋ idPS)
spec-miter-∘-Rk = KMC.spec-miter-∘


------------------------------------------------------------------------
-- Equivalence over {H, CNOT, R_k}, and translation validation
-- (PathSum.CRK.Miter, PathSum.CRK.Equivalence, PathSum.CRK.Validation,
-- PathSum.CRK.Specification)

-- The miter for the paper's gate set, and equivalence of two of its
-- Clifford circuits decided by the paper's route: Gaussian elimination
-- on the miter's restriction, then the reduction of corollary 4.4.

miter-Rk : (C₁ C₂ : K.Circuit n) →
           (K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧ ⇔ K.⟦ C₁ ++ C₂ KA.† ⟧ ≋ idPS)
miter-Rk = KM.miter

equivalence-gauss : (C₁ C₂ : K.Circuit n) →
  K.level C₁ ≤ 2 → K.level C₂ ≤ 2 →
  (K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧ ⇔
   ∃ λ m′ → ∃ λ (ξ : PathSum n (K.norm (C₁ ++ C₂ KA.†)) m′) →
     GC.⟦ C₁ ++ C₂ KA.† ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
       (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
equivalence-gauss = KEq.equivalence-gauss

equivalence-decidable-gauss : (C₁ C₂ : K.Circuit n) →
  K.level C₁ ≤ 2 → K.level C₂ ≤ 2 → Dec (K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧)
equivalence-decidable-gauss = KEq.equivalence-decidable-gauss

-- Section 5.1's translation validation, for circuits at any level of
-- the Clifford hierarchy (Clifford+T, say): reduce the miter's reified
-- restriction by any rules of figure 2.  Reaching |x⟩ ↦ |x⟩ proves the
-- circuits equivalent; lemma 4.2's pattern (Q odd somewhere) refutes
-- them.  Sound at every level, but complete only for Clifford circuits,
-- as the paper says: a non-Clifford miter may get stuck.

validation-sound : (C₁ C₂ : K.Circuit n)
  {ξ : PathSum n (K.norm (C₁ ++ C₂ KA.†)) m′} →
  GC.⟦ C₁ ++ C₂ KA.† ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n 0 0} → ξ ⟶ᶠ* ξ′ →
  (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) → phase ξ′ ≈[ pow M ] 0ᴾ →
  K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧
validation-sound = KVal.validation-sound

validation-refuted-interference : (C₁ C₂ : K.Circuit n)
  {ξ : PathSum n (K.norm (C₁ ++ C₂ KA.†)) m′} →
  GC.⟦ C₁ ++ C₂ KA.† ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ″ : PathSum n k″ (suc m″)} → ξ ⟶ᶠ* ξ″ →
  (Q : Poly n m″) →
  head-part (phase ξ″) ≈[ pow M ] (½ ·ᴾ Q) →
  (∀ w → NoVar (+ 2) y₀ (out ξ″ w)) →
  (∀ j → NoVar (+ 2) y[ j ] Q) →
  ¬ (Q ≈[ + 2 ] 0ᴾ) →
  ¬ (K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧)
validation-refuted-interference = KVal.validation-refuted-interference

validation-clifford : (C₁ C₂ : K.Circuit n) →
  K.level C₁ ≤ 2 → K.level C₂ ≤ 2 →
  {ξ : PathSum n (K.norm (C₁ ++ C₂ KA.†)) m′} →
  GC.⟦ C₁ ++ C₂ KA.† ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n k′ m″} → ξ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
  (K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧ ⇔
   (m″ ≡ 0 × k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
validation-clifford = KVal.validation-clifford

-- Section 5.2's check of a circuit against a path-sum specification,
-- through reducts of the composed miter.

spec-sound : (C : K.Circuit n) (ξ : PathSum n k m)
             {ξ′ : PathSum n 0 0} → (K.⟦ C KA.† ⟧ ∘ᴾ ξ) ⟶ᶠ* ξ′ →
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
             phase ξ′ ≈[ pow M ] 0ᴾ →
             K.⟦ C ⟧ ≋ ξ
spec-sound = KSpec.spec-sound


------------------------------------------------------------------------
-- Section 5.2: the quantum Fourier transform, for every n
-- (PathSum.CRK.Controlled, PathSum.QFT, PathSum.QFT.*)

-- The paper verifies "a circuit from [Nielsen–Chuang] together with a
-- final qubit permutation correction" against
-- QFT_n : |x⟩ ↦ 1/√2^n Σ_y e^{2πi [x][y]/2^n} |y⟩.  Its controlled
-- rotations are built here from {H, CNOT, R_k}: R_(k+1) c; R_(k+1) t;
-- CNOT; R_(k+1)† t; CNOT is the diagonal e^{2πi x_c x_t/2^k}.  At the
-- fixed precision 2^M the family needs n + 1 ≤ M; the equivalence is
-- proved through the amplitudes, not by a run of figure 2.

CR-≋ : ∀ k → suc k ≤ M → (c t : Fin n) (c≢t : c ≢ t) →
       K.⟦ KCR.CR k c t c≢t ⟧ ≋ KCR.CRᴾ k c t
CR-≋ = KCR.CR-≋

QFT-spec-phase : (x y : Assign n) →
                 eval (phase (QS.QFTˢ n)) x y ≡
                 pow (M ∸ n) *ℤ (QS.bin x *ℤ QS.bin y)
QFT-spec-phase = QS.eval-QFTˢ

QFT-≋ : ∀ n → suc n ≤ M → K.⟦ QC.QFTC n ⟧ ≋ QS.QFTˢ n
QFT-≋ = QFT.QFT-≋

QFT-matrix : ∀ n → suc n ≤ M → (x z : Assign n) →
             amp K.⟦ QC.QFTC n ⟧ x z ≐
             zpow (pow (M ∸ n) *ℤ (QS.bin x *ℤ QS.bin z))
QFT-matrix = QFT.QFTC-matrix

-- At a fixed precision the specification is the Fourier transform --
-- equivalently, unitary -- exactly up to n = M.

QFT-spec-Unitary⇔ : ∀ n → Unitary (QS.QFTˢ n) ⇔ n ≤ M
QFT-spec-Unitary⇔ = QU.QFTˢ-Unitary⇔

-- The final permutation is a relabelling of the outputs, and it cannot
-- be dropped from two qubits on; without it the circuit has exactly n²
-- Clifford gates -- table 2's 256 and 961 for n = 16 and 31.

QFT-without-permutation : ∀ n → 2 ≤ n → suc n ≤ M →
                          ¬ (K.⟦ QC.QFT₀ n ⟧ ≋ QS.QFTˢ n)
QFT-without-permutation = QR.QFT₀-not-spec

QFT-cliffords : ∀ n → QCnt.cliffords (QC.QFT₀ n) ≡ n * n
QFT-cliffords = QCnt.cliffords-QFT₀


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
