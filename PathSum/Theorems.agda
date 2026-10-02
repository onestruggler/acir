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
-- proved in a cost model for circuits over {H, S, CZ}
-- (PathSum.Cost.Corollary, the last section below).
--
-- Around that core: lemma 2.5 for every Boolean polynomial; composition
-- of path-sums (definition 2.6), proposition 2.7's operator equation,
-- and remark 2.8 up to ≋ (PathSum.Compose); definition 2.9 over the
-- paper's own gate set {H, CNOT, R_k} with propositions 2.10 and 2.14
-- (PathSum.CRK), compositionally as well; the size half of corollary
-- 2.15, with an interpreter building the representation gate by gate
-- (PathSum.Size); section 5.2's quantum Fourier transform for every n
-- within the precision (PathSum.QFT), its n-bit Toffoli gates with
-- ancillas for every n, both the standard decomposition -- the circuit
-- its tool verified included, with table 2's rows exactly
-- (PathSum.ToffoliN) -- and Maslov's with relative-phase Toffoli gates,
-- their phases cancelling exactly (PathSum.Maslov), its out-of-place
-- adder for every n -- the circuit its tool generates included, with
-- table 2's rows exactly (PathSum.Adder) -- and its hidden shift
-- algorithm for every size, bent function and shift, as path-sums and
-- as figure 3's circuits, with the calculus finding |s⟩ and |s⟩|s⟩ on
-- them (PathSum.HiddenShift); Z[ζ] as a commutative ring,
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
-- (sound, and complete for Clifford); section 4's incompleteness beyond
-- Clifford -- the paper's irreducible identity, non-unique normal
-- forms, an equivalent level-3 pair validation cannot settle -- and
-- its remedy, a complete (exponential) decision by expanding the
-- variables reduction leaves (PathSum.Expand); and the paper's worked
-- examples, checked at precision M₀ = 0 (PathSum.Examples, imported
-- below).
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
-- printed is the identity rather than ω·I, the fourth line of example
-- 3.4 does not follow from the third, section 5.2's formula for the
-- shifted function f′ drops the shift, and its adder has 5n qubits for
-- n ≥ 2, as its table and its tool's circuit say, not the text's
-- 5n − 1 bits.
-- One gap is filled: the proof of corollary 4.4 reduces by arbitrary
-- rules, which needs every rule to preserve order ≤ 2 -- lemma 2.13
-- covers only linear substitutions, and PathSum.Full.Clifford supplies
-- the rest.
--
-- The polynomial time bounds (proposition 3.2, corollaries 2.15 and
-- 4.4, the abstract's equivalence procedure) are proved in a cost
-- model, not on a machine (PathSum.Cost): for a fixed order and the
-- linear rules, and corollary 4.4's for circuits over {H, S, CZ}.
--
-- Not formalised: running times on a machine and complexity classes
-- (footnote 2's P = co-NP among them); the time bounds for [Case] and
-- non-linear quotients, and by the Gaussian route; constant inputs,
-- beyond restricting to the columns where an ancilla is |0⟩
-- (PathSum.Ancilla); the symmetric monoidal laws of remark 2.8 beyond
-- interchange and SWAP naturality; and section 5's benchmarks as runs
-- of the tool.
--
-- Each section's banner names the modules its results come from;
-- results proved here from them are stated with their proofs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _<_)

module PathSum.Theorems (M₀ : ℕ) where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Nat.Base using
  (_+_; _*_; _∸_; _^_; _≤_; _⊔_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _-_)
  renaming (_*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.List.Base using (List; []; _++_; length; map; upTo)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (Σ; _×_; _,_; ∃; proj₁; proj₂)
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
open import PathSum.Assign using (same; [_]ᶻ)
open import PathSum.AssignSum using (Σᶻ)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Cyclotomic M₀ using
  (0ᴬ; _≐_; Σᴮ; zpow; scale; scale-map)
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

import PathSum.Cost
module PC = PathSum.Cost

import PathSum.Cost.Normalise
module CN = PathSum.Cost.Normalise M

import PathSum.Cost.Equivalence
import PathSum.Cost.Normalise.Equivalence
import PathSum.Cost.Excluded

import PathSum.Cost.Corollary
module CCor = PathSum.Cost.Corollary M₀

import PathSum.Cost.Interpreter
module CInt = PathSum.Cost.Interpreter M

import PathSum.Full.Order2
module FO2 = PathSum.Full.Order2 M₀

import PathSum.Full.Order2.Sharp

import PathSum.Cost.Irreducible
module CIrr = PathSum.Cost.Irreducible M₀

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

import PathSum.Ancillas
module Anc = PathSum.Ancillas M₀
open Anc using (_≋[_]₀*_; Clean; set0ˢ)

import PathSum.Classical
module Cl = PathSum.Classical M₀
open Cl using (_computes_)

import PathSum.RelativePhase
module RP = PathSum.RelativePhase M₀
open RP using (_computes_up-to_)

import PathSum.CRK.Path
module KP = PathSum.CRK.Path M₀

import PathSum.Toffoli
module Tof = PathSum.Toffoli M₀

import PathSum.Toffoli.Netlist
module TNet = PathSum.Toffoli.Netlist M₀

import PathSum.ToffoliN.Chain
module TCh = PathSum.ToffoliN.Chain M₀

import PathSum.ToffoliN
module TN = PathSum.ToffoliN M₀

import PathSum.ToffoliN.Tool
module TT = PathSum.ToffoliN.Tool M₀

import PathSum.ToffoliN.Feynman
module TF = PathSum.ToffoliN.Feynman M₀

import PathSum.Toffoli.Depth3
module Tof3 = PathSum.Toffoli.Depth3 M₀

import PathSum.Maslov.Gate
module MGt = PathSum.Maslov.Gate M₀

import PathSum.Maslov.Gate4
module MG4 = PathSum.Maslov.Gate4 M₀

import PathSum.Maslov.Chain
module MCh = PathSum.Maslov.Chain M₀

import PathSum.Maslov
module Msl = PathSum.Maslov M₀

import PathSum.Maslov.Feynman
module MF = PathSum.Maslov.Feynman M₀

import PathSum.Adder.Binary
module ABin = PathSum.Adder.Binary

import PathSum.Adder.Layout
module AL = PathSum.Adder.Layout

import PathSum.Adder.Ripple
module ARip = PathSum.Adder.Ripple

import PathSum.Adder.Circuit
module ACi = PathSum.Adder.Circuit M₀

import PathSum.Adder.Spec
module ASp = PathSum.Adder.Spec M₀

import PathSum.Adder
module Add = PathSum.Adder M₀

import PathSum.Adder.CarryRipple
module ACR = PathSum.Adder.CarryRipple

import PathSum.Adder.Tool
module AT = PathSum.Adder.Tool M₀

import PathSum.Adder.Feynman
module AF = PathSum.Adder.Feynman M₀

import PathSum.CRK.Qubits
module Qb = PathSum.CRK.Qubits M₀

import PathSum.HiddenShift.Walsh
module HW = PathSum.HiddenShift.Walsh
open HW using (0ᵃ; _⧺_; mm; dual; dot; RespectsB)

import PathSum.HiddenShift
module HSh = PathSum.HiddenShift M₀

import PathSum.HiddenShift.Simulation
module HSim = PathSum.HiddenShift.Simulation M₀

import PathSum.HiddenShift.Gates
module HGa = PathSum.HiddenShift.Gates M₀

import PathSum.HiddenShift.Circuit
module HCi = PathSum.HiddenShift.Circuit M₀

import PathSum.HiddenShift.Symbolic
module HSy = PathSum.HiddenShift.Symbolic M₀

import PathSum.HiddenShift.Reduces
module HRe = PathSum.HiddenShift.Reduces M₀

import PathSum.Ancilla.Register
module AReg = PathSum.Ancilla.Register M₀

import PathSum.HiddenShift.Exists
module HEx = PathSum.HiddenShift.Exists M₀

import PathSum.HiddenShift.ExistsCircuit
module HEC = PathSum.HiddenShift.ExistsCircuit M₀

import PathSum.HiddenShift.ExistsSymbolic
module HES = PathSum.HiddenShift.ExistsSymbolic M₀

import PathSum.Expand
module Exp = PathSum.Expand M₀

import PathSum.CRK.Expand
module KE = PathSum.CRK.Expand M₀

import PathSum.Hardness.CNF
module HCNF = PathSum.Hardness.CNF

import PathSum.Hardness.Netlist
module HNet = PathSum.Hardness.Netlist

import PathSum.Hardness
module Hard = PathSum.Hardness M₀

import PathSum.Hardness.Certificate
module HCert = PathSum.Hardness.Certificate

import PathSum.Hardness.Prepared
module HPrep = PathSum.Hardness.Prepared M₀

import PathSum.Hardness.Conditional
module HCond = PathSum.Hardness.Conditional M₀

import PathSum.Hardness.Blowup
module HBlow = PathSum.Hardness.Blowup M₀

import PathSum.Full.Obstruction
import PathSum.CRK.WithX
import PathSum.Gauss.Single
import PathSum.Polynomial.SubstVar

-- Section 4's incompleteness witnesses, closed at M₀ = 0; stated below
-- through their own names only.

import PathSum.Examples.Incomplete
module ExInc = PathSum.Examples.Incomplete

import PathSum.Examples.ValidationIncomplete
module ExVInc = PathSum.Examples.ValidationIncomplete

-- Closed cross-checks of the hidden-shift development, at M₀ = 0.

import PathSum.HiddenShift.Example
import PathSum.HiddenShift.CircuitExample

-- Closed cross-checks of footnote 2's reduction and its certificates.

import PathSum.Hardness.Example

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
-- (This search is exponential; the polynomial one, on sparse
-- path-sums in a cost model, is proposition-3-2 in the last section.)

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
-- decidability in polynomial time, is corollary-4-4-polytime in the
-- last section, in a cost model.)

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

-- At order 2 the linear rules already decide irreducibility under all
-- of figure 2 (PathSum.Full.Order2): every step of figure 2 -- a
-- Boolean-valued quotient, [Case], at any variables -- implies that
-- some linear rule applies.  So the corollary holds at every end of a
-- reduction where no linear rule applies.  (Not at order 3:
-- PathSum.Full.Order2.Sharp.order-3-gap is a path-sum of order 3 that
-- no linear rule reduces and figure 2 does.)

Irreducible⇔Irreducibleᶠ : (ξ : PathSum n k m) → Ord≤ 2 (phase ξ) →
                           Irreducible ξ ⇔ Irreducibleᶠ ξ
Irreducible⇔Irreducibleᶠ = FO2.Irreducible⇔Irreducibleᶠ

corollary-4-4-normalᴸ : (C : Circuit n) {ξ′ : PathSum n k′ m′} →
  ⟦ C ⟧ᴿ ⟶ᶠ* ξ′ → Irreducible ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (m′ ≡ 0 × k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-normalᴸ = FO2.corollary-4-4-normalᴸ

circuit-decidableᶠ : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidableᶠ = FlCl.circuit-decidableᶠ


------------------------------------------------------------------------
-- Section 4: beyond Clifford the calculus is incomplete, and the
-- paper's remedy (PathSum.Examples.Incomplete,
-- PathSum.Examples.ValidationIncomplete, PathSum.Expand,
-- PathSum.CRK.Expand)

-- "The normal forms are not necessarily unique and hence our reduction
-- system is incomplete": the paper's Clifford+T identity has the
-- irreducible path-sum it prints (checked coefficient by coefficient
-- against the circuit read off its figure), so two equivalent
-- irreducible path-sums -- it and |x⟩ ↦ |x⟩ -- have 8 and 0 path
-- variables.  Closed facts at M₀ = 0.

normal-forms-not-unique : ¬ ExInc.UniqueNormalForms
normal-forms-not-unique = ExInc.normal-forms-not-unique

-- The same defeats translation validation beyond Clifford: two
-- equivalent level-3 circuits (the paper's box without its X gates,
-- and a box that undoes it) whose miter's reified restriction no rule
-- of figure 2 reduces, so the syntactic test is never reached --
-- whereas at level 2 every normal form decides (KE.complete-2).

validation-not-complete-3 : ¬ PathSum.CRK.Expand.Complete 0 3
validation-not-complete-3 = ExVInc.not-complete-3

validation-complete-2 : KE.Complete 2
validation-complete-2 = KE.complete-2

-- "A complete verification procedure could proceed by explicitly
-- expanding the values of remaining variables ... after all possible
-- reductions have been made": reduce to a normal form under all of
-- figure 2, then sum what is left over its path variables.  Sound and
-- complete for every path-sum, hence for equivalence of circuits at
-- every level; exponential, and on Clifford inputs never expanding.

decide-id : (ξ : PathSum n k m) → Dec (ξ ≋ idPS)
decide-id = Exp.decide-id

validation-decidableᵉ : (C₁ C₂ : K.Circuit n) → Dec (KE.Equivalent C₁ C₂)
validation-decidableᵉ = KE.validation-decidableᵉ

-- Footnote 2, its logical half: were normal forms unique, a normal
-- form keeping a path variable would never be the identity, and the
-- expansion would never be needed.  (Its complexity half is the next
-- section's reduction; complexity classes, and P = co-NP itself, are
-- not formalised.)

unique⇒no-expansion : Exp.UniqueNormalForms →
                      (ξ′ : PathSum n k (suc m)) → Irreducibleᶠ ξ′ →
                      ¬ (ξ′ ≋ idPS)
unique⇒no-expansion = Exp.unique⇒no-expansion


------------------------------------------------------------------------
-- Footnote 2: the reduction from unsatisfiability (PathSum.Hardness,
-- PathSum.Hardness.*)

-- "Equivalence checking of reversible Boolean circuits ... is
-- co-NP-complete": the reduction behind it, for every CNF formula φ --
-- a Clifford+T circuit (NOT, Toffoli and CNOT gates, NOT as H R₁ H)
-- that is the identity on the inputs whose ancillas are |0⟩ exactly
-- when φ is unsatisfiable, also with the ancillas read as the constant
-- 0 ...

hardness : (φ : HCNF.CNF n) →
           (KP.⟦ Hard.circuit φ ⟧ ≋[ HNet.ancillas φ ]₀* idPS) ⇔
           HCNF.Unsatisfiable φ
hardness = Hard.hardness

hardness-set0 : (φ : HCNF.CNF n) →
                (set0ˢ (HNet.ancillas φ) KP.⟦ Hard.circuit φ ⟧ ≋
                 set0ˢ (HNet.ancillas φ) idPS) ⇔ HCNF.Unsatisfiable φ
hardness-set0 = Hard.hardness-set0

-- ... and of linear size in ‖ φ ‖, the literal occurrences plus the
-- clauses: wires, path variables, T gates, gates.  (Only the size of
-- the reduction's output is proved, not its running time.)

hardness-wires : (φ : HCNF.CNF n) → HNet.wires φ ≤ n + 3 * HCNF.‖ φ ‖ + 3
hardness-wires = HNet.wires-bound

hardness-paths : (φ : HCNF.CNF n) →
                 KP.paths (Hard.circuit φ) ≡ 4 * HCNF.‖ φ ‖ + 4
hardness-paths = Hard.circuit-paths

hardness-tcount : (φ : HCNF.CNF n) →
                  TNet.tcount (Hard.circuit φ) ≡ 14 * HCNF.‖ φ ‖
hardness-tcount = Hard.circuit-tcount

hardness-gates : (φ : HCNF.CNF n) →
                 length (Hard.circuit φ) ≤ 40 * HCNF.‖ φ ‖ + 9
hardness-gates = Hard.circuit-length-bound

-- Membership, as a certificate check: the circuit is not the identity
-- on the clean inputs exactly when some input, simulated through the
-- netlist, is rejected -- in a linear number of counted simulation
-- steps (a count, not time on a machine).

circuit-certificate :
  (φ : HCNF.CNF n) →
  (¬ (KP.⟦ Hard.circuit φ ⟧ ≋[ HNet.ancillas φ ]₀* idPS)) ⇔
  (∃ λ x → proj₁ (HCert.check (HNet.ancillas φ) (HNet.netlist φ) [] x)
             ≡ true)
circuit-certificate = HPrep.circuit-certificate

certificate-steps :
  (φ : HCNF.CNF n) (x : HCNF.Assignment (HNet.wires φ)) →
  proj₂ (HCert.check (HNet.ancillas φ) (HNet.netlist φ) [] x) ≤
  n + 18 * HCNF.‖ φ ‖ + 10
certificate-steps = HCert.check-steps-bound

-- The footnote's conditional: with the ancillas prepared (read as 0,
-- their inputs returned), the reduction's path-sum is the identity
-- exactly when φ is unsatisfiable; were normal forms unique -- they
-- are not, normal-forms-not-unique above -- the syntactic test on its
-- normal form would decide unsatisfiability.  One direction needs no
-- hypothesis.

cleanPS-identity⇔unsat : (φ : HCNF.CNF n) →
                         (HPrep.cleanPS φ ≋ idPS) ⇔ HCNF.Unsatisfiable φ
cleanPS-identity⇔unsat = HPrep.cleanPS-identity⇔unsat

unsat-by-normalisation : Exp.UniqueNormalForms → (φ : HCNF.CNF n) →
                         HCNF.Unsatisfiable φ ⇔
                         HCond.NormalFormId (HPrep.cleanPS φ)
unsat-by-normalisation = HCond.unsat-by-normalisation

normal-form-refutes : (φ : HCNF.CNF n) →
                      HCond.NormalFormId (HPrep.cleanPS φ) →
                      HCNF.Unsatisfiable φ
normal-form-refutes = HCond.normal-form-refutes

-- What the hypothesis would force: for the single clause x₁ ∨ … ∨ x_n,
-- every irreducible reduct of the prepared path-sum -- 4n + 8 path
-- variables -- has, on the target's output, an odd coefficient on
-- every nonempty monomial over the inputs, 2^n − 1 of them (a count in
-- words).  Written as lists of terms, such normal forms are
-- exponentially large, so uniqueness and proposition 3.2's polynomial
-- time exclude each other on these instances -- an argument about a
-- representation and a running time, neither of them formalised.

unique⇒orφ : Exp.UniqueNormalForms → (n : ℕ) →
             ∀ {k′ m′} (ξ′ : PathSum (HNet.wires (HBlow.orφ n)) k′ m′) →
             HPrep.cleanPS (HBlow.orφ n) ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
             HBlow.OddOnInputs (HBlow.orφ n) ξ′
unique⇒orφ = HBlow.unique⇒orφ


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
-- Section 5.2: n-bit Toffoli gates, for every n (PathSum.Toffoli,
-- PathSum.ToffoliN, PathSum.ToffoliN.Tool, PathSum.ToffoliN.Feynman,
-- PathSum.Ancillas, PathSum.Classical)

-- The building block: the seven-T Toffoli circuit on any three distinct
-- wires of any circuit computes |x⟩ ↦ |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩ -- the
-- classical path-sum TG.toffoliˢ, phase 0, no path variables.

-- (Stated with CRK.Path's ⟦_⟧ and Toffoli's own tof, as Toffoli states
-- it: with K.⟦_⟧ and Toffoli.Gate's tof Agda unfolds the fifteen-gate
-- circuit to compare the two statements, for minutes.)

tof-spec : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
           (c₂≢t : c₂ ≢ t) →
           KP.⟦ Tof.tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ ≋ Tof.toffoliˢ c₁ c₂ t
tof-spec = Tof.tof-spec

-- "The standard decomposition into 2(n − 3) + 1 Toffoli gates and
-- n − 3 ancillas": on the inputs whose ancillas are |0⟩ it computes
-- Toffoli_n : |x⟩ ↦ |x₁ … (x_n ⊕ x₁ ⋯ x_(n−1))⟩, it leaves the ancillas
-- clean, and with the ancillas read as the constant 0 it is Toffoli_n
-- outright.  The proof composes classical path-sums (proposition 2.7)
-- rather than running figure 2.

Toffoliₙ-spec : (n : ℕ) (p : 3 ≤ n) →
                K.⟦ TN.Toffoliₙ n p ⟧ ≋[ TCh.anc (TCh.standard n p) ]₀*
                  TCh.toffoliₙˢ (TCh.standard n p)
Toffoliₙ-spec = TN.Toffoliₙ-spec

Toffoliₙ-clean : (n : ℕ) (p : 3 ≤ n) → ∀ x z →
                 Clean (TCh.anc (TCh.standard n p)) x → (i : Fin (n ∸ 3)) →
                 z (TCh.anc (TCh.standard n p) i) ≡ true →
                 amp K.⟦ TN.Toffoliₙ n p ⟧ x z ≐ 0ᴬ
Toffoliₙ-clean = TN.Toffoliₙ-clean

Toffoliₙ-set0 : (n : ℕ) (p : 3 ≤ n) →
                set0ˢ (TCh.anc (TCh.standard n p)) K.⟦ TN.Toffoliₙ n p ⟧ ≋
                set0ˢ (TCh.anc (TCh.standard n p))
                      (TCh.toffoliₙˢ (TCh.standard n p))
Toffoliₙ-set0 = TN.Toffoliₙ-set0

-- Table 2's rows Toffoli50 and Toffoli100, computed from the circuit:
-- qubits (the wires its gates touch, as the tool counts them), path
-- variables and T gates all as printed.  Its Clifford gates are eight
-- per Toffoli gate, 760 and 1560, where the table has nine, 855 and
-- 1755: the tool writes each Toffoli gate with its own sixteen-gate
-- circuit, below.

table-2-Toffoli50 : (p : 3 ≤ 50) →
                    (Qb.qubits (TN.Toffoliₙ 50 p) ≡ 97)
                    × (K.paths (TN.Toffoliₙ 50 p) ≡ 190)
                    × (TNet.tcount (TN.Toffoliₙ 50 p) ≡ 665)
table-2-Toffoli50 = TN.table-2-Toffoli50

table-2-Toffoli100 : (p : 3 ≤ 100) →
                     (Qb.qubits (TN.Toffoliₙ 100 p) ≡ 197)
                     × (K.paths (TN.Toffoliₙ 100 p) ≡ 390)
                     × (TNet.tcount (TN.Toffoliₙ 100 p) ≡ 1365)
table-2-Toffoli100 = TN.table-2-Toffoli100

Toffoliₙ-qubits : (n : ℕ) (p : 3 ≤ n) →
                  Qb.qubits (TN.Toffoliₙ n p) ≡ n + (n ∸ 3)
Toffoliₙ-qubits = TN.Toffoliₙ-qubits

Toffoliₙ-cliffords : (n : ℕ) (p : 3 ≤ n) →
                     QCnt.cliffords (TN.Toffoliₙ n p) ≡
                     (2 * (n ∸ 3) + 1) * 8
Toffoliₙ-cliffords = TN.Toffoliₙ-cliffords

cliffords-Toffoli50 : (p : 3 ≤ 50) → QCnt.cliffords (TN.Toffoliₙ 50 p) ≡ 760
cliffords-Toffoli50 = TN.cliffords-Toffoli50

cliffords-Toffoli100 : (p : 3 ≤ 100) →
                       QCnt.cliffords (TN.Toffoliₙ 100 p) ≡ 1560
cliffords-Toffoli100 = TN.cliffords-Toffoli100

-- The circuit the paper's tool verified (Feynman's toffoliN): the same
-- V-chain, each Toffoli gate written with the tool's sixteen-gate
-- circuit and the uncomputing one with its adjoint.  Gate for gate it
-- is the list the tool produces, for every n ≥ 3; its path-sum is ≋
-- the circuit's above on every input, so it is correct on the clean
-- columns; and it has table 2's rows in all four columns.

ToffoliNᶜ-tool : (n : ℕ) (p : 3 ≤ n) →
                 map AF.prim (TT.ToffoliNᶜ n p) ≡
                 TF.toffoliNᵀ (λ i → n + i) (upTo n)
ToffoliNᶜ-tool = TF.ToffoliNᶜ-tool

ToffoliNᶜ-≋ : (n : ℕ) (p : 3 ≤ n) →
              K.⟦ TT.ToffoliNᶜ n p ⟧ ≋ K.⟦ TN.Toffoliₙ n p ⟧
ToffoliNᶜ-≋ = TT.ToffoliNᶜ-≋

ToffoliNᶜ-spec : (n : ℕ) (p : 3 ≤ n) →
                 K.⟦ TT.ToffoliNᶜ n p ⟧ ≋[ TCh.anc (TCh.standard n p) ]₀*
                   TCh.toffoliₙˢ (TCh.standard n p)
ToffoliNᶜ-spec = TT.ToffoliNᶜ-spec

ToffoliNᶜ-clean : (n : ℕ) (p : 3 ≤ n) → ∀ x z →
                  Clean (TCh.anc (TCh.standard n p)) x →
                  (i : Fin (n ∸ 3)) →
                  z (TCh.anc (TCh.standard n p) i) ≡ true →
                  amp K.⟦ TT.ToffoliNᶜ n p ⟧ x z ≐ 0ᴬ
ToffoliNᶜ-clean = TT.ToffoliNᶜ-clean

ToffoliNᶜ-set0 : (n : ℕ) (p : 3 ≤ n) →
                 set0ˢ (TCh.anc (TCh.standard n p)) K.⟦ TT.ToffoliNᶜ n p ⟧ ≋
                 set0ˢ (TCh.anc (TCh.standard n p))
                       (TCh.toffoliₙˢ (TCh.standard n p))
ToffoliNᶜ-set0 = TT.ToffoliNᶜ-set0

table-2-Toffoli50-tool :
  (p : 3 ≤ 50) →
  (Qb.qubits (TT.ToffoliNᶜ 50 p) ≡ 97) × (K.paths (TT.ToffoliNᶜ 50 p) ≡ 190)
  × (QCnt.cliffords (TT.ToffoliNᶜ 50 p) ≡ 855)
  × (TNet.tcount (TT.ToffoliNᶜ 50 p) ≡ 665)
table-2-Toffoli50-tool = TT.Toffoli50ᵀ

table-2-Toffoli100-tool :
  (p : 3 ≤ 100) →
  (Qb.qubits (TT.ToffoliNᶜ 100 p) ≡ 197)
  × (K.paths (TT.ToffoliNᶜ 100 p) ≡ 390)
  × (QCnt.cliffords (TT.ToffoliNᶜ 100 p) ≡ 1755)
  × (TNet.tcount (TT.ToffoliNᶜ 100 p) ≡ 1365)
table-2-Toffoli100-tool = TT.Toffoli100ᵀ


------------------------------------------------------------------------
-- Section 5.2: the Maslov decomposition, for every n
-- (PathSum.RelativePhase, PathSum.Maslov, PathSum.Maslov.*)

-- The relative-phase Toffoli gates of [23] -- the three-qubit one
-- (four T gates; figure 3's dashed box) and the Toffoli-4 one (eight;
-- figure 4, the paper's tool's rToffoli4) -- compute the Toffoli
-- functions only up to a diagonal phase, computed exactly here ...

rtof-up-to : (c₁ c₂ t : Fin n) (c₁≢t : c₁ ≢ t) (c₂≢t : c₂ ≢ t) →
             KP.⟦ MGt.rtof c₁ c₂ t c₁≢t c₂≢t ⟧
               computes Tof.toffoli c₁ c₂ t up-to MGt.rtof-phase c₁ c₂ t
rtof-up-to = MGt.rtof-up-to

rc3x-up-to : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d) (c≢d : c ≢ d) →
             KP.⟦ MG4.rc3x a b c d a≢d b≢d c≢d ⟧
               computes MG4.toffoli₄ a b c d up-to MG4.rc3x-phase a b c d
rc3x-up-to = MG4.rc3x-up-to

-- ... so a gate followed by its adjoint is exactly the identity, but a
-- gate followed by itself -- as a netlist of Toffoli gates would be
-- expanded -- is not: the phases are real.

rc3x-rc3x† : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
             (c≢d : c ≢ d) →
             KP.⟦ MG4.rc3x a b c d a≢d b≢d c≢d
                  ++ MG4.rc3x a b c d a≢d b≢d c≢d KA.† ⟧ computes (λ x → x)
rc3x-rc3x† = MG4.rc3x-rc3x†

rc3x-rc3x-not-id : (a b c d : Fin n) (a≢d : a ≢ d) (b≢d : b ≢ d)
                   (c≢d : c ≢ d) →
                   ¬ (KP.⟦ MG4.rc3x a b c d a≢d b≢d c≢d
                          ++ MG4.rc3x a b c d a≢d b≢d c≢d ⟧
                        computes (λ x → x))
rc3x-rc3x-not-id = MG4.rc3x-rc3x-not-id

-- "The Maslov decomposition [23] using relative phase Toffolis and
-- ⌈(n − 3)/2⌉ ancillas", exactly as the paper's tool builds it -- its
-- maslovToffoli, gate for gate, read into the tool's primitives: a
-- chain of Toffoli-4 gates collects the controls into the ancillas, a
-- CNOT (at odd n the tool's Toffoli circuit) writes the target, and
-- the chain's adjoint uncomputes ...

Maslovₙ-tool : (n : ℕ) (p : 3 ≤ n) →
               map AF.prim (Msl.Maslovₙ n p) ≡
               MF.maslovToffoliᵀ (λ i → n + i) (upTo n)
Maslovₙ-tool = MF.Maslovₙ-tool

-- ... On every input its phases cancel exactly -- it computes a
-- permutation -- which on the inputs whose ancillas are |0⟩ is
-- Toffoli_n; it leaves them clean, and with them read as the constant
-- 0 it is Toffoli_n outright.

Maslovₙ-computes : (n : ℕ) (p : 3 ≤ n) →
                   KP.⟦ Msl.Maslovₙ n p ⟧
                     computes MCh.applyᴹ (MCh.standardᴹ n p)
Maslovₙ-computes = Msl.Maslovₙ-computes

Maslovₙ-spec : (n : ℕ) (p : 3 ≤ n) →
               KP.⟦ Msl.Maslovₙ n p ⟧ ≋[ MCh.anc (MCh.standardᴹ n p) ]₀*
                 MCh.toffoliᴹˢ (MCh.standardᴹ n p)
Maslovₙ-spec = Msl.Maslovₙ-spec

Maslovₙ-clean : (n : ℕ) (p : 3 ≤ n) → ∀ x z →
                Clean (MCh.anc (MCh.standardᴹ n p)) x →
                (i : Fin ⌊ n ∸ 2 /2⌋) →
                z (MCh.anc (MCh.standardᴹ n p) i) ≡ true →
                amp KP.⟦ Msl.Maslovₙ n p ⟧ x z ≐ 0ᴬ
Maslovₙ-clean = Msl.Maslovₙ-clean

Maslovₙ-set0 : (n : ℕ) (p : 3 ≤ n) →
               set0ˢ (MCh.anc (MCh.standardᴹ n p)) KP.⟦ Msl.Maslovₙ n p ⟧ ≋
               set0ˢ (MCh.anc (MCh.standardᴹ n p))
                     (MCh.toffoliᴹˢ (MCh.standardᴹ n p))
Maslovₙ-set0 = Msl.Maslovₙ-set0

-- Its resources: every one of its n + ⌈(n − 3)/2⌉ wires is touched,
-- so that many qubits as the tool counts them; at even n, 4(n − 2)
-- path variables, 8(n − 2) T gates and 10(n − 2) + 1 Clifford gates
-- (at odd n one T gate, two Clifford gates and two path variables
-- fewer) -- one T gate more than [23]'s own construction, which keeps
-- an exact Toffoli gate in the middle: 8n − 17.  Table 2's rows
-- Maslov50 and Maslov100, computed from the circuit, are all as
-- printed.

Maslovₙ-qubits : (n : ℕ) (p : 3 ≤ n) →
                 Qb.qubits (Msl.Maslovₙ n p) ≡ n + ⌈ n ∸ 3 /2⌉
Maslovₙ-qubits = Msl.Maslovₙ-qubits

Maslovₙ-paths : (n : ℕ) (p : 3 ≤ n) →
                KP.paths (Msl.Maslovₙ n p) + 2 * Msl.parity n ≡ 4 * (n ∸ 2)
Maslovₙ-paths = Msl.Maslovₙ-paths-closed

Maslovₙ-tcount : (n : ℕ) (p : 3 ≤ n) →
                 TNet.tcount (Msl.Maslovₙ n p) + Msl.parity n ≡ 8 * (n ∸ 2)
Maslovₙ-tcount = Msl.Maslovₙ-tcount-closed

Maslovₙ-cliffords : (n : ℕ) (p : 3 ≤ n) →
                    QCnt.cliffords (Msl.Maslovₙ n p) + 2 * Msl.parity n ≡
                    10 * (n ∸ 2) + 1
Maslovₙ-cliffords = Msl.Maslovₙ-cliffords-closed

table-2-Maslov50 : (p : 3 ≤ 50) →
                   (Qb.qubits (Msl.Maslovₙ 50 p) ≡ 74) ×
                   (KP.paths (Msl.Maslovₙ 50 p) ≡ 192) ×
                   (QCnt.cliffords (Msl.Maslovₙ 50 p) ≡ 481) ×
                   (TNet.tcount (Msl.Maslovₙ 50 p) ≡ 384)
table-2-Maslov50 = Msl.table-2-Maslov50

table-2-Maslov100 : (p : 3 ≤ 100) →
                    (Qb.qubits (Msl.Maslovₙ 100 p) ≡ 149) ×
                    (KP.paths (Msl.Maslovₙ 100 p) ≡ 392) ×
                    (QCnt.cliffords (Msl.Maslovₙ 100 p) ≡ 981) ×
                    (TNet.tcount (Msl.Maslovₙ 100 p) ≡ 784)
table-2-Maslov100 = Msl.table-2-Maslov100


------------------------------------------------------------------------
-- Section 5.2: the out-of-place adder, for every n (PathSum.Adder,
-- PathSum.Adder.*, PathSum.Reversible, PathSum.Toffoli.Depth3)

-- "Adder_n : |x⟩|y⟩|0⟩ ↦ |x⟩|y⟩|x + y⟩" by "a standard out-of-place
-- ripple-carry adder": the carries into n − 1 ancillas and the sum
-- bits into an n-bit temporary register, copied out, then uncomputed,
-- on 5n wires (n = m + 1), each Toffoli gate expanded into the seven-T
-- circuit.  The specification is "generated by implementing binary
-- addition on symbolic vectors": the classical path-sum whose output
-- register gets the lifts of the ripple-carry sum bits.  On the inputs
-- whose carries and temporary register are |0⟩ the circuit is the
-- specification, it leaves them clean, and with them read as the
-- constant 0 the two are ≋.  (The output register gains x + y by xor,
-- as in the tool's specification; Adder-spec₀ is the paper's form.)
-- The proofs compose classical path-sums (proposition 2.7), so they
-- cost the same for every n.

Adder-spec : (m : ℕ) →
             KP.⟦ ACi.Adderᶜ m ⟧ ≋[ ACi.scratch (AL.standard m) ]₀*
               ASp.adderˢ (AL.standard m)
Adder-spec = Add.Adder-spec

Adder-clean : (m : ℕ) → ∀ x z → Clean (ACi.scratch (AL.standard m)) x →
              (i : Fin (m + suc m)) →
              z (ACi.scratch (AL.standard m) i) ≡ true →
              amp KP.⟦ ACi.Adderᶜ m ⟧ x z ≐ 0ᴬ
Adder-clean = Add.Adder-clean

Adder-set0 : (m : ℕ) →
             set0ˢ (ACi.scratch (AL.standard m)) KP.⟦ ACi.Adderᶜ m ⟧ ≋
             set0ˢ (ACi.scratch (AL.standard m)) (ASp.adderˢ (AL.standard m))
Adder-set0 = Add.Adder-set0

-- The paper's form: with the output register |0⟩ as well, the circuit
-- is the specification that writes x + y there -- whose output
-- register holds x + y as a number.

Adder-spec₀ : (m : ℕ) →
              KP.⟦ ACi.Adderᶜ m ⟧ ≋[ Add.blank₀ (AL.standard m) ]₀*
                ASp.adder₀ˢ (AL.standard m)
Adder-spec₀ = Add.Adder-spec₀

adder₀ˢ-value : (m : ℕ) (x : Assign (AL.width m)) →
                ABin.val (λ k → Cl.fun (ASp.adder₀ᵒ (AL.standard m)) x
                                  (AL.wire (AL.standard m) (AL.zw k))) ≡
                ABin.val (ARip.xbits (AL.standard m) x) +
                ABin.val (ARip.ybits (AL.standard m) x)
adder₀ˢ-value m = ASp.adder₀ˢ-value (AL.standard m)

-- The paper's circuit is the one its tool generates: Feynman
-- (github.com/meamy/feynman), whose src/Feynman/Verification/SOP.hs
-- builds the netlist carryRipple, expands each Toffoli gate by its
-- sixteen-gate, T-depth-3 toffoli, uncomputes by the adjoint of the
-- expanded compute, and checks the result against adderOOPSpec.  The
-- tool's Toffoli circuit is the Toffoli gate ...

tof₃-spec : (c₁ c₂ t : Fin n) (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
            (c₂≢t : c₂ ≢ t) →
            KP.⟦ Tof3.tof₃ c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t ⟧ ≋ Tof.toffoliˢ c₁ c₂ t
tof₃-spec = Tof3.tof₃-spec

-- ... so the netlist expanded by it throughout, uncomputation included
-- (a Toffoli gate is its own inverse), is on the inputs whose ancillas
-- are |0⟩ the tool's specification, which adds modulo 2^n (the output
-- register has n bits); it leaves the ancillas clean; and with them
-- read as the constant 0 the two are ≋ -- the check the tool ran at
-- n = 8 and n = 16, here for every n.

Tool-spec : (m : ℕ) →
            KP.⟦ AT.CarryRippleᶜ m ⟧ ≋[ AT.ancᶠ (ACR.standardᶠ m) ]₀*
              AT.toolˢ (ACR.standardᶠ m)
Tool-spec = AT.Tool-spec

Tool-clean : (m : ℕ) → ∀ x z → Clean (AT.ancᶠ (ACR.standardᶠ m)) x →
             (j : Fin (suc m + suc m)) →
             z (AT.ancᶠ (ACR.standardᶠ m) j) ≡ true →
             amp KP.⟦ AT.CarryRippleᶜ m ⟧ x z ≐ 0ᴬ
Tool-clean = AT.Tool-clean

Tool-set0 : (m : ℕ) →
            set0ˢ (AT.ancᶠ (ACR.standardᶠ m)) KP.⟦ AT.CarryRippleᶜ m ⟧ ≋
            set0ˢ (AT.ancᶠ (ACR.standardᶠ m)) (AT.toolˢ (ACR.standardᶠ m))
Tool-set0 = AT.Tool-set0

-- The tool's circuit literally -- its uncomputation the adjoint of the
-- expanded compute, T and T† exchanged; the same gate list as the
-- tool's own output at n = 2 and 3 -- is ≋ that circuit, and so the
-- same holds of it.

Feynman-≋ : (m : ℕ) → KP.⟦ AF.Feynmanᶜ m ⟧ ≋ KP.⟦ AT.CarryRippleᶜ m ⟧
Feynman-≋ = AF.Feynman-≋

Feynman-spec : (m : ℕ) →
               KP.⟦ AF.Feynmanᶜ m ⟧ ≋[ AT.ancᶠ (ACR.standardᶠ m) ]₀*
                 AT.toolˢ (ACR.standardᶠ m)
Feynman-spec = AF.Feynman-spec

Feynman-clean : (m : ℕ) → ∀ x z → Clean (AT.ancᶠ (ACR.standardᶠ m)) x →
                (j : Fin (suc m + suc m)) →
                z (AT.ancᶠ (ACR.standardᶠ m) j) ≡ true →
                amp KP.⟦ AF.Feynmanᶜ m ⟧ x z ≐ 0ᴬ
Feynman-clean = AF.Feynman-clean

Feynman-set0 : (m : ℕ) →
               set0ˢ (AT.ancᶠ (ACR.standardᶠ m)) KP.⟦ AF.Feynmanᶜ m ⟧ ≋
               set0ˢ (AT.ancᶠ (ACR.standardᶠ m)) (AT.toolˢ (ACR.standardᶠ m))
Feynman-set0 = AF.Feynman-set0

-- Table 2's rows Adder8 and Adder16, counted from the circuit in both
-- forms: 40 and 80 qubits -- the wires its gates touch, as the tool
-- counts them -- 56 and 120 path variables, 334 and 710 Clifford
-- gates, 196 and 420 T gates, all as printed.  Its gates touch all 5n
-- wires once n ≥ 2; at n = 1 the carry-in wire is idle and the count
-- is 4, the text's "5n − 1 bits", which for n ≥ 2 leaves that wire out.
-- (The adder above, which keeps the carry out, touches all its 5n
-- wires for every n and has the same path variables and T gates, and
-- 304 and 648 Clifford gates.)

Tool-qubits : (m : ℕ) → m ≢ 0 → Qb.qubits (AT.CarryRippleᶜ m) ≡ 5 * suc m
Tool-qubits = AT.Tool-qubits

Tool-qubits-1 : Qb.qubits (AT.CarryRippleᶜ 0) ≡ 4
Tool-qubits-1 = AT.Tool-qubits-1

Adder-qubits : (m : ℕ) → Qb.qubits (ACi.Adderᶜ m) ≡ AL.width m
Adder-qubits = Add.Adder-qubits

table-2-Adder8 : (Qb.qubits (AT.CarryRippleᶜ 7) ≡ 40) ×
                 (KP.paths (AT.CarryRippleᶜ 7) ≡ 56) ×
                 (QCnt.cliffords (AT.CarryRippleᶜ 7) ≡ 334) ×
                 (TNet.tcount (AT.CarryRippleᶜ 7) ≡ 196)
table-2-Adder8 = AT.Adder8ᵀ

table-2-Adder16 : (Qb.qubits (AT.CarryRippleᶜ 15) ≡ 80) ×
                  (KP.paths (AT.CarryRippleᶜ 15) ≡ 120) ×
                  (QCnt.cliffords (AT.CarryRippleᶜ 15) ≡ 710) ×
                  (TNet.tcount (AT.CarryRippleᶜ 15) ≡ 420)
table-2-Adder16 = AT.Adder16ᵀ

table-2-Adder8-Feynman :
  (Qb.qubits (AF.Feynmanᶜ 7) ≡ 40) × (KP.paths (AF.Feynmanᶜ 7) ≡ 56) ×
  (QCnt.cliffords (AF.Feynmanᶜ 7) ≡ 334) × (TNet.tcount (AF.Feynmanᶜ 7) ≡ 196)
table-2-Adder8-Feynman = AF.Adder8-Feynman

table-2-Adder16-Feynman :
  (Qb.qubits (AF.Feynmanᶜ 15) ≡ 80) × (KP.paths (AF.Feynmanᶜ 15) ≡ 120) ×
  (QCnt.cliffords (AF.Feynmanᶜ 15) ≡ 710) ×
  (TNet.tcount (AF.Feynmanᶜ 15) ≡ 420)
table-2-Adder16-Feynman = AF.Adder16-Feynman


------------------------------------------------------------------------
-- Section 5.2: the quantum hidden shift algorithm, for every size
-- (PathSum.HiddenShift, PathSum.HiddenShift.*)

-- For the Maiorana–McFarland bent function f(x, y) = g(x) + x·y on
-- 2m bits the dual is f̃(x, y) = g(y) + x·y: the Walsh transform of f
-- is 2^m times f̃.

walsh-mm : ∀ {m} (g : (Fin m → Bool) → Bool) → RespectsB g →
           (c : Fin (m + m) → Bool) →
           Σᶻ (λ u → sgn (mm g u xor dot u c)) ≡
           + (2 ^ m) *ℤ sgn (dual g c)
walsh-mm = HW.walsh-mm

-- "The circuit H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n} is known to implement
-- the mapping |0⟩ ↦ |s⟩": for every m, every g and every shift s, as a
-- composite of path-sums (definition 2.6) ...

hidden-shift : (g : Poly m 0) (s z : Assign (m + m)) →
               amp (HSh.HS g s) 0ᵃ z ≐
               (if same s z then scale (HSh.hs-norm (m + m)) (zpow 0ℤ)
                else 0ᴬ)
hidden-shift g s = HSh.hidden-shift g s

-- ... and as figure 3(a)'s circuit over {H, CNOT, R_k}, the oracles
-- built from Z, CZ and CCZ gates for g any list of such monomials (X
-- is H R₁ H, which adds path variables but not amplitude).

hidden-shift-circuit : (gs : List (HGa.Term m)) (s z : Assign (m + m)) →
                       amp K.⟦ HCi.HSᶜ gs s ⟧ 0ᵃ z ≐
                       (if same s z
                        then scale (K.norm (HCi.HSᶜ gs s)) (zpow 0ℤ)
                        else 0ᴬ)
hidden-shift-circuit = HCi.hidden-shift-circuit

-- Figure 3(b), the shift given symbolically in a second register:
-- |0⟩|s⟩ ↦ |s⟩|s⟩.

symbolic-shift-0 : (gs : List (HGa.Term m)) (s : Assign (m + m))
                   (z : Assign ((m + m) + (m + m))) →
                   amp K.⟦ HSy.SSᶜ gs ⟧ (0ᵃ {m + m} ⧺ s) z ≐
                   (if same (s ⧺ s) z
                    then scale (K.norm (HSy.SSᶜ gs)) (zpow 0ℤ) else 0ᴬ)
symbolic-shift-0 = HSy.symbolic-shift-0

-- "Our calculus further finds the correct output |s⟩ or |s⟩|s⟩ even
-- without providing the specification": every reduction by figure 2's
-- rules, at any variables, that eliminates all path variables ends at
-- |x⟩ ↦ |s⟩ syntactically ...

hidden-shift-reduces : (g : Poly m 0) (s : Assign (m + m)) {k′ : ℕ}
                       {ζ : PathSum (m + m) k′ 0} →
                       HSim.at0 (HSh.HS g s) ⟶ᶠ* ζ →
                       (k′ ≡ 0) × (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                       (phase ζ ≈[ pow M ] 0ᴾ)
hidden-shift-reduces = HSim.hidden-shift-reduces

-- ... and such a reduction exists, for every m, g and s -- three passes
-- of [HH] and [Elim] over the coordinates -- so the calculus does find
-- |s⟩.  (The chain is constructed; that the search normal-formᶠ finds
-- one is not shown.)

hidden-shift-finds : (g : Poly m 0) (s : Assign (m + m)) →
                     Σ (PathSum (m + m) 0 0) (λ ζ →
                       (HSim.at0 (HSh.HS g s) ⟶ᶠ* ζ) ×
                       (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                       (phase ζ ≈[ pow M ] 0ᴾ))
hidden-shift-finds = HEx.hidden-shift-finds

-- The same on figure 3's circuits, their own path-sums (definition
-- 2.9): from |0⟩, figure 3(a) -- whose X gates, H R₁ H here, add path
-- variables the chain removes first -- every complete reduction ends at
-- |s⟩, and one exists ...

circuit-reduces : (gs : List (HGa.Term m)) (s : Assign (m + m)) {k′ : ℕ}
                  {ζ : PathSum (m + m) k′ 0} →
                  HSim.at0 K.⟦ HCi.HSᶜ gs s ⟧ ⟶ᶠ* ζ →
                  (k′ ≡ 0) × (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                  (phase ζ ≈[ pow M ] 0ᴾ)
circuit-reduces = HCi.circuit-reduces

circuit-finds : (gs : List (HGa.Term m)) (s : Assign (m + m)) →
                Σ (PathSum (m + m) 0 0) (λ ζ →
                  (HSim.at0 K.⟦ HCi.HSᶜ gs s ⟧ ⟶ᶠ* ζ) ×
                  (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                  (phase ζ ≈[ pow M ] 0ᴾ))
circuit-finds = HEC.circuit-finds

-- ... and figure 3(b), with its data register |0⟩ and the shift
-- symbolic, at |x_d, x_s⟩ ↦ |x_s, x_s⟩: the calculus finds |s⟩|s⟩.

symbolic-reduces : (gs : List (HGa.Term m)) {k′ : ℕ}
                   {ζ : PathSum ((m + m) + (m + m)) k′ 0} →
                   AReg.set0ᶜ (HSy.dataMask (m + m)) K.⟦ HSy.SSᶜ gs ⟧ ⟶ᶠ* ζ →
                   (k′ ≡ 0) ×
                   (∀ w → out ζ w ≈[ + 2 ] μ x[ HSy.copy (m + m) w ]) ×
                   (phase ζ ≈[ pow M ] 0ᴾ)
symbolic-reduces = HRe.symbolic-reduces

symbolic-finds : (gs : List (HGa.Term m)) →
                 Σ (PathSum ((m + m) + (m + m)) 0 0) (λ ζ →
                   (AReg.set0ᶜ (HSy.dataMask (m + m)) K.⟦ HSy.SSᶜ gs ⟧
                      ⟶ᶠ* ζ) ×
                   (∀ w → out ζ w ≈[ + 2 ] μ x[ HSy.copy (m + m) w ]) ×
                   (phase ζ ≈[ pow M ] 0ᴾ))
symbolic-finds = HES.symbolic-finds


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
-- input, so nothing here is polynomial-time; the polynomial-time
-- procedure, on sparse path-sums in a cost model, is the last
-- section's.)

circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidable = Cor.circuit-decidable

matrix-decidable : (C : Circuit n) →
  Dec (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z))
matrix-decidable = Cor.matrix-decidable


------------------------------------------------------------------------
-- The paper's polynomial-time claims, in a cost model (PathSum.Cost,
-- PathSum.Cost.*)

-- A cost model, not a machine model: every algorithm below is written
-- once, as a program in PathSum.Cost's monad that computes a value and
-- a count of unit steps together (an operation on numbers below 2^M,
-- on Booleans or Fin indices, a list or vector cell visited, and the
-- few conventions PathSum.Cost's header lists), on sparse path-sums
-- rather than the dense ones above.  Nothing is claimed about Turing
-- machines or complexity classes.

-- Proposition 3.2, as far as it holds: for a fixed order bound d ≥ 2,
-- normalising a sparse path-sum with [Elim], [ω] and [HH] with linear
-- quotients, at any variables, terminates after at most m rounds with
-- a chain to an irreducible path-sum, at a cost polynomial in n + m
-- (the Proposition-3-2 record: terminates, linear, normalises,
-- polynomial, every).  [Case] and non-linear quotients are left out:
-- one such step can raise the order the bounds rest on
-- (PathSum.Cost.Excluded.order-rises) -- and "matching is polynomial,
-- hence normalising is" needs the path-sum to stay small, which lemma
-- 2.13 gives only for linear quotients.

proposition-3-2 : (d : ℕ) → 2 ≤ d → (ξ : PathSum n k m) (R : Sp.Rep n m) →
                  Represents ξ R → Ord≤ d (phase ξ) →
                  CN.Proposition-3-2 d ξ R
proposition-3-2 = CN.proposition-3-2

-- Corollary 4.4 in polynomial time, for circuits over {H, S, CZ}:
-- interpret the circuit into its isometry restriction, normalise at
-- order 2, and read the verdict.  The value is true exactly when the
-- circuit is the identity, at a cost at most 313 (n + |C| + 3)^12 and
-- at most 313 (2 n |C| + 3)^12 in the volume (the Corollary-4-4
-- record's decides, polynomial, volume).  (The paper's gate set
-- {H, CNOT, R_k} at level ≤ 2 would need a cost-annotated Gaussian
-- elimination, which is not written.)

corollary-4-4-polytime : (C : Circuit n) → CCor.Corollary-4-4 C
corollary-4-4-polytime = CCor.corollary-4-4-polytime

decide-correct : (C : Circuit n) →
                 (PC.value (CCor.decideᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
decide-correct = CCor.decide-correct

decideBound-def : ∀ n ℓ → CCor.decideBound n ℓ ≡ 313 * (3 + (n + ℓ)) ^ 12
decideBound-def = CCor.decideBound-def

-- "A polynomial-time decision procedure for checking the equivalence
-- of Clifford group circuits" (the abstract): the miter, built in the
-- monad and decided, at a cost at most
-- 315 (n + 3 (|C₁| + |C₂|) + 3)^12.

equivalence-polytime : (C₁ C₂ : Circuit n) → CCor.PolyEquivalence C₁ C₂
equivalence-polytime = CCor.equivalence-polytime

equiv-correct : (C₁ C₂ : Circuit n) →
                (PC.value (CCor.equivᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equiv-correct = CCor.equiv-correct

-- Corollary 2.15's time half: the path-sum of a circuit over
-- {H, CNOT, R_k, R_k†} is computed gate by gate at a cost polynomial
-- in n + |C| for each fixed level k (the Corollary-2-15-time record:
-- computes, few-terms, polynomial, volume).

corollary-2-15-time : (C : K.Circuit n) → CInt.Corollary-2-15-time C
corollary-2-15-time = CInt.corollary-2-15-time

-- At order 2 -- every Clifford circuit's restriction -- the linear
-- normaliser's outputs are normal forms of all of figure 2
-- (PathSum.Full.Order2), so proposition 3.2 holds for the whole
-- calculus there, at the linear normaliser's polynomial cost (the
-- Proposition-3-2ᶠ record: linear, terminatesᶠ, lengthᶠ, reachesᶠ,
-- normalᶠ), and the normal form corollary-4-4-polytime computes is one
-- of figure 2, read by corollary-4-4-normalᶠ.

proposition-3-2ᶠ : (ξ : PathSum n k m) (R : Sp.Rep n m) → Represents ξ R →
                   Ord≤ 2 (phase ξ) → CIrr.Proposition-3-2ᶠ ξ R
proposition-3-2ᶠ = CIrr.proposition-3-2ᶠ

corollary-4-4-polytimeᶠ : (C : Circuit n) →
                          CCor.Corollary-4-4 C × CIrr.PipelineNormalForm C
corollary-4-4-polytimeᶠ = CIrr.corollary-4-4-polytimeᶠ
