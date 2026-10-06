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
-- (PathSum.Cost.Corollary) and, by the paper's own route of Gaussian
-- elimination, over its gate set {H, CNOT, R_k} at level ≤ 2
-- (PathSum.Cost.Gauss.Corollary): the last two sections below.
--
-- Around that core: lemma 2.5 for every Boolean polynomial; composition
-- of path-sums (definition 2.6), proposition 2.7's operator equation,
-- and remark 2.8 up to renaming path variables, every symmetric
-- monoidal law and for circuits (PathSum.Compose, PathSum.Compose.
-- Monoidal, PathSum.CRK.Structural); definition 2.1's constant inputs
-- and section 2.1's compatibility condition, with proposition 2.7
-- under exactly the compatibility it needs and footnote 1's reduction
-- (PathSum.Signature); definition 2.9 over the
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
-- them, and as its tool generated them for every random draw, with
-- table 2's rows (PathSum.HiddenShift); Z[ζ] as a commutative ring,
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
-- linear rules, and corollary 4.4's for circuits over {H, S, CZ} and,
-- by Gaussian elimination, over {H, CNOT, R_k} at level ≤ 2.
--
-- The precision is fixed, as in the paper's tool: phases are integer
-- numerators over 2^M, with M = M₀ + 3 for every M₀, and R_k for
-- k > M is read as R_M (PathSum.CRK.Circuit), so a theorem about a
-- circuit with such gates is about their R_M reading; the families of
-- section 5.2 state the precision they need (the QFT n + 1 ≤ M).
--
-- Not formalised: running times on a machine and complexity classes
-- (footnote 2's P = co-NP among them, and footnote 1's hardness of
-- compatibility as a complexity statement); the time bounds for [Case]
-- and non-linear quotients beyond order 2; and section 5's benchmarks
-- as runs of the tool.
--
-- Each section's banner names the modules its results come from;
-- results proved here from them are stated with their proofs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _<_)

module PathSum.Theorems (M₀ : ℕ) where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using
  (Bool; true; false; not; _xor_; if_then_else_)
open import Data.Nat.Base using
  (_+_; _*_; _∸_; _^_; _≤_; _⊔_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Subset using (Subset; ⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _-_)
  renaming (_*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.List.Base using (List; []; _∷_; _++_; length; map; upTo)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (Σ; _×_; _,_; ∃; proj₁; proj₂)
open import Level using (0ℓ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; no; map′; True)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Assign using (same; [_]ᶻ)
open import PathSum.AssignSum using (Σᶻ; RespectsZ)
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

import Data.Fin.Permutation as Perm

import PathSum.Permute as Pm
open Pm using (_≡ᴿ⟨_⟩_; relabel)

import PathSum.Permute.Sound
module PmS = PathSum.Permute.Sound M₀
open PmS using (_≈ᴿ⟨_⟩_)

import PathSum.Permute.Blocks as Blk
open Blk using (_⊕ᵖ_)

import PathSum.Compose.Monoidal
module Mon = PathSum.Compose.Monoidal M₀
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

import PathSum.Cost.Gauss
module CGs = PathSum.Cost.Gauss M

import PathSum.Cost.Gauss.Correct
module CGC = PathSum.Cost.Gauss.Correct M₀

import PathSum.Cost.Gauss.Corollary
module CG = PathSum.Cost.Gauss.Corollary M₀

-- Closed runs of the decision at precision M = 3, imported so that
-- this root checks them.

import PathSum.Cost.Gauss.Example

import PathSum.Permute.Congruence
module PmC = PathSum.Permute.Congruence M₀

import PathSum.Permute.Hexagon as Hex

import PathSum.Compose.Relabel
module Rel = PathSum.Compose.Relabel M₀

import PathSum.Compose.Relabel.Sharp
module RelS = PathSum.Compose.Relabel.Sharp M₀

import PathSum.CRK.RenamingNeeded
module KRN = PathSum.CRK.RenamingNeeded M₀

import PathSum.Circuit.Trace
import PathSum.Circuit.Structural
module CStr = PathSum.Circuit.Structural M₀

import PathSum.Cost.Gauss.Total
module CGT = PathSum.Cost.Gauss.Total M₀

import PathSum.Cost.Corollary.Volume
module CCorV = PathSum.Cost.Corollary.Volume M₀

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

import PathSum.CRK.Structural
module Str = PathSum.CRK.Structural M₀
open Str using (_∼_; _≃⟨_⟩_)

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

import PathSum.Ancilla
module Ancl = PathSum.Ancilla M₀

module KX = PathSum.CRK.WithX M₀

import PathSum.Signature
module Sig = PathSum.Signature M₀
open Sig using (Signature; Signed; _⊢_; sig; ps; ⌜_⌝; ampˢ; _≋ˢ_; inline)

import PathSum.Signature.Compose
module SigC = PathSum.Signature.Compose M₀
open SigC using
  (SynCompatible; PathCompatible; Compatible; _∘ˢ_; Prop-2-7)

import PathSum.Signature.Clean
module SigCl = PathSum.Signature.Clean M₀
open SigCl using (LeavesClean; LeavesClean₁; prepare; watched)

import PathSum.Signature.WithX
module SigX = PathSum.Signature.WithX M₀

-- Section 5.2's hidden shift benchmarks as the paper's tool generates
-- them.  The modules export generic names (prim, Prim, Block, Draw,
-- firsts, countᵀ, …; prim and Prim clash with PathSum.Adder.Feynman's),
-- so they are imported qualified.

import PathSum.HiddenShift.Tool
module HTo = PathSum.HiddenShift.Tool M₀

import PathSum.HiddenShift.ToolSymbolic
module HTSy = PathSum.HiddenShift.ToolSymbolic M₀

import PathSum.HiddenShift.Feynman
module HFy = PathSum.HiddenShift.Feynman M₀

import PathSum.HiddenShift.Table
module HTb = PathSum.HiddenShift.Table M₀

import PathSum.HiddenShift.ToolExists
module HTE = PathSum.HiddenShift.ToolExists M₀

-- Multilinear forms, the size of addition's expansion, and the hidden
-- shift for every bent function (generic names: imported qualified;
-- PCnt.count would clash with PathSum.Reversible's count).

import PathSum.Polynomial.Count as PCnt
import PathSum.Polynomial.Interpolate as PInt
import PathSum.Adder.Expansion as AExp
import PathSum.Adder.Expansion.Lift as ALift
import PathSum.Adder.Expansion.PathSums
module APS = PathSum.Adder.Expansion.PathSums M₀
import PathSum.HiddenShift.Bent as HBent
open HBent using (Bent; walsh)
import PathSum.HiddenShift.AnyBent
module HAB = PathSum.HiddenShift.AnyBent M₀
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Mobius using (evalˢ)

-- Section 4.1's restriction for any outputs.

import PathSum.Restrict
module Rs = PathSum.Restrict M₀
open Rs using (Restricts; Solved; _↝*_; _⇝*_)

import PathSum.Restrict.Pivot
module RPv = PathSum.Restrict.Pivot M₀
open RPv using (Pivot; restrictᴾ)

import PathSum.Restrict.Spec
module RSp = PathSum.Restrict.Spec M₀

import PathSum.Restrict.Linear
module RLn = PathSum.Restrict.Linear M₀

import PathSum.Restrict.Removes
module RRm = PathSum.Restrict.Removes M₀

import PathSum.CRK.WithX.WellFormed
module KXW = PathSum.CRK.WithX.WellFormed M₀

import PathSum.Gauss
module Gau = PathSum.Gauss M₀
import PathSum.Gauss.Forms as GF
import PathSum.CRK.Amp
module KAmp = PathSum.CRK.Amp M₀

-- Counterexamples tied to definition 2.1's normalisation, and lemma 4.1
-- with constant inputs.

import PathSum.Tied
module Td = PathSum.Tied M₀
import PathSum.Compose.Counterexample.Tied
module CEt = PathSum.Compose.Counterexample.Tied M₀
import PathSum.PartialIsometry.Strict.Tied
module Strt = PathSum.PartialIsometry.Strict.Tied M₀
import PathSum.Isometry.Counterexample
module IsoC = PathSum.Isometry.Counterexample M₀
import PathSum.Signature.Isometry
module SigI = PathSum.Signature.Isometry M₀
import PathSum.Polynomial.Substitution as PSub

-- Closed restrictions at M₀ = 0, imported so that this root checks
-- them.

import PathSum.Examples.Restrict
import PathSum.Examples.Restrict.NonLinear

-- Section 4's incompleteness witnesses, closed at M₀ = 0; stated below
-- through their own names only.

import PathSum.Examples.Incomplete
module ExInc = PathSum.Examples.Incomplete

import PathSum.Examples.ValidationIncomplete
module ExVInc = PathSum.Examples.ValidationIncomplete

-- Section 3.2's identity behind [Case], closed at M₀ = 0; stated below
-- through its own names and instances only (ExCase.D, ExCase.CX).  It
-- is imported with "as", not applied as a module: a module application
-- copies every definition, and a closed statement made with the copies
-- is matched against the originals by unfolding ≋ into amplitudes.

import PathSum.Examples.CaseIdentity as ExCase
import PathSum.Examples.Base as ExB

-- Circuits with X gates: lemma 4.1 and the reified restriction; and
-- figure 2 without [Case], generically and at the examples' precision.

import PathSum.CRK.WithX.Columns
module KXC = PathSum.CRK.WithX.Columns M₀

import PathSum.Full.WithoutCase
module FWC  = PathSum.Full.WithoutCase M
module FWC₀ = PathSum.Full.WithoutCase 3
module Fl₀  = PathSum.Full 3

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
-- definition 2.4.  For definition 2.4 the witnesses must be path-sums
-- in definition 2.1's sense, the normalisation 1/√2^m tied to the m
-- path variables: |0⟩⟨0| then |+⟩⟨+|, whose composite is
-- (1/√2)|+⟩⟨0|, both written with three path variables
-- (PathSum.Compose.Counterexample.Tied).  The untied pair CE.P₀, CE.P₊
-- (normalisation ½, one path variable) is kept as the operator-level
-- statement it is.  It holds when the path-sum applied second is an
-- isometry -- the paper's footnote: in practice only unitaries are
-- composed.

WellFormed-∘-fails :
  WellFormed CE.plus × WellFormed CE.erase × ¬ WellFormed (CE.erase ∘ᴾ CE.plus)
WellFormed-∘-fails = CE.WellFormed-∘-fails

PartialIsometric-∘-fails-tied :
  ∃ λ m → ∃ λ (ξ : PathSum 1 m m) → ∃ λ (ζ : PathSum 1 m m) →
    PartialIsometric ξ × PartialIsometric ζ × ¬ PartialIsometric (ζ ∘ᴾ ξ)
PartialIsometric-∘-fails-tied = CEt.PartialIsometric-∘-fails-tied

PartialIsometric-∘-fails :
  PartialIsometric CE.P₀ × PartialIsometric CE.P₊ ×
  ¬ PartialIsometric (CE.P₊ ∘ᴾ CE.P₀)
PartialIsometric-∘-fails = CE.PartialIsometric-∘-fails

-- Every path-sum is equivalent to one with its normalisation tied to
-- its path variables (pad and gadget), so keeping the two apart costs
-- nothing in what operators are expressible.

tie : (ξ : PathSum n k m) → ∃ λ j → ∃ λ (ξ′ : PathSum n j j) → ξ′ ≋ ξ
tie = Td.tie

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
-- tensor interchange, and SWAP is natural, up to ≋.  The next section
-- has these and the other laws as equalities up to renaming.

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
-- Remark 2.8: the symmetric monoidal laws up to renaming
-- (PathSum.Permute, PathSum.Permute.Sound, PathSum.Permute.Blocks,
-- PathSum.Compose.Monoidal)

-- "Strictly equal in the path-sum picture", as far as path-sums name
-- their variables: ξ ≡ᴿ⟨ π ⟩ ζ says the normalisations are equal and
-- every phase and output coefficient is equal as an integer once the
-- path variables are renamed along the bijection π; ξ ≈ᴿ⟨ π ⟩ ζ asks
-- only for outputs modulo 2 (where definition 2.6's lifted outputs
-- enter).  Either gives ≋.  The structure maps act on the wires by
-- relabelling (the casts along +-assoc and +-identityʳ, the block
-- exchange), since ≋ only relates path-sums on the same wires.

renumber-≋ : (π : Perm.Permutation m m′) (ξ : PathSum n k m) →
             Pm.renumber π ξ ≋ ξ
renumber-≋ = PmS.renumber-≋

≡ᴿ⇒≋ : {ξ : PathSum n k m} {π : Perm.Permutation m m′}
       {ζ : PathSum n k′ m′} → ξ ≡ᴿ⟨ π ⟩ ζ → ξ ≋ ζ
≡ᴿ⇒≋ = PmS.≡ᴿ⇒≋

≈ᴿ⇒≋ : {ξ : PathSum n k m} {π : Perm.Permutation m m′}
       {ζ : PathSum n k′ m′} → ξ ≈ᴿ⟨ π ⟩ ζ → ξ ≋ ζ
≈ᴿ⇒≋ = PmS.≈ᴿ⇒≋

⊗-assocᴿ : ∀ {n₃ k₃ m₃}
           (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
           (ξ₃ : PathSum n₃ k₃ m₃) →
           relabel (Blk.assocᵖ n₁ n₂ n₃) ((ξ₁ ⊗ᴾ ξ₂) ⊗ᴾ ξ₃)
           ≡ᴿ⟨ Blk.assocᵖ m₁ m₂ m₃ ⟩ (ξ₁ ⊗ᴾ (ξ₂ ⊗ᴾ ξ₃))
⊗-assocᴿ = Mon.⊗-assocᴿ

⊗-unitˡᴿ : (ξ : PathSum n k m) → (idPS {0} ⊗ᴾ ξ) ≡ᴿ⟨ Perm.id ⟩ ξ
⊗-unitˡᴿ = Mon.⊗-unitˡᴿ

⊗-unitʳᴿ : (ξ : PathSum n k m) →
           relabel (Blk.unitʳᵖ n) (ξ ⊗ᴾ idPS {0}) ≡ᴿ⟨ Blk.unitʳᵖ m ⟩ ξ
⊗-unitʳᴿ = Mon.⊗-unitʳᴿ

⊗-braidᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
           relabel (Blk.braidᵖ n₁ n₂) (ξ₁ ⊗ᴾ ξ₂)
           ≡ᴿ⟨ Blk.braidᵖ m₁ m₂ ⟩ (ξ₂ ⊗ᴾ ξ₁)
⊗-braidᴿ = Mon.⊗-braidᴿ

braid-braidᴿ : ∀ a b (ξ : PathSum (a + b) k m) →
               relabel (Blk.braidᵖ b a) (relabel (Blk.braidᵖ a b) ξ)
               ≡ᴿ⟨ Perm.id ⟩ ξ
braid-braidᴿ = Mon.braid-braidᴿ

hexagonᴿ : ∀ a b c (ξ : PathSum ((a + b) + c) k m) →
           relabel (Blk.assocᵖ b c a)
             (relabel (Blk.braidᵖ a (b + c)) (relabel (Blk.assocᵖ a b c) ξ))
           ≡ᴿ⟨ Perm.id ⟩
           relabel (Perm.id {b} ⊕ᵖ Blk.braidᵖ a c)
             (relabel (Blk.assocᵖ b a c)
               (relabel (Blk.braidᵖ a b ⊕ᵖ Perm.id {c}) ξ))
hexagonᴿ = Mon.hexagonᴿ

pentagonᴿ : ∀ a b c d (ξ : PathSum (((a + b) + c) + d) k m) →
            relabel (Blk.assocᵖ a b (c + d))
              (relabel (Blk.assocᵖ (a + b) c d) ξ)
            ≡ᴿ⟨ Perm.id ⟩
            relabel (Perm.id {a} ⊕ᵖ Blk.assocᵖ b c d)
              (relabel (Blk.assocᵖ a (b + c) d)
                (relabel (Blk.assocᵖ a b c ⊕ᵖ Perm.id {d}) ξ))
pentagonᴿ = Mon.pentagonᴿ

triangleᴿ : ∀ a b (ξ : PathSum ((a + 0) + b) k m) →
            relabel (Perm.id {a} ⊕ᵖ Perm.id {b})
              (relabel (Blk.assocᵖ a 0 b) ξ)
            ≡ᴿ⟨ Perm.id ⟩ relabel (Blk.unitʳᵖ a ⊕ᵖ Perm.id {b}) ξ
triangleᴿ = Mon.triangleᴿ

-- Bifunctoriality and the naturality of SWAP -- the remark's two
-- examples -- and the category laws of ∘ᴾ.

⊗-interchangeᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                 (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂) →
                 ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂))
                 ≡ᴿ⟨ Blk.shuffleᵖ l₁ l₂ m₁ m₂ ⟩
                 ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂))
⊗-interchangeᴿ = Mon.⊗-interchangeᴿ

swap-naturalᴿ : (ξ₁ : PathSum n k₁ m₁) (ξ₂ : PathSum n k₂ m₂) →
                (swapᴾ n ∘ᴾ (ξ₁ ⊗ᴾ ξ₂))
                ≈ᴿ⟨ Blk.unitʳᵖ (m₁ + m₂) Perm.∘ₚ Blk.braidᵖ m₁ m₂ ⟩
                ((ξ₂ ⊗ᴾ ξ₁) ∘ᴾ swapᴾ n)
swap-naturalᴿ = Mon.swap-naturalᴿ

∘ᴾ-identityʳᴿ : (ξ : PathSum n k m) → (ξ ∘ᴾ idPS) ≡ᴿ⟨ Perm.id ⟩ ξ
∘ᴾ-identityʳᴿ = Mon.∘ᴾ-identityʳᴿ

∘ᴾ-identityˡᴿ : (ξ : PathSum n k m) → (idPS ∘ᴾ ξ) ≈ᴿ⟨ Blk.unitʳᵖ m ⟩ ξ
∘ᴾ-identityˡᴿ = Mon.∘ᴾ-identityˡᴿ

∘ᴾ-assocᴿ : (ξ″ : PathSum n k″ m″) (ξ′ : PathSum n k′ m′)
            (ξ : PathSum n k m) →
            ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) ≡ᴿ⟨ Perm.flip (Blk.assocᵖ m m′ m″) ⟩
            (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ))
∘ᴾ-assocᴿ = Mon.∘ᴾ-assocᴿ


------------------------------------------------------------------------
-- Remark 2.8 for circuits (PathSum.CRK.Structural)

-- Circuits over {H, CNOT, R_k, R_k†} related by exchanging adjacent
-- gates on disjoint wires (_∼_) have path-sums with the same
-- normalisation and the same phase and output coefficients once the
-- path variables are renamed along a permutation read off the
-- derivation (two Hadamards exchanged swap their variables) -- hence
-- ≋.  The renaming cannot be dropped: H on wire 0 then wire 1 against
-- the other order (renaming-needed).  Relabelling a circuit's wires
-- relabels its path-sum.

structural : {C C′ : KP.Circuit n} → C ∼ C′ →
             Σ (Perm.Permutation (KP.paths C) (KP.paths C′))
               (λ π → KP.⟦ C ⟧ ≡ᴿ⟨ π ⟩ KP.⟦ C′ ⟧)
structural = Str.structural

structural-≋ : {C C′ : KP.Circuit n} → C ∼ C′ → KP.⟦ C ⟧ ≋ KP.⟦ C′ ⟧
structural-≋ = Str.structural-≋

parallel-⟦⟧ : (C D : KP.Circuit n) → Str.Apart C D →
              Σ (Perm.Permutation (KP.paths (C ++ D)) (KP.paths (D ++ C)))
                (λ π → KP.⟦ C ++ D ⟧ ≡ᴿ⟨ π ⟩ KP.⟦ D ++ C ⟧)
parallel-⟦⟧ = Str.parallel-⟦⟧

relabel-⟦⟧ : ∀ {n′} (σ : Perm.Permutation n n′) (C : KP.Circuit n) →
             relabel σ KP.⟦ C ⟧ ≡ᴿ⟨ Str.paths-cast σ C ⟩
             KP.⟦ Str.relabelC σ C ⟧
relabel-⟦⟧ = Str.relabel-⟦⟧

structural-≃-≋ : ∀ {n′} {C : KP.Circuit n} {σ : Perm.Permutation n n′}
                 {C′ : KP.Circuit n′} → C ≃⟨ σ ⟩ C′ →
                 relabel σ KP.⟦ C ⟧ ≋ KP.⟦ C′ ⟧
structural-≃-≋ = Str.structural-≃-≋

renaming-needed : (Str.HH₀₁ ∼ Str.HH₁₀) ×
                  ¬ (KP.⟦ Str.HH₀₁ ⟧ ≡ᴿ⟨ Perm.id ⟩ KP.⟦ Str.HH₁₀ ⟧)
renaming-needed = Str.HH-∼ , Str.renaming-needed


------------------------------------------------------------------------
-- Remark 2.8, continued (PathSum.Permute.Congruence,
-- PathSum.Permute.Hexagon, PathSum.Compose.Relabel,
-- PathSum.Compose.Relabel.Sharp, PathSum.CRK.RenamingNeeded)

-- Congruence up to renaming is an equivalence: symmetric along the
-- inverse renaming, transitive along the composite.

≈ᴿ-sym : {ξ : PathSum n k m} {π : Perm.Permutation m m′}
         {ζ : PathSum n k′ m′} → ξ ≈ᴿ⟨ π ⟩ ζ → ζ ≈ᴿ⟨ Perm.flip π ⟩ ξ
≈ᴿ-sym = PmC.≈ᴿ-sym

≈ᴿ-trans : {ξ : PathSum n k m} {π : Perm.Permutation m m′}
           {ζ : PathSum n k′ m′} {ρ : Perm.Permutation m′ m″}
           {χ : PathSum n k″ m″} →
           ξ ≈ᴿ⟨ π ⟩ ζ → ζ ≈ᴿ⟨ ρ ⟩ χ → ξ ≈ᴿ⟨ π Perm.∘ₚ ρ ⟩ χ
≈ᴿ-trans = PmC.≈ᴿ-trans

-- Relabelling the wires is functorial over both compositions, with no
-- renaming of the path variables and the outputs equal as integers.

relabel-∘ᴾ : ∀ {n′} (σ : Perm.Permutation n n′) (ξ′ : PathSum n k′ m′)
             (ξ : PathSum n k m) →
             relabel σ (ξ′ ∘ᴾ ξ) ≡ᴿ⟨ Perm.id ⟩ (relabel σ ξ′ ∘ᴾ relabel σ ξ)
relabel-∘ᴾ = Rel.relabel-∘ᴾ

relabel-⊗ᴾ : ∀ {n₁′ n₂′} (σ : Perm.Permutation n₁ n₁′)
             (τ : Perm.Permutation n₂ n₂′)
             (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
             relabel (σ ⊕ᵖ τ) (ξ₁ ⊗ᴾ ξ₂) ≡ᴿ⟨ Perm.id ⟩
             (relabel σ ξ₁ ⊗ᴾ relabel τ ξ₂)
relabel-⊗ᴾ = Rel.relabel-⊗ᴾ

-- Conjugation by SWAP is relabelling along the braiding (outputs
-- modulo 2: SWAP's outputs carry the lifts of ξ's).

swap-conjugateᴿ : (ξ : PathSum (n + n) k m) →
                  ((swapᴾ n ∘ᴾ ξ) ∘ᴾ swapᴾ n) ≈ᴿ⟨ Blk.unitʳᵖ m ⟩
                  relabel (Blk.braidᵖ n n) ξ
swap-conjugateᴿ {n = n} ξ = Rel.swap-conjugateᴿ {n = n} ξ

-- The drawn form of bifunctoriality, in either order, and the two
-- orders against each other (outputs modulo 2).

⊗-sequentialᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
                ((ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂))
                ≈ᴿ⟨ Rel.seqᵖ m₁ m₂ ⟩ (ξ₁ ⊗ᴾ ξ₂)
⊗-sequentialᴿ = Rel.⊗-sequentialᴿ

⊗-sequential′ᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
                 ((idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂}))
                 ≈ᴿ⟨ Rel.seq′ᵖ m₁ m₂ ⟩ (ξ₁ ⊗ᴾ ξ₂)
⊗-sequential′ᴿ = Rel.⊗-sequential′ᴿ

remark-2-8ᴿ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
              ((ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂))
              ≈ᴿ⟨ Rel.seqᵖ m₁ m₂ Perm.∘ₚ Perm.flip (Rel.seq′ᵖ m₁ m₂) ⟩
              ((idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂}))
remark-2-8ᴿ = Rel.remark-2-8ᴿ

-- Where the lifts enter, congruence is the best one gets: none of the
-- four ≈ᴿ laws above (both drawn forms, the two orders against each
-- other, conjugation by SWAP) holds as ≡ᴿ under any renaming, for a
-- one-wire path-sum whose output is 3 x₀.

sequential-sharp :
  (π : Perm.Permutation 0 0) →
  ¬ (((idPS {0} ⊗ᴾ idPS {1}) ∘ᴾ (idPS {0} ⊗ᴾ RelS.three)) ≡ᴿ⟨ π ⟩
     (idPS {0} ⊗ᴾ RelS.three))
sequential-sharp = RelS.sequential-sharp

sequential′-sharp :
  (π : Perm.Permutation 0 0) →
  ¬ (((idPS {1} ⊗ᴾ idPS {0}) ∘ᴾ (RelS.three ⊗ᴾ idPS {0})) ≡ᴿ⟨ π ⟩
     (RelS.three ⊗ᴾ idPS {0}))
sequential′-sharp = RelS.sequential′-sharp

remark-2-8-sharp :
  (π : Perm.Permutation 0 0) →
  ¬ (((RelS.three ⊗ᴾ idPS {0}) ∘ᴾ (idPS {1} ⊗ᴾ idPS {0})) ≡ᴿ⟨ π ⟩
     ((idPS {1} ⊗ᴾ idPS {0}) ∘ᴾ (RelS.three ⊗ᴾ idPS {0})))
remark-2-8-sharp = RelS.remark-2-8-sharp

swap-conjugate-sharp :
  (π : Perm.Permutation 0 0) →
  ¬ (((swapᴾ 1 ∘ᴾ RelS.three₂) ∘ᴾ swapᴾ 1) ≡ᴿ⟨ π ⟩
     relabel (Blk.braidᵖ 1 1) RelS.three₂)
swap-conjugate-sharp = RelS.swap-conjugate-sharp

-- The second hexagon.

hexagon′ᴿ : ∀ a b c (ξ : PathSum (a + (b + c)) k m) →
            relabel (Perm.flip (Blk.assocᵖ c a b))
              (relabel (Blk.braidᵖ (a + b) c)
                (relabel (Perm.flip (Blk.assocᵖ a b c)) ξ))
            ≡ᴿ⟨ Perm.id ⟩
            relabel (Blk.braidᵖ a c ⊕ᵖ Perm.id {b})
              (relabel (Perm.flip (Blk.assocᵖ a c b))
                (relabel (Perm.id {a} ⊕ᵖ Blk.braidᵖ b c) ξ))
hexagon′ᴿ = Rel.hexagon′ᴿ

-- Even congruence needs the renaming, for H on wire 0 then wire 1
-- against the other order.

renaming-needed-≈ : ¬ (KP.⟦ Str.HH₀₁ ⟧ ≈ᴿ⟨ Perm.id ⟩ KP.⟦ Str.HH₁₀ ⟧)
renaming-needed-≈ = KRN.renaming-needed-≈


------------------------------------------------------------------------
-- Remark 2.8 for circuits over {H, S, CZ} (PathSum.Circuit.Trace,
-- PathSum.Circuit.Structural)

-- Exchanging adjacent gates on disjoint wires renames the path
-- variables of ⟦ C ⟧ and of its isometry restriction ⟦ C ⟧ᴿ, and
-- changes nothing else -- hence ≋.

structural-HSCZ : {C C′ : Circuit n} → C CStr.∼ C′ →
                  Σ (Perm.Permutation (Circ.pathsᵁ C) (Circ.pathsᵁ C′))
                    (λ π → ⟦ C ⟧ ≡ᴿ⟨ π ⟩ ⟦ C′ ⟧)
structural-HSCZ = CStr.structural

structural-HSCZ-≋ : {C C′ : Circuit n} → C CStr.∼ C′ → ⟦ C ⟧ ≋ ⟦ C′ ⟧
structural-HSCZ-≋ = CStr.structural-≋

structuralᴿ-HSCZ : {C C′ : Circuit n} → C CStr.∼ C′ →
                   Σ (Perm.Permutation (Circ.paths C) (Circ.paths C′))
                     (λ π → ⟦ C ⟧ᴿ ≡ᴿ⟨ π ⟩ ⟦ C′ ⟧ᴿ)
structuralᴿ-HSCZ = CStr.structuralᴿ

structuralᴿ-HSCZ-≋ : {C C′ : Circuit n} → C CStr.∼ C′ → ⟦ C ⟧ᴿ ≋ ⟦ C′ ⟧ᴿ
structuralᴿ-HSCZ-≋ = CStr.structuralᴿ-≋

parallel-⟦⟧-HSCZ : (C D : Circuit n) → CStr.Apart C D →
                   Σ (Perm.Permutation (Circ.pathsᵁ (C ++ D))
                                       (Circ.pathsᵁ (D ++ C)))
                     (λ π → ⟦ C ++ D ⟧ ≡ᴿ⟨ π ⟩ ⟦ D ++ C ⟧)
parallel-⟦⟧-HSCZ = CStr.parallel-⟦⟧

parallel-⟦⟧ᴿ-HSCZ : (C D : Circuit n) → CStr.Apart C D →
                    Σ (Perm.Permutation (Circ.paths (C ++ D))
                                        (Circ.paths (D ++ C)))
                      (λ π → ⟦ C ++ D ⟧ᴿ ≡ᴿ⟨ π ⟩ ⟦ D ++ C ⟧ᴿ)
parallel-⟦⟧ᴿ-HSCZ = CStr.parallel-⟦⟧ᴿ

renaming-needed-HSCZ : (CStr.HH₀₁ CStr.∼ CStr.HH₁₀) ×
                       ¬ (⟦ CStr.HH₀₁ ⟧ ≈ᴿ⟨ Perm.id ⟩ ⟦ CStr.HH₁₀ ⟧)
renaming-needed-HSCZ = CStr.HH-∼ , CStr.renaming-needed-≈


------------------------------------------------------------------------
-- Definition 2.1's input signatures with Boolean constants, and section
-- 2.1's compatibility condition (PathSum.Signature,
-- PathSum.Signature.Compose, PathSum.Signature.Clean,
-- PathSum.Signature.WithX)

-- Each wire a variable or a Boolean constant.  A signed path-sum
-- σ ⊢ ξ denotes the partial operator of definition 2.1 extended by zero
-- to the inputs σ does not admit, and definition 2.3 for it is ≋ˢ.
-- Without constants it is ≋; with one signature it is ≋ between the
-- path-sums with their constants written in, as the paper writes them.

≋ˢ⇔≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
       (⌜ ξ ⌝ ≋ˢ ⌜ ζ ⌝) ⇔ (ξ ≋ ζ)
≋ˢ⇔≋ = Sig.≋ˢ⇔≋

inline-≋ˢ : (σ : Signature n) (ξ : PathSum n k m) →
            (σ ⊢ ξ) ≋ˢ (σ ⊢ inline σ ξ)
inline-≋ˢ = Sig.inline-≋ˢ

≋ˢ⇔inline : (σ : Signature n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
            ((σ ⊢ ξ) ≋ˢ (σ ⊢ ζ)) ⇔ (inline σ ξ ≋ inline σ ζ)
≋ˢ⇔inline = Sig.≋ˢ⇔inline

-- Constants 0 are the library's |0⟩-restrictions -- a register, one
-- ancilla, a family of ancillas -- and the path-sum with them inline is
-- Register's set0ᶜ.  (Constants 1 are new.)

≋⟨⟩₀⇔≋ˢ : (c : Fin n → Bool) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
          (ξ AReg.≋⟨ c ⟩₀ ζ) ⇔ ((Sig.zeros c ⊢ ξ) ≋ˢ (Sig.zeros c ⊢ ζ))
≋⟨⟩₀⇔≋ˢ = Sig.≋⟨⟩₀⇔≋ˢ

inline-zeros : (c : Fin n → Bool) (ξ : PathSum n k m) →
               inline (Sig.zeros c) ξ ≋ AReg.set0ᶜ c ξ
inline-zeros = Sig.inline-zeros

≋[]₀⇔≋ˢ : (i : Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
          (ξ Ancl.≋[ i ]₀ ζ) ⇔
          ((Sig.at i false ⊢ ξ) ≋ˢ (Sig.at i false ⊢ ζ))
≋[]₀⇔≋ˢ = Sig.≋[]₀⇔≋ˢ

≋[]₀*⇔≋ˢ : (a : Fin j → Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
           (ξ ≋[ a ]₀* ζ) ⇔
           ((Sig.zeros (Sig.image a) ⊢ ξ) ≋ˢ (Sig.zeros (Sig.image a) ⊢ ζ))
≋[]₀*⇔≋ˢ = Sig.≋[]₀*⇔≋ˢ

-- Compatibility.  The paper's condition -- every output on a constant
-- wire is that constant, as a Boolean polynomial -- is decided
-- coefficient by coefficient; on the path-sum written with its
-- constants inline it is compatibility along every path (Möbius
-- inversion), which implies compatibility by the operator's range, but
-- not conversely (P₀ = |0⟩⟨0|); only the range form is a property of
-- the operator.

synCompatible? : (ξ : PathSum n k m) (σ′ : Signature n) →
                 Dec (SynCompatible ξ σ′)
synCompatible? = SigC.synCompatible?

path⇔syn : (σ : Signature n) (ξ : PathSum n k m) (σ′ : Signature n) →
           PathCompatible (σ ⊢ ξ) σ′ ⇔ SynCompatible (inline σ ξ) σ′
path⇔syn = SigC.path⇔syn

path⇒range : (ξ : Signed n k m) (σ′ : Signature n) →
             PathCompatible ξ σ′ → Compatible ξ σ′
path⇒range = SigC.path⇒range

compatible? : (ξ : Signed n k m) (σ′ : Signature n) →
              Dec (Compatible ξ σ′)
compatible? = SigC.compatible?

range⇏path : Compatible ⌜ CE.P₀ ⌝ SigC.const0 ×
             ¬ PathCompatible ⌜ CE.P₀ ⌝ SigC.const0
range⇏path = SigC.range⇏path

path-not-invariant : ⌜ CE.P₀ ⌝ ≋ˢ ⌜ SigC.P₀′ ⌝ ×
                     ¬ PathCompatible ⌜ CE.P₀ ⌝ SigC.const0 ×
                     SynCompatible SigC.P₀′ SigC.const0
path-not-invariant = SigC.path-not-invariant

Compatible-≋ˢ : (ξ : Signed n k m) (ζ : Signed n k′ m′) (σ′ : Signature n) →
                ξ ≋ˢ ζ → Compatible ξ σ′ → Compatible ζ σ′
Compatible-≋ˢ = SigC.Compatible-≋ˢ

-- Definition 2.6 and proposition 2.7 for signed path-sums: the
-- composite (Compose's, with the left signature) has the product of the
-- operators as its matrix when the range of the first lies where the
-- second is defined -- in particular under the paper's own condition
-- -- and that is exactly what the proposition needs.  Then composition
-- is well defined on operators.

prop-2-7ˢ : (ξ′ : Signed n k′ m′) (ξ : Signed n k m) →
            Compatible ξ (sig ξ′) →
            ∀ x z → ampˢ (ξ′ ∘ˢ ξ) x z ≐ (ampˢ ξ′ Mat.⊙ ampˢ ξ) x z
prop-2-7ˢ = SigC.prop-2-7ˢ

prop-2-7-syn : (ξ′ : Signed n k′ m′) (ξ : Signed n k m) →
               SynCompatible (inline (sig ξ) (ps ξ)) (sig ξ′) →
               ∀ x z → ampˢ (ξ′ ∘ˢ ξ) x z ≐ (ampˢ ξ′ Mat.⊙ ampˢ ξ) x z
prop-2-7-syn = SigC.prop-2-7-syn

compatible⇔prop-2-7 : (ξ : Signed n k m) (σ′ : Signature n) →
                      Compatible ξ σ′ ⇔
                      (∀ {k′ m′} (ξ′ : PathSum n k′ m′) →
                       Prop-2-7 (σ′ ⊢ ξ′) ξ)
compatible⇔prop-2-7 = SigC.compatible⇔prop-2-7

∘ˢ-congˡ : (ξ′ : Signed n k′ m′) (η′ : Signed n j′ l′) (ξ : Signed n k m) →
           Compatible ξ (sig ξ′) → Compatible ξ (sig η′) → ξ′ ≋ˢ η′ →
           (ξ′ ∘ˢ ξ) ≋ˢ (η′ ∘ˢ ξ)
∘ˢ-congˡ = SigC.∘ˢ-congˡ

-- Without compatibility: the identity on one wire, then |0⟩ ↦ |0⟩.  As
-- the paper writes it (output 0) the composite is the erasure and the
-- product the projection onto |0⟩; stored with output the variable of
-- the constant wire the composite is the identity.  Proposition 2.7
-- fails for both, and the composite is not a function of the operators.

composite-erases : (SigC.η′₀ ∘ˢ SigC.ξ₀) ≋ˢ ⌜ CE.erase ⌝
composite-erases = SigC.composite-erases

prop-2-7ˢ-fails-η : ¬ Prop-2-7 SigC.η′₀ SigC.ξ₀
prop-2-7ˢ-fails-η = SigC.prop-2-7ˢ-fails-η

prop-2-7ˢ-fails : ¬ Compatible SigC.ξ₀ SigC.const0 ×
                  ¬ Prop-2-7 SigC.ξ′₀ SigC.ξ₀
prop-2-7ˢ-fails = SigC.prop-2-7ˢ-fails

∘ˢ-congˡ-fails : SigC.ξ′₀ ≋ˢ SigC.η′₀ ×
                 ¬ ((SigC.ξ′₀ ∘ˢ SigC.ξ₀) ≋ˢ (SigC.η′₀ ∘ˢ SigC.ξ₀))
∘ˢ-congˡ-fails = SigC.∘ˢ-congˡ-fails

-- Footnote 1: an ancilla is clean exactly when the path-sum prepared
-- with it at 0 is compatible (by its range) with that preparation, so
-- deciding compatibility decides cleanliness; and through footnote 2's
-- reduction, unsatisfiability.  (That this makes compatibility
-- co-NP-hard is not formalised.)

clean⇔compatible : (ξ : PathSum n k m) (a : Fin j → Fin n) →
                   LeavesClean ξ a ⇔ Compatible (prepare a ⊢ ξ) (prepare a)
clean⇔compatible = SigCl.clean⇔compatible

clean₁⇔compatible : (ξ : PathSum n k m) (i : Fin n) →
                    LeavesClean₁ ξ i ⇔
                    Compatible (Sig.at i false ⊢ ξ) (Sig.at i false)
clean₁⇔compatible = SigCl.clean₁⇔compatible

compatible⇔unsat : (φ : HCNF.CNF n) →
                   Compatible (prepare (watched φ) ⊢ KP.⟦ Hard.circuit φ ⟧)
                              (prepare (watched φ)) ⇔
                   HCNF.Unsatisfiable φ
compatible⇔unsat = SigCl.compatible⇔unsat

decide-unsat : SigCl.CompatibilityDecider → (φ : HCNF.CNF n) →
               Dec (HCNF.Unsatisfiable φ)
decide-unsat = SigCl.decide-unsat

-- Preparing a wire in |1⟩ is preparing it in |0⟩ and applying X, for
-- circuits over {H, X, CNOT, R_k, R_k†}: as path-sums with their
-- constants inline, and as signed operators up to X's relabelling of
-- the input.

X-prepares : (w : Fin n) (b : Bool) (C : KX.Circuit n) →
             inline (Sig.at w b) KX.⟦ KX.X w ∷ C ⟧ ≋
             inline (Sig.at w (not b)) KX.⟦ C ⟧
X-prepares = SigX.X-prepares

X-prepares-ampˢ : (w : Fin n) (b : Bool) (C : KX.Circuit n)
                  (x z : Assign n) → x w ≡ b →
                  ampˢ (Sig.at w b ⊢ KX.⟦ KX.X w ∷ C ⟧) x z ≐
                  ampˢ (Sig.at w (not b) ⊢ KX.⟦ C ⟧) (HNet.flip w x) z
X-prepares-ampˢ = SigX.X-prepares-ampˢ


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

-- The converse fails: (1/√2)·id, with its normalisation tied to its
-- two path variables, is WellFormed but not a partial isometry
-- (PathSum.PartialIsometry.Strict.Tied); WellFormed-strict is ½·id
-- written with no path variables.

WellFormed-strict-tied :
  ∃ λ (ξ : PathSum 1 2 2) → WellFormed ξ × ¬ PartialIsometric ξ
WellFormed-strict-tied = Strt.WellFormed-strict-tied

WellFormed-strict :
  ∃ λ (ξ : PathSum 1 2 0) → WellFormed ξ × ¬ PartialIsometric ξ
WellFormed-strict = Strict.WellFormed-strict

-- Lemma 4.1 needs well-formedness: |x⟩ ↦ |x⟩ + |x ⊕ 1⟩ has the
-- identity's restriction and is not the identity
-- (PathSum.Isometry.Counterexample), also with its normalisation tied.

lemma-4-1-needs-WellFormed :
  ∃ λ (ξ : PathSum 1 0 1) → Restriction-id ξ × ¬ (ξ ≋ idPS)
lemma-4-1-needs-WellFormed = IsoC.lemma-4-1-needs-WellFormed

lemma-4-1-needs-WellFormed-tied :
  ∃ λ (ξ : PathSum 1 2 2) → Restriction-id ξ × ¬ (ξ ≋ idPS)
lemma-4-1-needs-WellFormed-tied = IsoC.lemma-4-1-needs-WellFormed-tied

-- Lemma 4.1 for path-sums with constant inputs: on the columns a
-- signature admits, well-formedness and the restriction criterion
-- (PathSum.Signature.Isometry).

lemma-4-1ˢ : (σ : Signature n) (ξ : PathSum n k m) →
             SigI.WellFormedˢ (σ ⊢ ξ) →
             ((σ ⊢ ξ) ≋ˢ (σ ⊢ idPS)) ⇔ SigI.Restriction-idˢ (σ ⊢ ξ)
lemma-4-1ˢ = SigI.lemma-4-1ˢ

lemma-4-1ˢ-partial : (σ : Signature n) (ξ : PathSum n k m) →
                     SigI.PartialIsometricˢ (σ ⊢ ξ) →
                     ((σ ⊢ ξ) ≋ˢ (σ ⊢ idPS)) ⇔ SigI.Restriction-idˢ (σ ⊢ ξ)
lemma-4-1ˢ-partial = SigI.lemma-4-1ˢ-partial

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

-- Lemma 4.2 as printed ("Q non-zero, integer-valued") fails, for a
-- path-sum in definition 2.1's sense -- normalisation tied to its three
-- path variables, Q = 2x₁ -- that is the identity.  (The untied
-- lemma-4-2-as-stated-fails below, normalisation ½ with one path
-- variable, read with 1/√2^m is √2·id, not a counterexample.)

lemma-4-2-as-stated-fails-tied :
  ∃ λ (ξ : PathSum 1 3 3) → ∃ λ (Q : Poly 1 2) →
    (head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q)) ×
    (∀ j → PSub.Absent y[ j ] Q) ×
    (∀ w → NoVar (+ 2) y₀ (out ξ w)) ×
    ¬ (∀ γ → Q γ ≡ 0ℤ) ×
    (ξ ≋ idPS)
lemma-4-2-as-stated-fails-tied = Intf.lemma-4-2-as-stated-fails-tied

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
-- The identity behind [Case] (PathSum.CRK.WithX.Columns,
-- PathSum.Full.WithoutCase, PathSum.Examples.CaseIdentity)

-- Section 3.2 says that [Case] "is a specific case distinction needed
-- to prove the 2-qubit Clifford+T identity (CNOT (X ⊗ T) controlled-H
-- (X ⊗ T†))²" [29].  Over {H, X, CNOT, R_k, R_k†} every circuit is well
-- formed (circuit-WellFormed-X above), so lemma 4.1 applies to it, and
-- Gaussian elimination reifies its restriction (the X gates make the
-- outputs affine).

lemma-4-1-circuit-X : (C : KX.Circuit n) →
                      (KX.⟦ C ⟧ ≋ idPS ⇔ Restriction-id KX.⟦ C ⟧)
lemma-4-1-circuit-X = KXC.lemma-4-1-circuit

reification-circuit-X :
  (C : KX.Circuit n) →
  Gau.Reification (proj₂ (KX.run C K.init)) (KX.norm C)
reification-circuit-X = KXC.reification-circuit

-- Figure 2 without [Case] (FWC._⟶⁻_: [Elim], [ω], [HH], any
-- Boolean-valued quotient, any variable).  A certificate -- two
-- coefficients at every renumbering -- shows that none of its steps
-- applies; then every chain of figure 2 that gets rid of the path
-- variables begins with a [Case].

stuck-without-case! : (i : Fin n) (ξ : PathSum n k (suc m)) →
                      {True (FWC.certificate? i ξ)} → FWC.Stuck⁻ ξ
stuck-without-case! = FWC.stuck⁻!

case-first : (ξ : PathSum n k (suc m)) → FWC.Stuck⁻ ξ → FWC.CaseFirst ξ
case-first = FWC.case-first

-- The identity, closed at M₀ = 0.  CH is (1 ⊗ S H T) CNOT (1 ⊗ T† H S†),
-- whose matrix is twice controlled-H; W is the operator product
-- (X ⊗ T† acts first), Wᶜ its left-to-right reading as a circuit.
-- Both squares are the identity, by their matrices; neither factor is.
-- (The paper does not say how it decomposes controlled-H; "needed" is
-- proved for this decomposition.)

controlled-H-matrix : ExCase.SameMatrix ExCase.CH ExCase.CHᴬ
controlled-H-matrix = ExCase.CH-matrix

case-identity-W² : ExCase.CX.⟦ ExCase.W² ⟧ ExCase.D.≋ idPS
case-identity-W² = ExCase.W²-id

case-identity-Wᶜ² : ExCase.CX.⟦ ExCase.Wᶜ² ⟧ ExCase.D.≋ idPS
case-identity-Wᶜ² = ExCase.Wᶜ²-id

case-W-not-id : ¬ (ExCase.CX.⟦ ExCase.W ⟧ ExCase.D.≋ idPS)
case-W-not-id = ExCase.W-not-id

-- Its isometry restriction W²ᴿ, by elimination: the identity exactly
-- when the circuit is.

case-restriction :
  ExCase.CX.⟦ ExCase.W² ⟧ ExCase.D.≋ idPS ⇔ ExCase.W²ᴿ ExCase.D.≋ idPS
case-restriction = ExCase.W²-restriction

-- [Case] is needed: no [Elim], [ω] or [HH] step applies to the
-- circuit's path-sum or to its restriction, so no chain without [Case]
-- gets rid of the path variables, and every chain of figure 2 that
-- does begins with a [Case].

case-stuck : FWC₀.Stuck⁻ ExCase.CX.⟦ ExCase.W² ⟧
case-stuck = ExCase.W²-stuck⁻

case-stuck-restriction : FWC₀.Stuck⁻ ExCase.W²ᴿ
case-stuck-restriction = ExCase.W²ᴿ-stuck⁻

case-needed : FWC₀.NeedsCase ExCase.CX.⟦ ExCase.W² ⟧
case-needed = ExCase.W²-needs-case

case-first-W² : FWC₀.CaseFirst ExCase.CX.⟦ ExCase.W² ⟧
case-first-W² = ExCase.W²-case-first

-- [Case] suffices: on literals congruent to the path-sum (renumbered)
-- and to the restriction, [Case] at (y₂ , y₁) with X = x₁, then [HH]
-- and [Elim] (path-sum) or [Elim] (restriction), end at a path-sum
-- congruent to the identity; so the circuit is the identity by the
-- rules, and by the restriction and lemma 4.1, without its matrix.

case-chain : ExCase.W²ᵖ Fl₀.⟶ᶠ* ExCase.W²ᵖ₃
case-chain = ExCase.W²ᵖ-chain

case-chain-end : ExB.Cong.Id-syntactic ExCase.W²ᵖ₃
case-chain-end = ExCase.W²ᵖ-end

case-chain-restriction : ExCase.W²ᴿᵖ Fl₀.⟶ᶠ* ExCase.W²ᴿᵖ₂
case-chain-restriction = ExCase.W²ᴿᵖ-chain

case-chain-restriction-end : ExB.Cong.Id-syntactic ExCase.W²ᴿᵖ₂
case-chain-restriction-end = ExCase.W²ᴿᵖ-end

case-by-rules : ExCase.CX.⟦ ExCase.W² ⟧ ExCase.D.≋ idPS
case-by-rules = ExCase.W²-by-rules

case-by-restriction : ExCase.CX.⟦ ExCase.W² ⟧ ExCase.D.≋ idPS
case-by-restriction = ExCase.W²-by-restriction

-- The claim in one statement, for each reading.

case-identity :
  ExCase.CX.⟦ ExCase.W² ⟧ ExCase.D.≋ idPS ×
  FWC₀.Stuck⁻ ExCase.CX.⟦ ExCase.W² ⟧ × FWC₀.Stuck⁻ ExCase.W²ᴿ ×
  FWC₀.NeedsCase ExCase.CX.⟦ ExCase.W² ⟧ × FWC₀.NeedsCase ExCase.W²ᴿ ×
  (ExCase.W²ᵖ Fl₀.⟶ᶠ* ExCase.W²ᵖ₃) × ExB.Cong.Id-syntactic ExCase.W²ᵖ₃ ×
  (ExCase.W²ᴿᵖ Fl₀.⟶ᶠ* ExCase.W²ᴿᵖ₂) ×
  ExB.Cong.Id-syntactic ExCase.W²ᴿᵖ₂
case-identity = ExCase.case-identity

case-identityᶜ :
  ExCase.CX.⟦ ExCase.Wᶜ² ⟧ ExCase.D.≋ idPS ×
  FWC₀.Stuck⁻ ExCase.CX.⟦ ExCase.Wᶜ² ⟧ × FWC₀.Stuck⁻ ExCase.Wᶜ²ᴿ ×
  FWC₀.NeedsCase ExCase.CX.⟦ ExCase.Wᶜ² ⟧ × FWC₀.NeedsCase ExCase.Wᶜ²ᴿ ×
  (ExCase.Wᶜ²ᵖ Fl₀.⟶ᶠ* ExCase.Wᶜ²ᵖ₃) ×
  ExB.Cong.Id-syntactic ExCase.Wᶜ²ᵖ₃ ×
  (ExCase.Wᶜ²ᴿᵖ Fl₀.⟶ᶠ* ExCase.Wᶜ²ᴿᵖ₂) ×
  ExB.Cong.Id-syntactic ExCase.Wᶜ²ᴿᵖ₂
case-identityᶜ = ExCase.case-identityᶜ


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
-- Section 4.1's restriction for any outputs (PathSum.Restrict,
-- PathSum.Restrict.Pivot, PathSum.Restrict.Spec, PathSum.Restrict.Linear,
-- PathSum.Restrict.Removes, PathSum.CRK.WithX.WellFormed)

-- The paper reifies the restriction where an output reads
-- f_w = y_j ⊕ Q, and ignores the outputs it cannot reify.  For any
-- path-sum, a restriction step at such an output -- Q any Boolean
-- polynomial, constants included -- keeps every entry whose output
-- agrees with the input on wire w; along a chain of steps and rules of
-- figure 2, lemma 4.1 holds whatever outputs are left unsolved, so
-- ignoring them is sound.

restricts-amp : {ξ : PathSum n k (suc m)} {w : Fin n} {j : Fin (suc m)}
                {ρ : PathSum n k m} → Restricts ξ w j ρ →
                ∀ x z → z w ≡ x w → amp ξ x z ≐ amp ρ x z
restricts-amp = Rs.restricts-amp

restriction-amp : {ξ : PathSum n k m} {ρ : PathSum n k m′} → ξ ↝* ρ →
                  ∀ x z → (∀ w → Solved ρ w → z w ≡ x w) →
                  amp ξ x z ≐ amp ρ x z
restriction-amp = Rs.restriction-amp

restriction-lemma-4-1 : (ξ : PathSum n k m) {ρ : PathSum n k′ m′} →
                        WellFormed ξ → ξ ⇝* ρ →
                        (ξ ≋ idPS ⇔ Restriction-id ρ)
restriction-lemma-4-1 = Rs.restriction-lemma-4-1

restriction-solved : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
                     WellFormed ξ → ξ ⇝* ρ → (∀ w → Solved ρ w) →
                     (ξ ≋ idPS ⇔ ρ ≋ idPS)
restriction-solved = Rs.restriction-solved

restriction-syntactic : (ξ : PathSum n k m) (ρ : PathSum n k′ 0) →
                        WellFormed ξ → ξ ⇝* ρ →
                        (ξ ≋ idPS ⇔
                         (k′ ≡ 0 × (∀ w → out ρ w ≈[ + 2 ] μ x[ w ]) ×
                          phase ρ ≈[ pow M ] 0ᴾ))
restriction-syntactic = Rs.restriction-syntactic

restriction-refutes : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) → ξ ⇝* ρ →
                      (w : Fin n) (x : Assign n) →
                      (∀ y → Den.outBit ρ x y w ≡ not (x w)) → ¬ (ξ ≋ idPS)
restriction-refutes = Rs.restriction-refutes

noPaths-WellFormed : (ξ : PathSum n 0 0) → WellFormed ξ
noPaths-WellFormed = Rs.noPaths-WellFormed

-- The paper's step: at an output f_w = y_j ⊕ Q (y_j not in Q), the
-- substitution y_j ← x_w ⊕ Q is a restriction step, and every step at
-- that output is it, coefficient by coefficient; a chain of steps
-- removes at most n path variables; Gaussian elimination is a chain of
-- such steps.

restrictᴾ-step : (ξ : PathSum n k (suc m)) (w : Fin n) (j : Fin (suc m)) →
                 Pivot ξ w j → Restricts ξ w j (restrictᴾ ξ w j)
restrictᴾ-step = RPv.restrictᴾ-step

restricts≈restrictᴾ : {ξ : PathSum n k (suc m)} {w : Fin n}
                      {j : Fin (suc m)} {ρ : PathSum n k m} →
                      Pivot ξ w j → Restricts ξ w j ρ →
                      phase ρ ≈[ pow M ] phase (restrictᴾ ξ w j) ×
                      (∀ v → out ρ v ≈[ + 2 ] out (restrictᴾ ξ w j) v)
restricts≈restrictᴾ = RPv.restricts≈restrictᴾ

restriction-removes : {ξ : PathSum n k m} {ρ : PathSum n k m′} →
                      ξ ↝* ρ → m ≤ m′ + n
restriction-removes = RRm.restriction-removes

gauss-restricts : (st : K.State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
                  GF.coefʸ (K.sig st w) j ≡ true →
                  Restricts (KAmp.toPS {k = k} st) w j
                            (KAmp.toPS {k = k} (Gau.step st w j))
gauss-restricts = RLn.gauss-restricts

-- Section 3's specification route, for any specification: a circuit
-- C meets a well-formed ξ exactly when a restriction of the miter
-- ⟦ C† ⟧ ∘ ξ satisfies lemma 4.1's criterion.

spec-restriction : (C : K.Circuit n) (ξ : PathSum n k m)
                   {ρ : PathSum n k′ m′} →
                   WellFormed ξ → (K.⟦ C KA.† ⟧ ∘ᴾ ξ) ⇝* ρ →
                   (K.⟦ C ⟧ ≋ ξ ⇔ Restriction-id ρ)
spec-restriction = RSp.spec-restriction

spec-restriction-syntactic :
  (C : K.Circuit n) (ξ : PathSum n k m) (ρ : PathSum n k′ 0) →
  WellFormed ξ → (K.⟦ C KA.† ⟧ ∘ᴾ ξ) ⇝* ρ →
  (K.⟦ C ⟧ ≋ ξ ⇔
   (k′ ≡ 0 × (∀ w → out ρ w ≈[ + 2 ] μ x[ w ]) × phase ρ ≈[ pow M ] 0ᴾ))
spec-restriction-syntactic = RSp.spec-restriction-syntactic

spec-restriction-refutes :
  (C : K.Circuit n) (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
  (K.⟦ C KA.† ⟧ ∘ᴾ ξ) ⇝* ρ → (w : Fin n) (x : Assign n) →
  (∀ y → Den.outBit ρ x y w ≡ not (x w)) → ¬ (K.⟦ C ⟧ ≋ ξ)
spec-restriction-refutes = RSp.spec-restriction-refutes

-- Circuits with X gates, whose outputs are affine, are well formed, so
-- the same applies to them.

circuit-WellFormed-X : (C : KX.Circuit n) → WellFormed KX.⟦ C ⟧
circuit-WellFormed-X = KXW.circuit-WellFormed


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

-- Section 5.1's translation validation, for circuits at any level --
-- the largest k of an R_k gate, Clifford+T being level 3: reduce the
-- miter's reified
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

-- The paper verifies "a circuit from [20] (Kaye, Laflamme and Mosca)
-- together with a final qubit permutation correction" -- here the
-- textbook circuit, not shown to be the tool's gate for gate -- against
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
-- Section 5.2 and table 2: the hidden shift benchmarks as the paper's
-- tool generates them (PathSum.HiddenShift.Tool, ToolSymbolic,
-- Feynman, Table, ToolExists, with ToolCCZ, LayersX, TraceX,
-- ThreeLayers, ToolRuns)

-- The tool, Feynman, draws its hidden shift instances at random: for
-- n = 2m qubits and A alternations, a shift s and a Maiorana-McFarland
-- g of A blocks, each a ccz and 200 cz or Z draws (Block 200 m).  For
-- every draw: the hidden shift circuit (X primitive, 3n path
-- variables) is HiddenShift's composite HS for the sum of the drawn
-- monomials; with every input read as 0 it is |x⟩ ↦ |s⟩ (the check the
-- tool ran, verifyHiddenShift); the symbolic shift circuit with its
-- data register read as 0 is |x, y⟩ ↦ |y, y⟩ (the tool's
-- verifyHiddenShiftQuantum); and the first is figure 3(a)'s circuit up
-- to ≋.

hidden-shift-tool-≋ : ∀ {d} (s : Assign (m + m)) (Bs : List (HTo.Block d m)) →
                      KX.⟦ HTo.HSᵗ s Bs ⟧ ≋ HSh.HS (HCi.sumᴾ (HTo.gTerms Bs)) s
hidden-shift-tool-≋ = HTo.hidden-shift-tool-≋

hidden-shift-tool-set0 :
  ∀ {d} (s : Assign (m + m)) (Bs : List (HTo.Block d m)) →
  AReg.set0ᶜ (HCi.allMask (m + m)) KX.⟦ HTo.HSᵗ s Bs ⟧ ≋ HSh.specᴾ s
hidden-shift-tool-set0 = HTo.hidden-shift-tool-set0

symbolic-shift-tool-set0 :
  ∀ {d} (Bs : List (HTo.Block d m)) →
  AReg.set0ᶜ (HSy.dataMask (m + m)) KX.⟦ HTSy.SSᵗ Bs ⟧ ≋ HSy.specSᴾ (m + m)
symbolic-shift-tool-set0 = HTSy.symbolic-shift-tool-set0

tool-≋-figure3a : ∀ {d} (s : Assign (m + m)) (Bs : List (HTo.Block d m)) →
                  KX.⟦ HTo.HSᵗ s Bs ⟧ ≋ K.⟦ HCi.HSᶜ (HTo.gTerms Bs) s ⟧
tool-≋-figure3a = HTo.tool-≋-figure3a

-- Gate for gate the tool's own lists: read as the tool writes gates,
-- the circuits are its hiddenShift and hiddenShiftQuantum on the same
-- draws.

prim-HSᵗ : ∀ {d} (s : Assign (m + m)) (Bs : List (HTo.Block d m)) →
           map HFy.prim (HTo.HSᵗ s Bs) ≡
           HFy.hiddenShiftᵀ (m + m) (HFy.shiftᵀ s) (HFy.altsᵀ Bs)
prim-HSᵗ = HFy.prim-HSᵗ

prim-SSᵗ : ∀ {d} (Bs : List (HTo.Block d m)) →
           map HFy.prim (HTSy.SSᵗ Bs) ≡
           HFy.hiddenShiftQuantumᵀ (m + m) (HFy.altsᵀ Bs)
prim-SSᵗ = HFy.prim-SSᵗ

-- printVerStats's four numbers on those lists, for every draw at the
-- tool's 200 draws per alternation (c of them a cz): n qubits (2n for
-- the symbolic shift), 3n path variables, 8n + 2|s| + 414A + 8c
-- (10n + 414A + 8c) Clifford and 14A T gates; and the same columns
-- counted on the circuits (wires touched, path variables).

HSᵗ-printVerStats :
  (s : Assign (m + m)) (Bs : List (HTo.Block 200 m)) →
  HTb.printVerStatsᵀ (map HFy.prim (HTo.HSᵗ s Bs)) ≡
  (m + m , 3 * (m + m) ,
   ((8 * (m + m) + 2 * Qb.#ʷ s) + 414 * length Bs) + 8 * HTb.czs Bs ,
   14 * length Bs)
HSᵗ-printVerStats = HTb.HS-printVerStats

SSᵗ-printVerStats :
  (Bs : List (HTo.Block 200 m)) →
  HTb.printVerStatsᵀ (map HFy.prim (HTSy.SSᵗ Bs)) ≡
  ((m + m) + (m + m) , 3 * (m + m) ,
   (10 * (m + m) + 414 * length Bs) + 8 * HTb.czs Bs ,
   14 * length Bs)
SSᵗ-printVerStats = HTb.SS-printVerStats

HSᵗ-cliffords : (s : Assign (m + m)) (Bs : List (HTo.Block 200 m)) →
                HTb.cliffordsᵀ (map HFy.prim (HTo.HSᵗ s Bs)) ≡
                ((8 * (m + m) + 2 * Qb.#ʷ s) + 414 * length Bs) +
                8 * HTb.czs Bs
HSᵗ-cliffords = HTb.HS-cliffords-200

SSᵗ-cliffords : (Bs : List (HTo.Block 200 m)) →
                HTb.cliffordsᵀ (map HFy.prim (HTSy.SSᵗ Bs)) ≡
                (10 * (m + m) + 414 * length Bs) + 8 * HTb.czs Bs
SSᵗ-cliffords = HTb.SS-cliffords-200

HSᵗ-tcount : (s : Assign (m + m)) (Bs : List (HTo.Block 200 m)) →
             HTb.tcountᵀ (map HFy.prim (HTo.HSᵗ s Bs)) ≡ 14 * length Bs
HSᵗ-tcount = HTb.HS-tcount

SSᵗ-tcount : (Bs : List (HTo.Block 200 m)) →
             HTb.tcountᵀ (map HFy.prim (HTSy.SSᵗ Bs)) ≡ 14 * length Bs
SSᵗ-tcount = HTb.SS-tcount

HSᵗ-paths : (s : Assign (m + m)) (Bs : List (HTo.Block 200 m)) →
            KX.paths (HTo.HSᵗ s Bs) ≡ 3 * (m + m)
HSᵗ-paths = HTb.HS-paths

SSᵗ-paths : (Bs : List (HTo.Block 200 m)) →
            KX.paths (HTSy.SSᵗ Bs) ≡ 3 * (m + m)
SSᵗ-paths = HTb.SS-paths

HSᵗ-qubits : (s : Assign (m + m)) (Bs : List (HTo.Block 200 m)) →
             HTb.qubitsˣ (HTo.HSᵗ s Bs) ≡ m + m
HSᵗ-qubits = HTb.HS-qubits

SSᵗ-qubits : (Bs : List (HTo.Block 200 m)) →
             HTb.qubitsˣ (HTSy.SSᵗ Bs) ≡ (m + m) + (m + m)
SSᵗ-qubits = HTb.SS-qubits

-- Table 2's six rows, for every draw of A alternations of 200 draws:
-- qubits, path variables and T gates as printed, and the printed
-- Clifford count exactly when |s| + 4c (hidden shift) or c (symbolic
-- shift) is the given number.  First counted on the circuits, then
-- with all four columns printVerStats's on the tool's lists (-tool).
-- The table's own draws are unknown (the tool's QuickCheck generator
-- is unseeded), so the Clifford column is characterised, not computed.

table-2-HiddenShift20-4 : HTb.HSRow 10 4 20 60 5254 56 1719
table-2-HiddenShift20-4 = HTb.table-HiddenShift-20-4

table-2-HiddenShift40-5 : HTb.HSRow 20 5 40 120 6466 70 2038
table-2-HiddenShift40-5 = HTb.table-HiddenShift-40-5

table-2-HiddenShift60-10 : HTb.HSRow 30 10 60 180 12784 140 4082
table-2-HiddenShift60-10 = HTb.table-HiddenShift-60-10

table-2-SymbolicShift20-4 : HTb.SSRow 10 4 40 60 5296 56 430
table-2-SymbolicShift20-4 = HTb.table-SymbolicShift-20-4

table-2-SymbolicShift40-5 : HTb.SSRow 20 5 80 120 6638 70 521
table-2-SymbolicShift40-5 = HTb.table-SymbolicShift-40-5

table-2-SymbolicShift60-10 : HTb.SSRow 30 10 120 180 12804 140 1008
table-2-SymbolicShift60-10 = HTb.table-SymbolicShift-60-10

table-2-HiddenShift20-4-tool : HTb.HSRowᵀ 10 4 20 60 5254 56 1719
table-2-HiddenShift20-4-tool = HTb.table-HiddenShift-20-4ᵀ

table-2-HiddenShift40-5-tool : HTb.HSRowᵀ 20 5 40 120 6466 70 2038
table-2-HiddenShift40-5-tool = HTb.table-HiddenShift-40-5ᵀ

table-2-HiddenShift60-10-tool : HTb.HSRowᵀ 30 10 60 180 12784 140 4082
table-2-HiddenShift60-10-tool = HTb.table-HiddenShift-60-10ᵀ

table-2-SymbolicShift20-4-tool : HTb.SSRowᵀ 10 4 40 60 5296 56 430
table-2-SymbolicShift20-4-tool = HTb.table-SymbolicShift-20-4ᵀ

table-2-SymbolicShift40-5-tool : HTb.SSRowᵀ 20 5 80 120 6638 70 521
table-2-SymbolicShift40-5-tool = HTb.table-SymbolicShift-40-5ᵀ

table-2-SymbolicShift60-10-tool : HTb.SSRowᵀ 30 10 120 180 12804 140 1008
table-2-SymbolicShift60-10-tool = HTb.table-SymbolicShift-60-10ᵀ

-- Each row is attained by a draw of the tool's shape, and printVerStats
-- prints the row's four numbers on it: the table is consistent with the
-- tool's generator.

table-2-HiddenShift20-4-attained :
  ∃ λ (s : Assign 20) → ∃ λ (Bs : List (HTo.Block 200 10)) →
  (length Bs ≡ 4) ×
  (HTb.printVerStatsᵀ (map HFy.prim (HTo.HSᵗ s Bs)) ≡ (20 , 60 , 5254 , 56))
table-2-HiddenShift20-4-attained = HTb.HS-20-4-attainedᵀ

table-2-HiddenShift40-5-attained :
  ∃ λ (s : Assign 40) → ∃ λ (Bs : List (HTo.Block 200 20)) →
  (length Bs ≡ 5) ×
  (HTb.printVerStatsᵀ (map HFy.prim (HTo.HSᵗ s Bs)) ≡ (40 , 120 , 6466 , 70))
table-2-HiddenShift40-5-attained = HTb.HS-40-5-attainedᵀ

table-2-HiddenShift60-10-attained :
  ∃ λ (s : Assign 60) → ∃ λ (Bs : List (HTo.Block 200 30)) →
  (length Bs ≡ 10) ×
  (HTb.printVerStatsᵀ (map HFy.prim (HTo.HSᵗ s Bs)) ≡
   (60 , 180 , 12784 , 140))
table-2-HiddenShift60-10-attained = HTb.HS-60-10-attainedᵀ

table-2-SymbolicShift20-4-attained :
  ∃ λ (Bs : List (HTo.Block 200 10)) →
  (length Bs ≡ 4) ×
  (HTb.printVerStatsᵀ (map HFy.prim (HTSy.SSᵗ Bs)) ≡ (40 , 60 , 5296 , 56))
table-2-SymbolicShift20-4-attained = HTb.SS-20-4-attainedᵀ

table-2-SymbolicShift40-5-attained :
  ∃ λ (Bs : List (HTo.Block 200 20)) →
  (length Bs ≡ 5) ×
  (HTb.printVerStatsᵀ (map HFy.prim (HTSy.SSᵗ Bs)) ≡ (80 , 120 , 6638 , 70))
table-2-SymbolicShift40-5-attained = HTb.SS-40-5-attainedᵀ

table-2-SymbolicShift60-10-attained :
  ∃ λ (Bs : List (HTo.Block 200 30)) →
  (length Bs ≡ 10) ×
  (HTb.printVerStatsᵀ (map HFy.prim (HTSy.SSᵗ Bs)) ≡
   (120 , 180 , 12804 , 140))
table-2-SymbolicShift60-10-attained = HTb.SS-60-10-attainedᵀ

-- The rewrite rules find |s⟩ and |s⟩|s⟩ on the tool's own path-sums:
-- complete reductions by figure 2's rules, of exactly 3n steps, ending
-- at the specification coefficient by coefficient; every complete
-- reduction of the symbolic one ends there.  (Constructed chains, not
-- the tool's search.)

tool-exists : ∀ {d} (s : Assign (m + m)) (Bs : List (HTo.Block d m)) →
              Σ (PathSum (m + m) 0 0) (λ ζ →
                Σ (HSim.at0 KX.⟦ HTo.HSᵗ s Bs ⟧ ⟶ᶠ* ζ) (λ steps →
                  lenᶠ steps ≡ 3 * (m + m)))
tool-exists = HTE.tool-exists

tool-finds : ∀ {d} (s : Assign (m + m)) (Bs : List (HTo.Block d m)) →
             Σ (PathSum (m + m) 0 0) (λ ζ →
               (HSim.at0 KX.⟦ HTo.HSᵗ s Bs ⟧ ⟶ᶠ* ζ) ×
               (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
               (phase ζ ≈[ pow M ] 0ᴾ))
tool-finds = HTE.tool-finds

tool-symbolic-exists :
  ∀ {d} (Bs : List (HTo.Block d m)) →
  Σ (PathSum ((m + m) + (m + m)) 0 0) (λ ζ →
    Σ (AReg.set0ᶜ (HSy.dataMask (m + m)) KX.⟦ HTSy.SSᵗ Bs ⟧ ⟶ᶠ* ζ)
      (λ steps → lenᶠ steps ≡ 3 * (m + m)))
tool-symbolic-exists = HTE.tool-symbolic-exists

tool-symbolic-reduces :
  ∀ {d} (Bs : List (HTo.Block d m)) {k′ : ℕ}
  {ζ : PathSum ((m + m) + (m + m)) k′ 0} →
  AReg.set0ᶜ (HSy.dataMask (m + m)) KX.⟦ HTSy.SSᵗ Bs ⟧ ⟶ᶠ* ζ →
  (k′ ≡ 0) ×
  (∀ w → out ζ w ≈[ + 2 ] μ x[ HSy.copy (m + m) w ]) ×
  (phase ζ ≈[ pow M ] 0ᴾ)
tool-symbolic-reduces = HTE.tool-symbolic-reduces

tool-symbolic-finds :
  ∀ {d} (Bs : List (HTo.Block d m)) →
  Σ (PathSum ((m + m) + (m + m)) 0 0) (λ ζ →
    (AReg.set0ᶜ (HSy.dataMask (m + m)) KX.⟦ HTSy.SSᵗ Bs ⟧ ⟶ᶠ* ζ) ×
    (∀ w → out ζ w ≈[ + 2 ] μ x[ HSy.copy (m + m) w ]) ×
    (phase ζ ≈[ pow M ] 0ᴾ))
tool-symbolic-finds = HTE.tool-symbolic-finds


------------------------------------------------------------------------
-- Every function on the Boolean cube is a multilinear polynomial
-- (PathSum.Polynomial.Interpolate)

-- Section 2 takes functions and multilinear polynomials to correspond.
-- Every integer-valued function of n bits is the value of a
-- polynomial, built by interpolation at the head variable, and only of
-- that one (Möbius inversion) ...

multilinear-exists : (F : (Fin n → Bool) → ℤ) → RespectsZ F →
                     ∀ x (y : Fin 0 → Bool) → eval (PInt.polyᶻ F) x y ≡ F x
multilinear-exists = PInt.eval-polyᶻ

multilinear-unique : (F : (Fin n → Bool) → ℤ) → RespectsZ F →
                     (P : Poly n 0) →
                     (∀ x (y : Fin 0 → Bool) → eval P x y ≡ F x) →
                     ∀ γ → P γ ≡ PInt.polyᶻ F γ
multilinear-unique = PInt.polyᶻ-unique

-- ... and every Boolean function is the reading modulo 2 of a
-- polynomial, unique modulo 2.  (The functions must read their
-- argument through its values: RespectsZ, RespectsB.)

boolean-exists : (f : (Fin n → Bool) → Bool) → RespectsB f →
                 ∀ x (y : Fin 0 → Bool) → odd (eval (PInt.polyᴮ f) x y) ≡ f x
boolean-exists = PInt.odd-polyᴮ

boolean-unique : (f : (Fin n → Bool) → Bool) → RespectsB f →
                 (P : Poly n 0) →
                 (∀ x (y : Fin 0 → Bool) → odd (eval P x y) ≡ f x) →
                 P ≈[ + 2 ] PInt.polyᴮ f
boolean-unique = PInt.polyᴮ-unique


------------------------------------------------------------------------
-- Sections 2 and 5.2: the bitwise expansion of x + y is exponentially
-- large (PathSum.Adder.Expansion, PathSum.Adder.Expansion.Lift,
-- PathSum.Adder.Expansion.PathSums)

-- "The polynomial representation of a classical function may grow
-- exponentially large, as in the case of addition."  In the 2n
-- variables x₀, y₀, …, x_(n−1), y_(n−1) (interleaved: AExp.xs, AExp.ys)
-- every polynomial whose values are the carry out modulo 2 has odd
-- coefficients exactly on the monomials of its algebraic normal form
-- ⊕_i x_i y_i Π_{j>i} (x_j ⊕ y_j) ...

carry-anf : (f : Subset (AExp.dbl n) → ℤ) →
            (∀ v → odd (evalˢ f v) ≡
                   ABin.carry-out (AExp.xs v) (AExp.ys v) false) →
            ∀ s → odd (f s) ≡ AExp.cmon s
carry-anf {n} = AExp.carry-anf {n}

-- ... which are 2^n − 1; those of the sum bit i are 2^i + 1 ...

count-cmon : suc (PCnt.count (AExp.cmon {n})) ≡ 2 ^ n
count-cmon {n} = AExp.count-cmon {n}

count-smon : (i : Fin n) → PCnt.count (AExp.smon i) ≡ suc (2 ^ toℕ i)
count-smon {n} = AExp.count-smon {n}

sumbit-anf : (i : Fin n) (f : Subset (AExp.dbl n) → ℤ) →
             (∀ v → odd (evalˢ f v) ≡
                    ABin.sumbit (AExp.xs v) (AExp.ys v) false i) →
             ∀ s → odd (f s) ≡ AExp.smon i s
sumbit-anf {n} = AExp.sumbit-anf {n}

-- ... so a polynomial computing the carry, written down as a list of
-- terms -- in any order, with any repetitions and integer
-- coefficients -- has at least 2^n − 1 of them, one computing the sum
-- bit i at least 2^i + 1.

carry-terms : (ts : List (Subset (AExp.dbl n) × ℤ)) →
              (∀ v → odd (evalˢ (AExp.⟦_⟧ᵗ ts) v) ≡
                     ABin.carry-out (AExp.xs v) (AExp.ys v) false) →
              2 ^ n ≤ suc (length ts)
carry-terms {n} = AExp.carry-terms {n}

sumbit-terms : (i : Fin n) (ts : List (Subset (AExp.dbl n) × ℤ)) →
               (∀ v → odd (evalˢ (AExp.⟦_⟧ᵗ ts) v) ≡
                      ABin.sumbit (AExp.xs v) (AExp.ys v) false i) →
               suc (2 ^ toℕ i) ≤ length ts
sumbit-terms {n} = AExp.sumbit-terms {n}

-- As a Boolean-valued integer polynomial -- the lift, the form in
-- which outputs enter phases -- the carry out is unique and has
-- (3^n − 1)/2 terms.

carry-exact : (f : Subset (AExp.dbl n) → ℤ) →
              (∀ v → evalˢ f v ≡
                     [ ABin.carry-out (AExp.xs v) (AExp.ys v) false ]ᶻ) →
              ∀ s → f s ≡ ALift.cZ s
carry-exact {n} = ALift.carry-exact {n}

count-cZ : suc (2 * PCnt.count (λ s → AExp.nonzero (ALift.cZ {n} s))) ≡
           3 ^ n
count-cZ {n} = ALift.count-cZ {n}

-- So no classical specification of the adder -- a path-sum without
-- path variables computing it -- has a carry output of fewer than
-- 2^n − 1 terms, however it is written: on any adder layout (n =
-- m + 1 bits), every list of terms representing the carry output,
-- modulo 2 as outputs are read, is that long ...

addition-carry-terms :
  (L : AL.Layout (AL.Wire false m) n) (ξ : PathSum n k 0) →
  ξ computes ARip.addition L →
  (ts : List (Mon n 0 × ℤ)) →
  APS.⟦_⟧ᵐ L ts ≈[ + 2 ] out ξ (APS.carry-wire L) →
  2 ^ suc m ≤ suc (length ts)
addition-carry-terms L ξ c =
  APS.adds-carry-terms L ξ (APS.computes-adds L ξ c)

-- ... and so in particular for section 5.2's specification, in the
-- tool's form and in the paper's; its own carry output, a lift, has
-- exactly (3^n − 1)/2 non-zero coefficients on the register monomials.

adderˢ-carry-terms :
  (L : AL.Layout (AL.Wire false m) n) (ts : List (Mon n 0 × ℤ)) →
  APS.⟦_⟧ᵐ L ts ≈[ + 2 ] out (ASp.adderˢ L) (APS.carry-wire L) →
  2 ^ suc m ≤ suc (length ts)
adderˢ-carry-terms = APS.adderˢ-carry-terms

adder₀ˢ-carry-terms :
  (L : AL.Layout (AL.Wire false m) n) (ts : List (Mon n 0 × ℤ)) →
  APS.⟦_⟧ᵐ L ts ≈[ + 2 ] out (ASp.adder₀ˢ L) (APS.carry-wire L) →
  2 ^ suc m ≤ suc (length ts)
adder₀ˢ-carry-terms = APS.adder₀ˢ-carry-terms

adderˢ-carry-lift :
  (L : AL.Layout (AL.Wire false m) n) →
  suc (2 * PCnt.count (λ S →
         AExp.nonzero (out (ASp.adderˢ L) (APS.carry-wire L) (APS.reg L S))))
  ≡ 3 ^ suc m
adderˢ-carry-lift = APS.adderˢ-carry-lift


------------------------------------------------------------------------
-- Section 5.2: the hidden shift algorithm for every bent function
-- (PathSum.HiddenShift.Bent, PathSum.HiddenShift.AnyBent)

-- f on 2m bits is bent with dual f̃ when its Walsh transform is 2^m
-- times the sign of f̃.

Bent-def : ∀ m (f f̃ : Assign (m + m) → Bool) →
           Bent m f f̃ ≡ (∀ a → walsh f a ≡ + (2 ^ m) *ℤ sgn (f̃ a))
Bent-def m f f̃ = refl

walsh-def : (f : Assign n → Bool) (a : Assign n) →
            walsh f a ≡ Σᶻ (λ x → sgn (f x xor dot a x))
walsh-def f a = refl

-- The dual of a bent function is bent, with dual f.

dual-bent : (f f̃ : Assign (m + m) → Bool) → RespectsB f →
            Bent m f f̃ → Bent m f̃ f
dual-bent {m} = HBent.dual-bent {m}

-- "Given oracles O_f′ and O_f̃ for the shifted and dual bent functions
-- f′, f̃, the circuit H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n} is known to
-- implement the mapping |0⟩ ↦ |s⟩": for oracles of any polynomials
-- whose readings are bent and dual ...

hidden-shift-bent : (E Ẽ : Poly (m + m) 0) (s : Assign (m + m)) →
                    Bent m (HSh.boolᴾ E) (HSh.boolᴾ Ẽ) →
                    (z : Assign (m + m)) →
                    amp (HAB.HSᵇ {m} E Ẽ s) 0ᵃ z ≐
                    (if same s z then scale (HSh.hs-norm (m + m)) (zpow 0ℤ)
                     else 0ᴬ)
hidden-shift-bent {m} = HAB.hidden-shift-bent {m}

hidden-shift-bent-≋ : (E Ẽ : Poly (m + m) 0) (s : Assign (m + m)) →
                      Bent m (HSh.boolᴾ E) (HSh.boolᴾ Ẽ) →
                      HSim.at0 (HAB.HSᵇ {m} E Ẽ s) ≋ HSh.specᴾ s
hidden-shift-bent-≋ {m} = HAB.hidden-shift-bent-≋ {m}

-- ... and so for every bent pair of Boolean functions, through their
-- polynomials ...

hidden-shift-any : (f f̃ : Assign (m + m) → Bool) →
                   RespectsB f → RespectsB f̃ → Bent m f f̃ →
                   (s z : Assign (m + m)) →
                   amp (HAB.HSᵇ {m} (PInt.polyᴮ f) (PInt.polyᴮ f̃) s) 0ᵃ z ≐
                   (if same s z then scale (HSh.hs-norm (m + m)) (zpow 0ℤ)
                    else 0ᴬ)
hidden-shift-any {m} = HAB.hidden-shift-any {m}

hidden-shift-any-≋ : (f f̃ : Assign (m + m) → Bool) →
                     RespectsB f → RespectsB f̃ → Bent m f f̃ →
                     (s : Assign (m + m)) →
                     HSim.at0 (HAB.HSᵇ {m} (PInt.polyᴮ f) (PInt.polyᴮ f̃) s)
                     ≋ HSh.specᴾ s
hidden-shift-any-≋ {m} = HAB.hidden-shift-any-≋ {m}

-- ... the Maiorana–McFarland functions being an instance.

hidden-shift-mm : (g : Poly m 0) (s z : Assign (m + m)) →
                  amp (HSh.HS g s) 0ᵃ z ≐
                  (if same s z then scale (HSh.hs-norm (m + m)) (zpow 0ℤ)
                   else 0ᴬ)
hidden-shift-mm = HAB.hidden-shift-mm


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
-- record's decides, polynomial, volume).  The paper's gate set
-- {H, CNOT, R_k} at level ≤ 2, by Gaussian elimination, is the last
-- section below.

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


------------------------------------------------------------------------
-- Corollary 4.4 in polynomial time for the paper's gate set, by
-- Gaussian elimination (PathSum.Cost.Gauss, PathSum.Cost.Gauss.Correct,
-- PathSum.Cost.Gauss.Corollary)

-- Section 4.1's elimination on sparse path-sums, in the cost model: on
-- the path-sum of a circuit over {H, CNOT, R_k, R_k†}, at any order
-- d ≥ max(2, level C), a refutation refutes the circuit, and otherwise
-- the restriction it returns is the identity exactly when the circuit
-- is (lemma 4.1); its cost is at most (L + 79) (n + m + 3)^(3d + 3) on
-- L terms.  The program runs in lockstep with PathSum.Gauss's
-- elimination, and refutes exactly when some input has no solution
-- y with f(x, y) = x; that it refutes exactly when PathSum.Gauss.gauss
-- does is not proved (gauss's pivot choice is private), only that the
-- two never disagree about the identity.

gauss-circuit-refutes :
  (C : K.Circuit n) (d : ℕ) → 2 ⊔ K.level C ≤ d → ∀ {x} →
  PC.value (CGs.gaussᶜ d (proj₂ (PC.value (CInt.interpKᶜ C)))) ≡
  CGs.refutes x →
  ¬ (K.⟦ C ⟧ ≋ idPS)
gauss-circuit-refutes = CGC.circuit-refutes

gauss-circuit-identity :
  (C : K.Circuit n) (d : ℕ) (le : 2 ⊔ K.level C ≤ d)
  {m′ : ℕ} {R′ : Sp.Rep n m′}
  (eq : PC.value (CGs.gaussᶜ d (proj₂ (PC.value (CInt.interpKᶜ C)))) ≡
        CGs.reifies R′) →
  (K.⟦ C ⟧ ≋ idPS ⇔ CGC.reified (CGC.circuit-reifies C d le eq) ≋ idPS)
gauss-circuit-identity = CGC.circuit-identity

cost-gauss : (d : ℕ) (R : Sp.Rep n m) →
             PC.cost (CGs.gaussᶜ d R) ≤
             CGs.gaussBound n m d (length (Sp.terms R))
cost-gauss = CGs.cost-gaussᶜ

gaussBound-def : ∀ n m d L →
                 CGs.gaussBound n m d L ≡ (L + 79) * (3 + (n + m)) ^ (3 * d + 3)
gaussBound-def = CGs.gaussBound-def

-- Corollary 4.4 with its time claim, for the paper's gate set by the
-- paper's route: count the Hadamards, interpret, eliminate, then
-- refute or normalise at order 2 and read the verdict.  The value is
-- true exactly when ⟦ C ⟧ ≋ idPS, at a cost at most
-- 398 (n + |C| + 3)^11, and at most 398 (2 n |C| + 3)^11 in the volume
-- (the Corollary-4-4ᴳ record); and the equivalence of two such
-- circuits through the miter C₁ ++ C₂ †, at a cost at most
-- 400 (n + |C₁| + |C₂| + 3)^11.

corollary-4-4-polytime-Rk : (C : K.Circuit n) → K.level C ≤ 2 →
                            CG.Corollary-4-4ᴳ C
corollary-4-4-polytime-Rk = CG.corollary-4-4-polytime-gauss

decide-correct-Rk : (C : K.Circuit n) → K.level C ≤ 2 →
                    (PC.value (CG.decideᴳᶜ C) ≡ true ⇔ K.⟦ C ⟧ ≋ idPS)
decide-correct-Rk = CG.decideᴳ-correct

decide?-Rk : (C : K.Circuit n) → K.level C ≤ 2 → Dec (K.⟦ C ⟧ ≋ idPS)
decide?-Rk = CG.decideᴳ?

decideBound-Rk-def : ∀ n ℓ → CG.decideᴳBound n ℓ ≡ 398 * (3 + (n + ℓ)) ^ 11
decideBound-Rk-def = CG.decideᴳBound-def

volumeBound-Rk-def : ∀ v → CG.volumeᴳBound v ≡ 398 * (3 + 2 * v) ^ 11
volumeBound-Rk-def = CG.volumeᴳBound-def

cost-decide-Rk : (C : K.Circuit n) → K.level C ≤ 2 →
                 PC.cost (CG.decideᴳᶜ C) ≤ CG.decideᴳBound n (length C)
cost-decide-Rk = CG.cost-decideᴳᶜ

cost-decide-volume-Rk : (C : K.Circuit n) → K.level C ≤ 2 →
                        PC.cost (CG.decideᴳᶜ C) ≤
                        CG.volumeᴳBound (n * length C)
cost-decide-volume-Rk = CG.cost-decideᴳ-volume

equivalence-polytime-Rk : (C₁ C₂ : K.Circuit n) → K.level C₁ ≤ 2 →
                          K.level C₂ ≤ 2 → CG.PolyEquivalenceᴳ C₁ C₂
equivalence-polytime-Rk = CG.equivalence-polytime-gauss

equiv-correct-Rk : (C₁ C₂ : K.Circuit n) → K.level C₁ ≤ 2 →
                   K.level C₂ ≤ 2 →
                   (PC.value (CG.equivᴳᶜ C₁ C₂) ≡ true ⇔
                    K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧)
equiv-correct-Rk = CG.equivᴳ-correct

equiv?-Rk : (C₁ C₂ : K.Circuit n) → K.level C₁ ≤ 2 → K.level C₂ ≤ 2 →
            Dec (K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧)
equiv?-Rk = CG.equivᴳ?

equivBound-Rk-def : ∀ n a b →
                    CG.equivᴳBound n a b ≡ 400 * (3 + (n + (a + b))) ^ 11
equivBound-Rk-def = CG.equivᴳBound-def


------------------------------------------------------------------------
-- Corollary 4.4 for every circuit over {H, CNOT, R_k, R_k†}, and the
-- equivalence bounds in the volume (PathSum.Cost.Gauss.Total,
-- PathSum.Cost.Corollary.Volume)

-- The level is computed in the monad (one step per gate, one more per
-- R_k or R_k†), so the decision checks corollary 4.4's promise itself:
-- it answers nothing above level 2 and decideᴳᶜ's verdict otherwise --
-- correct for every circuit, at a cost at most 399 (n + |C| + 3)^11,
-- and 399 (2 n |C| + 3)^11 in the volume.  Equivalence goes through
-- the miter, whose level is the larger of the two: at most
-- 401 (n + |C₁| + |C₂| + 3)^11, and 401 (2 n (|C₁| + |C₂|) + 3)^11 in
-- the volume.  PathSum.Cost.Gauss.Corollary's equivalence (levels
-- assumed) costs at most 400 (2 n (|C₁| + |C₂|) + 3)^11 in the volume,
-- and PathSum.Cost.Corollary's, over {H, S, CZ}, at most
-- 315 (6 n (|C₁| + |C₂|) + 3)^12.

level-total : (C : K.Circuit n) → PC.value (CGT.levelᶜ C) ≡ K.level C
level-total = CGT.value-levelᶜ

cost-level-total : (C : K.Circuit n) → PC.cost (CGT.levelᶜ C) ≤ 2 * length C
cost-level-total = CGT.cost-levelᶜ

decide-total-correct : (C : K.Circuit n) (b : Bool) →
                       (PC.value (CGT.decideᴷᶜ C) ≡ just b ⇔
                        (K.level C ≤ 2 × (b ≡ true ⇔ K.⟦ C ⟧ ≋ idPS)))
decide-total-correct = CGT.decideᴷ-correct

decide-total-nothing : (C : K.Circuit n) →
                       (PC.value (CGT.decideᴷᶜ C) ≡ nothing ⇔
                        (¬ (K.level C ≤ 2)))
decide-total-nothing = CGT.decideᴷ-nothing

decide-total-agrees : (C : K.Circuit n) → K.level C ≤ 2 →
                      PC.value (CGT.decideᴷᶜ C) ≡
                      just (PC.value (CG.decideᴳᶜ C))
decide-total-agrees = CGT.decideᴷ-agrees

decideBound-total-def : ∀ n ℓ →
                        CGT.decideᴷBound n ℓ ≡ 399 * (3 + (n + ℓ)) ^ 11
decideBound-total-def = CGT.decideᴷBound-def

volumeBound-total-def : ∀ v → CGT.volumeᴷBound v ≡ 399 * (3 + 2 * v) ^ 11
volumeBound-total-def = CGT.volumeᴷBound-def

corollary-4-4-polytime-total : (C : K.Circuit n) → CGT.Corollary-4-4ᴷ C
corollary-4-4-polytime-total = CGT.corollary-4-4-polytime-total

equiv-total-correct : (C₁ C₂ : K.Circuit n) (b : Bool) →
                      (PC.value (CGT.equivᴷᶜ C₁ C₂) ≡ just b ⇔
                       ((K.level C₁ ≤ 2 × K.level C₂ ≤ 2) ×
                        (b ≡ true ⇔ K.⟦ C₁ ⟧ ≋ K.⟦ C₂ ⟧)))
equiv-total-correct = CGT.equivᴷ-correct

equivBound-total-def : ∀ n a b →
                       CGT.equivᴷBound n a b ≡ 401 * (3 + (n + (a + b))) ^ 11
equivBound-total-def = CGT.equivᴷBound-def

equivVolumeBound-total-def : ∀ v →
                             CGT.equivᴷVolumeBound v ≡ 401 * (3 + 2 * v) ^ 11
equivVolumeBound-total-def = CGT.equivᴷVolumeBound-def

equivalence-polytime-total : (C₁ C₂ : K.Circuit n) →
                             CGT.PolyEquivalenceᴷ C₁ C₂
equivalence-polytime-total = CGT.equivalence-polytime-total

equivVolumeBound-Rk-def : ∀ v →
                          CGT.equivᴳVolumeBound v ≡ 400 * (3 + 2 * v) ^ 11
equivVolumeBound-Rk-def = CGT.equivᴳVolumeBound-def

equivalence-polytime-volume-Rk : (C₁ C₂ : K.Circuit n) → K.level C₁ ≤ 2 →
                                 K.level C₂ ≤ 2 → CGT.PolyEquivalenceᴳᵛ C₁ C₂
equivalence-polytime-volume-Rk = CGT.equivalence-polytime-gauss-volume

equivVolumeBound-def : ∀ v →
                       CCorV.equivVolumeBound v ≡ 315 * (3 + 6 * v) ^ 12
equivVolumeBound-def = CCorV.equivVolumeBound-def

equivalence-polytime-volume : (C₁ C₂ : Circuit n) →
                              CCorV.PolyEquivalenceᵛ C₁ C₂
equivalence-polytime-volume = CCorV.equivalence-polytime-volume
