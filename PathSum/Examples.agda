------------------------------------------------------------------------
-- Presentations of groups
--
-- The paper's worked examples, checked
--
-- The examples of Amy's paper (QPL 2018) as facts about closed
-- path-sums at Clifford+T precision (M₀ = 0, phases in eighths), each
-- reduction chain written out with the paper's quotients and every
-- premise discharged by computation:
--
--  * PathSum.Examples.Section2: example 2.2's Hadamard is the circuit's
--    path-sum, and example 2.12, the order of three polynomials;
--  * PathSum.Examples.Section3: section 3.1, HH = I -- the paper's
--    path-sum, the circuit's own path-sum by the same chain, and the
--    restriction corollary 4.4 reduces;
--  * PathSum.Examples.Toffoli: example 3.3, the Toffoli path-sum
--    reduced to its specification by the paper's column of rules and
--    manipulations, with the general [HH] (quotient x3 ⊕ x1x2); and a
--    seven-T Toffoli circuit, whose path-sum it is;
--  * PathSum.Examples.ControlledT: example 3.4, controlled-T with an
--    ancilla, its path-sum reduced by [HH, Elim] twice (one printed
--    line corrected); and the paper's circuit, which on the inputs
--    whose ancilla is |0⟩ is controlled-T and leaves the ancilla clean;
--  * PathSum.Examples.AppendixB: example B.1, (SH)³ = ω I, by the
--    paper's chain on the circuit itself, and by corollary 4.4's route
--    with lemma 4.1 at the phase ω (PathSum.GlobalPhase); and the
--    path-sum printed for it, which is the identity, not ω I (an
--    erratum);
--  * PathSum.Examples.Adder: example B.2, the full adder, by one
--    general [HH] and [Elim]; and the paper's circuit;
--  * PathSum.Examples.General: the general [ω] and [Case] at work;
--  * PathSum.Examples.Clifford: Clifford identities and non-identities
--    by corollary 4.4's method, lemma 4.2 among the refutations, and
--    the decision procedure run;
--  * PathSum.Examples.Validation: section 5.1's translation validation
--    on small miters -- T;T ≡ S and T;H;H ≡ T proved, X ≢ I and
--    CNOT ≢ I refuted (by lemma 4.2 and by Gaussian elimination);
--  * PathSum.Examples.Brute: cross-checks of all of the above by brute
--    force (PathSum.Brute), which is not the paper's method.
--
-- PathSum.Examples.Base fixes the precision and the notation.  Not
-- covered here: the irreducible Clifford+T identity of section 4.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples where

open import PathSum.Examples.Base public
open import PathSum.Examples.Section2 public
open import PathSum.Examples.Section3 public
open import PathSum.Examples.Toffoli public
open import PathSum.Examples.ControlledT public
open import PathSum.Examples.AppendixB public
open import PathSum.Examples.Adder public
open import PathSum.Examples.General public
open import PathSum.Examples.Clifford public
open import PathSum.Examples.Validation public
open import PathSum.Examples.Brute public
