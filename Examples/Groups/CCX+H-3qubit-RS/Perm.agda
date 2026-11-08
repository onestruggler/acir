------------------------------------------------------------------------
-- Presentations of groups
--
-- Permutations of the basis states as circuits.
--
-- Symmetric.CoxeterFrames with the circuits T d of Figure 7 for the
-- transpositions of adjacent basis states, at every level k: a Coxeter
-- word is a circuit of Examples.Groups.Symmetric on eight wires, whose
-- wires here are the eight basis states, read with T d for its
-- generator on d, d + 1 (Pc).  Given the Coxeter relations for the
-- circuits T d (Coxeter), two Coxeter words with the same permutation
-- have equivalent circuits (perm-complete), a word fixing the states
-- below j is a word in the T i with i ≥ j (stab), and a circuit those
-- T i commute with, conjugated by a Coxeter word, depends only on where
-- the word sends the states below j (frame≈); frame ts sends 0, 1, …
-- to the distinct states ts.  The action of a Coxeter word on basis
-- states is act: the circuit Pc 0 w sends x to act w x.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Perm where

open import Data.Nat.Base using (ℕ)

open import Examples.Groups.Symmetric.CoxeterFrames public hiding (module Circuits)
import Examples.Groups.Symmetric.CoxeterFrames as CF

open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics using (T)

module _ {k : ℕ} where

  open CF.Circuits (T {k}) public
