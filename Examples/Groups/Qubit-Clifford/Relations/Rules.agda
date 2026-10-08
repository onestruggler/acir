------------------------------------------------------------------------
-- Presentations of groups
--
-- The equations (3.1) to (3.101) of the supplement: the rewrite rules
-- of Figures 3 to 7, and the equations (3.1), (3.2) that bring the
-- identity to normal form
--
-- One module per figure, which keeps the memory a single run needs to
-- check them within bounds.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Relations.Rules where

open import Examples.Groups.Qubit-Clifford.Relations.Rules.Identity public
open import Examples.Groups.Qubit-Clifford.Relations.Rules.Figure3 public
open import Examples.Groups.Qubit-Clifford.Relations.Rules.Figure4 public
open import Examples.Groups.Qubit-Clifford.Relations.Rules.Figure5 public
open import Examples.Groups.Qubit-Clifford.Relations.Rules.Figure6 public
open import Examples.Groups.Qubit-Clifford.Relations.Rules.Figure7 public
