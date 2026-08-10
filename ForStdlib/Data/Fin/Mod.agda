------------------------------------------------------------------------
-- The Agda standard library
--
-- Modular arithmetic on ℤ/nℤ, represented as Fin n
--
-- This module gathers the whole development.  It is split across four
-- files -- the operations, their algebraic properties, a ring solver,
-- and the theory of a prime modulus -- but users almost always want
-- all four at once.
--
-- (Staged in ForStdlib for upstreaming into Data.Fin.Mod.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Data.Fin.Mod where

import Notations

import ForStdlib.Data.Fin.Mod.Base as Base
import ForStdlib.Data.Fin.Mod.Prime as Prime
import ForStdlib.Data.Fin.Mod.Properties as Properties
import ForStdlib.Data.Fin.Mod.Solver as Solver

------------------------------------------------------------------------
-- Re-export the numeral patterns
--
-- ℤ n is indexed by a numeral and its elements are numerals, so every
-- user of this module needs them.

open Notations public
  using (auto ; ₀ ; ₁ ; ₂ ; ₃ ; ₄)

------------------------------------------------------------------------
-- Re-export the development

open Base public

open Properties public

open Solver public

open Prime public
