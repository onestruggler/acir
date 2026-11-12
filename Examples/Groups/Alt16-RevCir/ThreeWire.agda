------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules (1)–(7) are complete on one, two and three wires
--
-- Two circuits over this folder's gates on at most three wires that
-- are the same function on states are equal by the rules of Theory,
-- and the circuits on one, two and three wires present S₂, S₄ and S₈.
-- Each width is a Reidemeister–Schreier step from Symmetric's
-- presentation of the permutations of the states (BySymmetric), with
-- the Coxeter relations between the edge Toffolis and the gates' words
-- derived from the rules (Width1, Width2, Width3).  On three wires
-- only the rules (1)–(6) and the laws of the swap take part: rule (7)
-- lives on four.
--
-- This is what a step on three wires of a four-wire derivation rests
-- on (FourWire's bot and top).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.ThreeWire where

open import Examples.Groups.Alt16-RevCir.Width1 public
  using (complete₁ ; presentation₁)
open import Examples.Groups.Alt16-RevCir.Width2 public
  using (complete₂ ; presentation₂)
open import Examples.Groups.Alt16-RevCir.Width3 public
  using (complete₃ ; presentation₃)
