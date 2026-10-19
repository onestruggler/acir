------------------------------------------------------------------------
-- Presentations of groups
--
-- Five wires: the theory with AX and the controlled four-wire rules is
-- sound and complete
--
-- Five.Complete5 with its two hypotheses discharged: completeness on
-- four wires (Four.Complete) and the generated five-wire lemmas
-- (Five.Inputs5, with the transport of the four-wire rules from
-- Five.MissingInst, which the five-wire rules λ(lf), λ(hyb-sq),
-- λ(hyb-yb) give, and for ck-tct its derivation Five.CKTDerived).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Main where

open import Examples.Groups.Clifford+CS.Four.Complete using (complete₄)
open import Examples.Groups.Clifford+CS.Five.Inputs5 using (inputs)
open import Examples.Groups.Clifford+CS.Five.MissingInst using (missing)
open import Examples.Groups.Clifford+CS.Five.Complete5 (inputs complete₄ (missing complete₄)) complete₄ public
  using (complete₅ ; sound₅)
