------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire facts for (354), decided
--
-- (333) and (334) on four wires: the rotations as words in the H gate
-- (H on wire 0, box wire 1) and the box on wire 2 — the base of the
-- width induction of GeneralN.ZX354, one width below five.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base354 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)

-- The box on wire 2 at width 4.
K₄ : Circuit 4
K₄ = Ex ↑ • (Ex ↓ • Λ□ 3 • Ex ↓) • Ex ↑

e-333 : Evaluated {4} (Hg 1 • K₄ • Hg 1 • K₄) (ΛZX 3)
e-333 = evaluated Eq.refl

e-334 : Evaluated {4} (K₄ • Hg 1 • K₄ • Hg 1) (ΛXZ 3)
e-334 = evaluated Eq.refl
