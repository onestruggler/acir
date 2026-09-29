------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire evaluations for rule (38) (GeneralN.Canon38)
--
-- c is the CH from wire 2 onto wire 3 and Q the negations of the wires
-- 2 3.  The letters of (320) on the wires 0–3 — the triply controlled
-- ZX and XZ on wire 0 and on wire 1 — pass c once coloured white on the
-- wires 2 3 (`e-ZX`, `e-XZ`, `e-Kb`, `e-Kb′`); c with its control
-- negated is the CH from wire 3 onto wire 1, white, under the swaps of
-- the wires 2 3 and 1 2 (`e-°c`); and c is the CH from wire 2 onto
-- wire 0 under the transposition of the wires 0 3 (`e-pc`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base38 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

c₄ Q₄ : Circuit 4
c₄ = (Ex • CH • Ex) ↑ ↑
Q₄ = X ↑ ↑ • X ↑ ↑ ↑

e-ZX : Evaluated {4} (c₄ • (Q₄ • ΛZX 3 • Q₄)) ((Q₄ • ΛZX 3 • Q₄) • c₄)
e-ZX = evaluated Eq.refl

e-XZ : Evaluated {4} (c₄ • (Q₄ • ΛXZ 3 • Q₄)) ((Q₄ • ΛXZ 3 • Q₄) • c₄)
e-XZ = evaluated Eq.refl

e-Kb : Evaluated {4} (c₄ • (Q₄ • (Ex • ΛZX 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛZX 3 • Ex) • Q₄) • c₄)
e-Kb = evaluated Eq.refl

e-Kb′ : Evaluated {4} (c₄ • (Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄) • c₄)
e-Kb′ = evaluated Eq.refl

e-°c : Evaluated {4} (X ↑ ↑ • c₄ • X ↑ ↑) ((Ex ↑ ↑ • Ex ↑) • (Ex ↑ • °CH • Ex ↑) ↑ • (Ex ↑ • Ex ↑ ↑))
e-°c = evaluated Eq.refl

e-pc : Evaluated {4} ((Ex • (Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • Ex)))) • (Ex ↑ • CH • Ex ↑) • ((((Ex • Ex ↑) • Ex ↑ ↑) • Ex ↑) • Ex)) c₄
e-pc = evaluated Eq.refl
