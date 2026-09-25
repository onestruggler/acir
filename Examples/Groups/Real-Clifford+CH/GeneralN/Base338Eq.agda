------------------------------------------------------------------------
-- Presentations of groups
--
-- The doubly controlled ZX between P ⊗ P against the box on wire 1
-- negated on wire 2, on four wires, decided (GeneralN.Box338Eq)
--
-- RW₄ is CCZX between P ⊗ P on the wires 0 1; Dw₄ the box on wire 1
-- controlled by wire 0, negatively by wire 2, and by wire 3.  They
-- commute (`d-base`), and RW₄ commutes with the two rotation letters of
-- (320) under the same conjugations (`d-zx`, `d-kb`): the base and the
-- letters of Box338Eq's induction.  Each an evaluation of a few
-- seconds; in a module of its own, since Agda frees the memory of an
-- evaluation only when its module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base338Eq where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

-- CCZX between P ⊗ P.
RW₄ : Circuit 4
RW₄ = PP ↓ • CCZX • PP ↓

-- The swap of the wires 0 1 around X on wire 2 around w.
SN : Circuit 4 → Circuit 4
SN w = Ex ↓ • (X ↑ ↑ • w • X ↑ ↑) • Ex ↓

Dw₄ L-zx L-kb : Circuit 4
Dw₄  = SN (Λ□ 3)
L-zx = SN (ΛZX 3 ↓ᵏ 0)
L-kb = SN (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓)

d-base : Evaluated (RW₄ • Dw₄) (Dw₄ • RW₄)
d-base = evaluated Eq.refl

d-zx : Evaluated (RW₄ • L-zx) (L-zx • RW₄)
d-zx = evaluated Eq.refl

d-kb : Evaluated (RW₄ • L-kb) (L-kb • RW₄)
d-kb = evaluated Eq.refl
