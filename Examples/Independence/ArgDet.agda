------------------------------------------------------------------------
-- Presentations of groups
--
-- The weights of the arg det_k separators are determinant phases
--
-- Each fragment separated by arg det_k (Cliff₂ and RCliff₂ by arg det₂
-- at (I), CliffCS₂ by arg det₂ at (I), CNOTdihe₂ by arg det₃ at (C³T))
-- weighs its gates by a table ad, in units of π/4.  Here every entry
-- is checked against the matrix semantics: ⟦ g ⟧ has determinant
-- ω^{ad g} (Semantics.Determinant.ArgDet), and the swap ω⁴ = −1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.ArgDet where

open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Semantics.Qubit using (SWᵍ ; √2 ; √2-cancel ; ω⁸≡1)
open import Examples.Independence.Semantics.Determinant 2 (+ 0) (-[1+ 0 ]) √2 √2-cancel 7 ω⁸≡1
  using (ArgDet)

import Examples.Independence.Clifford.Syntactics       as Cliff
import Examples.Independence.Clifford.Semantics        as Cliff-Sem
import Examples.Independence.Clifford.Minimality       as Cliff-Min
import Examples.Independence.Real-Clifford.Syntactics  as RCliff
import Examples.Independence.Real-Clifford.Semantics   as RCliff-Sem
import Examples.Independence.Real-Clifford.Minimality  as RCliff-Min
import Examples.Independence.Clifford+CS.Syntactics    as CliffCS
import Examples.Independence.Clifford+CS.Semantics     as CliffCS-Sem
import Examples.Independence.Clifford+CS.Minimality    as CliffCS-Min
import Examples.Independence.CNOT-Dihedral.Syntactics  as CNOTdihe
import Examples.Independence.CNOT-Dihedral.Semantics   as CNOTdihe-Sem
import Examples.Independence.CNOT-Dihedral.Minimality  as CNOTdihe-Min

private
  variable
    k : ℕ

-- The swap has determinant −1 = ω⁴.
swap : ArgDet SWᵍ 4
swap = refl

Cliff₂ : (g : Cliff.Gate k) → ArgDet (Cliff-Sem.val Cliff.⌈ g ⌉) (Cliff-Min.ad g)
Cliff₂ Cliff.ω-gate  = refl
Cliff₂ Cliff.H-gate  = refl
Cliff₂ Cliff.S-gate  = refl
Cliff₂ Cliff.CX-gate = refl

RCliff₂ : (g : RCliff.Gate k) → ArgDet (RCliff-Sem.val RCliff.⌈ g ⌉) (RCliff-Min.ad g)
RCliff₂ RCliff.m-gate  = refl
RCliff₂ RCliff.H-gate  = refl
RCliff₂ RCliff.Z-gate  = refl
RCliff₂ RCliff.CX-gate = refl

CliffCS₂ : (g : CliffCS.Gate k) → ArgDet (CliffCS-Sem.val CliffCS.⌈ g ⌉) (CliffCS-Min.ad g)
CliffCS₂ CliffCS.ω-gate  = refl
CliffCS₂ CliffCS.H-gate  = refl
CliffCS₂ CliffCS.S-gate  = refl
CliffCS₂ CliffCS.CS-gate = refl

CNOTdihe₂ : (g : CNOTdihe.Gate k) → ArgDet (CNOTdihe-Sem.val CNOTdihe.⌈ g ⌉) (CNOTdihe-Min.ad g)
CNOTdihe₂ CNOTdihe.ω-gate  = refl
CNOTdihe₂ CNOTdihe.X-gate  = refl
CNOTdihe₂ CNOTdihe.T-gate  = refl
CNOTdihe₂ CNOTdihe.CX-gate = refl
