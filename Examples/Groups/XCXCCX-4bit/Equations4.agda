------------------------------------------------------------------------
-- Presentations of groups
--
-- Equations on four wires, among them the paper's equation (8)
--
-- Each is a derivation of PlacedEngine whose steps are rule (7) under a
-- relabelling of the wires and three-wire steps justified by
-- completeness on three wires, found by gen/pg_search.py
-- (gen/pg_results.json) and written out by gen/mk_equations4.py.  A
-- letter CCX_{a,b→t} is the Toffoli with controls a, b and target t; a
-- bar marks a control that is negated (X on both sides of it).  Wire 0
-- is the bottom wire, and words are in diagram order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Equations4 where

open import Data.List.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ)
open import Examples.Groups.XCXCCX-4bit.PlacedEngine


-- Two Toffolis with the same controls commute.
E2⁼ : Eqnᵖ
E2⁼ = derive
  (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ [])
  (narrow 2 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 1 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 2 0 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 3 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 0 2 [] ∷
   [])
  Eq.refl

-- A Toffoli and a CNOT with the same target commute.
E4⁼ : Eqnᵖ
E4⁼ = derive
  (CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ [])
  (CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (narrow 1 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 2 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 4 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 5 2 [] ∷
   rw 1 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 0 2 [] ∷
   [])
  Eq.refl

-- A Toffoli and a CNOT onto its target from the fourth wire
-- commute.
E8⁼ : Eqnᵖ
E8⁼ = derive
  (CCXᵖ ₁ ₂ ₀ ∷ CXᵖ ₃ ₀ ∷ [])
  (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₀ ∷ [])
  (narrow 1 0 (CCXᵖ ₁ ₂ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   narrow 2 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₁ ₂ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   rw 4 (r7at ₀ ₃ ₁ ₂) ∷
   narrow 5 2 [] ∷
   rw 1 (r7at ₀ ₃ ₁ ₂) ∷
   narrow 0 2 [] ∷
   [])
  Eq.refl

-- A Toffoli commutes with a CNOT from one of its controls onto a
-- wire it does not touch.
E5⁼ : Eqnᵖ
E5⁼ = derive
  (CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ [])
  (narrow 2 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 1 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 0 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 3 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 1 (r7at ₀ ₁ ₂ ₃) ∷
   perm (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 2 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   narrow 0 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   [])
  Eq.refl

-- Toffolis that act on disjoint sets of states commute:
-- CCX_{3,2̄→1} against CCX_{3,2→0}.
E6a⁼ : Eqnᵖ
E6a⁼ = derive
  (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ [])
  (narrow 2 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 3 1 (CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 2 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 0 1 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 2 3 (Xᵖ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ []) ∷
   rw 1 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 3 4 (CXᵖ ₃ ₁ ∷ []) ∷
   narrow 2 4 (CXᵖ ₃ ₁ ∷ []) ∷
   narrow 1 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   [])
  Eq.refl

-- CCX_{3̄,2→1} against CCX_{3,2→0}.
E6e⁼ : Eqnᵖ
E6e⁼ = derive
  (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ [])
  (narrow 2 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 2 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 0 1 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 2 3 (Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₂ ₀ ∷ []) ∷
   rw 1 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 3 4 (CXᵖ ₂ ₁ ∷ []) ∷
   narrow 2 4 (CXᵖ ₂ ₁ ∷ []) ∷
   narrow 1 2 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ []) ∷
   [])
  Eq.refl

-- CCX_{3̄,1→2} against CCX_{3,2→0}.
E6d⁼ : Eqnᵖ
E6d⁼ = derive
  (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ [])
  (narrow 0 3 (CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 3 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 2 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 0 3 (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 1 1 (CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 4 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 5 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   narrow 4 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 9 4 (Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 8 2 [] ∷
   narrow 3 3 (Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 1 4 (CXᵖ ₁ ₀ ∷ []) ∷
   narrow 2 4 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₁ ₀ ∷ []) ∷
   narrow 3 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 6 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 11 1 (CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   narrow 12 1 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 8 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 9 2 [] ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   narrow 7 4 [] ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 5 3 (Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 3 (CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 3 (CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 0 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 1 3 (CXᵖ ₁ ₂ ∷ []) ∷
   narrow 1 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   [])
  Eq.refl

-- CCX_{2̄,1̄→3} against CCX_{3,2→0}.
E6b⁼ : Eqnᵖ
E6b⁼ = derive
  (Xᵖ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₁ ∷ [])
  (perm (Xᵖ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 0 5 (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CXᵖ ₁ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   narrow 5 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 4 (sym⁼ (r7at ₀ ₁ ₃ ₂)) ∷
   narrow 2 3 (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   narrow 3 1 (CXᵖ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₁ ₂ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   rw 6 (r7at ₀ ₃ ₁ ₂) ∷
   narrow 7 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 2 (Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₀ ∷ CCXᵖ ₁ ₂ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₂ ₀ ∷ []) ∷
   narrow 8 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₀ ₃ ₁ ₂)) ∷
   narrow 11 4 (Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ []) ∷
   narrow 10 2 [] ∷
   narrow 5 3 (Xᵖ ₂ ∷ CXᵖ ₁ ₃ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 3 4 (CXᵖ ₁ ₀ ∷ []) ∷
   narrow 4 4 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 5 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 13 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 14 1 (CCXᵖ ₁ ₂ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₂ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₀ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   rw 10 (r7at ₀ ₃ ₁ ₂) ∷
   narrow 11 2 [] ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₀ ∷ CCXᵖ ₁ ₂ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₀ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 4 [] ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ CCXᵖ ₁ ₂ ₀ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₀ ₃ ₁ ₂)) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 7 3 (Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 6 3 (CXᵖ ₁ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 6 3 (CXᵖ ₁ ₃ ∷ CCXᵖ ₁ ₂ ₃ ∷ []) ∷
   rw 2 (r7at ₀ ₁ ₃ ₂) ∷
   narrow 3 3 (CXᵖ ₁ ₃ ∷ []) ∷
   narrow 3 2 (Xᵖ ₂ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 0 4 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   narrow 2 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   [])
  Eq.refl

-- CCX_{3̄,2̄→1} against CCX_{3,2→0}.
E6c⁼ : Eqnᵖ
E6c⁼ = derive
  (Xᵖ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₂ ∷ [])
  (perm (Xᵖ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 0 5 (Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 6 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 5 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 4 2 [] ∷
   narrow 2 2 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ []) ∷
   perm (Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 5 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   rw 3 (r7at ₀ ₁ ₃ ₂) ∷
   perm (Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 4 3 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 2 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 3 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 2 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 1 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 4 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 2 (r7at ₀ ₁ ₂ ₃) ∷
   perm (Xᵖ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 3 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 1 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 1 4 (Xᵖ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₂ ∷ []) ∷
   [])
  Eq.refl

-- The commutator of CCX_{3,2→1} and CCX_{3,1→0} is CCX_{3,2→0}
-- (the controlled Steinberg relation).
E7⁼ : Eqnᵖ
E7⁼ = derive
  (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ [])
  (narrow 3 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   narrow 2 1 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 4 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 3 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 5 3 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 2 3 (CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 3 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 4 2 [] ∷
   narrow 1 1 (Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 3 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 5 3 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 5 2 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 6 (r7at ₁ ₀ ₃ ₂) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₂ ₁ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 2 6 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 5 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 12 1 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ []) ∷
   rw 8 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 9 2 [] ∷
   narrow 8 4 [] ∷
   narrow 7 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 5 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 6 (r7at ₂ ₀ ₃ ₁) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₀ ₂ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₁ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 3 7 [] ∷
   rw 0 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 1 2 [] ∷
   [])
  Eq.refl

-- Two Toffolis with the same target and a common control commute.
E3⁼ : Eqnᵖ
E3⁼ = derive
  (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ [])
  (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
  (narrow 1 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 0 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 0 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 1 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 2 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 4 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 3 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 6 0 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 10 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 11 3 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 3 (CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 9 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 10 2 [] ∷
   narrow 11 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 15 3 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 9 3 (Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 3 (CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 5 3 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 10 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 11 3 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 3 (CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 9 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 10 2 [] ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 6 (r7at ₀ ₂ ₁ ₃) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 4 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 5 2 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 6 (r7at ₁ ₀ ₃ ₂) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₂ ₁ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 5 4 (CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 6 2 [] ∷
   narrow 2 2 [] ∷
   narrow 1 2 [] ∷
   narrow 0 2 [] ∷
   narrow 4 2 [] ∷
   narrow 3 2 (CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 2 2 (Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 6 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 3 3 (CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 4 1 (CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 7 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 8 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 7 2 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 9 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 12 4 (Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ []) ∷
   narrow 11 2 [] ∷
   narrow 6 3 (Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 4 (CXᵖ ₂ ₀ ∷ []) ∷
   narrow 5 4 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 6 1 (CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ []) ∷
   narrow 15 1 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 11 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 12 2 [] ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ []) ∷
   narrow 10 4 [] ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 3 (Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₂ ₀ ∷ []) ∷
   perm (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 3 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 4 3 (CXᵖ ₂ ₁ ∷ []) ∷
   narrow 4 5 [] ∷
   narrow 2 4 [] ∷
   [])
  Eq.refl

-- Equation (8): the CNOT from wire 1 onto wire 2 conjugates the
-- Toffoli from wires 3, 2 onto wire 0 into its product with the
-- Toffoli from wires 3, 1 onto wire 0.
eq8⁼ : Eqnᵖ
eq8⁼ = derive
  (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ [])
  (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ [])
  (narrow 2 0 (Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 2 1 (CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 2 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   rw 1 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 5 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 5 1 (CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 6 1 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   rw 8 (r7at ₀ ₂ ₁ ₃) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 8 0 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 10 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 13 4 (CXᵖ ₁ ₀ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 12 3 (CXᵖ ₁ ₀ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 7 3 (Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 4 4 (CXᵖ ₁ ₂ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₁ ₂ ∷ []) ∷
   narrow 3 5 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 2 1 (CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 4 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 9 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CXᵖ ₁ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 10 1 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 6 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 7 2 [] ∷
   narrow 5 6 (CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   narrow 6 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 4 2 [] ∷
   narrow 2 3 (CXᵖ ₁ ₂ ∷ []) ∷
   narrow 1 3 (CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 3 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 4 2 [] ∷
   narrow 1 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   narrow 3 3 (CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 6 3 (Xᵖ ₃ ∷ []) ∷
   narrow 0 3 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 1 3 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 2 4 (CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 0 0 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 1 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 3 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 2 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 5 0 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 9 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 10 3 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 8 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 9 2 [] ∷
   narrow 10 0 (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 14 3 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 8 3 (Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 4 3 (Xᵖ ₃ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 9 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 10 3 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 8 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 9 2 [] ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 5 (r7at ₀ ₁ ₂ ₃) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₁ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 3 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 6 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 4 2 (Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 5 (r7at ₂ ₀ ₃ ₁) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₀ ₂ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 3 (CXᵖ ₁ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 4 4 (CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 5 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 3 2 [] ∷
   narrow 2 2 [] ∷
   narrow 1 2 [] ∷
   narrow 0 2 [] ∷
   [])
  Eq.refl
