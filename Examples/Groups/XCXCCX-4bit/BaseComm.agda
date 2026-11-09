------------------------------------------------------------------------
-- Presentations of groups
--
-- The three base commutations of the controlled matchings
--
-- Ḡ = X₃ CX₃₀ X₃ is X on wire 0 controlled by wire 3 = 0, and Q CX₃₀ Q⁻¹,
-- for a circuit Q of the lower wires, is the matching Q μ₀ Q⁻¹
-- controlled by wire 3 = 1.  They act on disjoint halves of the
-- states, so they commute; CRel needs this for one Q of each of the
-- five union types of the matching with μ₀ (CLabels' baseQ).  Two of
-- them are three-wire identities (CBC); the other three, written here,
-- are derivations of PlacedEngine whose steps are rule (7) under a
-- relabelling of the wires and three-wire steps justified by
-- completeness on three wires, found by gen/bc_targets.py with the
-- equations of Equations4 as lemmas (gen/bc_results.json) and written
-- out by gen/mk_basecomm.py.  A letter CCX_{a,b→t} is the Toffoli with
-- controls a, b and target t.  Wire 0 is the bottom wire, and words
-- are in diagram order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.BaseComm where

open import Data.List.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ)
open import Examples.Groups.XCXCCX-4bit.PlacedEngine


-- Ḡ against G placed by CCX_{2,0→1} (union type 2 + 1 + 1).
BC211⁼ : Eqnᵖ
BC211⁼ = derive
  (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ [])
  (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ [])
  (narrow 0 3 (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 0 (Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 5 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 5 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 4 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 8 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 1 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ []) ∷
   rw 11 (r7at ₁ ₀ ₃ ₂) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 11 0 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 13 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 16 4 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 15 3 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 3 (Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 5 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   narrow 5 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 12 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 13 1 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 9 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 10 2 [] ∷
   narrow 8 6 (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   narrow 9 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 7 2 [] ∷
   narrow 5 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 4 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   rw 6 (r7at ₁ ₃ ₀ ₂) ∷
   narrow 7 2 [] ∷
   narrow 4 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 9 3 (Xᵖ ₂ ∷ []) ∷
   narrow 3 3 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 4 3 (CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 5 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 6 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 8 0 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₃ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 12 2 (CXᵖ ₁ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₁ ₃ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₃ ₁ ₂ ₀)) ∷
   narrow 13 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₁ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   rw 11 (r7at ₃ ₁ ₂ ₀) ∷
   narrow 12 2 [] ∷
   narrow 13 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 14 0 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 17 3 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 11 3 (Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 3 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 12 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 13 3 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 3 (CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 11 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 12 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 4 (CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 8 (r7at ₁ ₃ ₀ ₂) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 4 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 9 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 7 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 8 (r7at ₀ ₁ ₂ ₃) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 8 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 2 4 [] ∷
   narrow 0 2 (CXᵖ ₃ ₀ ∷ Xᵖ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 2 1 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ []) ∷
   narrow 3 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 0 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 1 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 4 0 (Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 4 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 4 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 3 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 7 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 8 1 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 10 (r7at ₁ ₀ ₃ ₂) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 10 0 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 12 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 15 4 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 14 3 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 3 (Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 5 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   narrow 4 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 11 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 12 1 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 8 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 9 2 [] ∷
   narrow 7 6 (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   narrow 8 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 6 2 [] ∷
   narrow 4 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 3 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   rw 5 (r7at ₁ ₃ ₀ ₂) ∷
   narrow 6 2 [] ∷
   narrow 3 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 8 3 (Xᵖ ₂ ∷ []) ∷
   narrow 2 3 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 3 3 (CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 4 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 2 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 5 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 4 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 7 0 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 11 2 (CXᵖ ₁ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₃ ₁ ₂ ₀)) ∷
   narrow 12 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   rw 10 (r7at ₃ ₁ ₂ ₀) ∷
   narrow 11 2 [] ∷
   narrow 12 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 13 0 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 16 3 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 10 3 (Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 3 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 11 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 12 3 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 3 (CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 10 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 11 2 [] ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 4 (CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 7 (r7at ₁ ₃ ₀ ₂) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 4 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 8 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 6 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 9 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 7 (r7at ₀ ₁ ₂ ₃) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 8 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 7 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 3 2 [] ∷
   narrow 2 2 [] ∷
   narrow 3 2 [] ∷
   narrow 2 2 [] ∷
   narrow 1 2 [] ∷
   narrow 0 2 [] ∷
   narrow 3 2 (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   [])
  Eq.refl

-- Ḡ against G placed by CCX_{2,0→1} CCX_{1,0→2} (union type 3 + 1).
BC31⁼ : Eqnᵖ
BC31⁼ = derive
  (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
   CCXᵖ ₀ ₂ ₁ ∷ [])
  (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
   CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ [])
  (narrow 8 0 (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 0 3 (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 3 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 0 (Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 9 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 1 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (r7at ₂ ₀ ₃ ₁) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 0 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 17 4 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 3 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 5 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 13 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 1 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 10 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 11 2 [] ∷
   narrow 9 6 (CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   narrow 10 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 8 2 [] ∷
   narrow 6 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   rw 7 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 8 2 [] ∷
   narrow 5 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 3 (Xᵖ ₁ ∷ []) ∷
   narrow 4 3 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 5 3 (CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 6 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 8 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 7 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 9 0 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CXᵖ ₂ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷
   narrow 14 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   rw 12 (r7at ₃ ₂ ₁ ₀) ∷
   narrow 13 2 [] ∷
   narrow 14 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 15 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 18 3 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 12 3 (Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 14 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 12 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 13 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 4 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 9 (r7at ₂ ₃ ₀ ₁) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 8 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (r7at ₀ ₂ ₁ ₃) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 9 2 [] ∷
   narrow 9 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 6 0 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 8 0 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 11 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 1 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 14 (r7at ₂ ₀ ₃ ₁) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 15 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 19 4 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 18 3 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 5 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 15 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 1 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 12 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 13 2 [] ∷
   narrow 11 6 (CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   narrow 12 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 10 2 [] ∷
   narrow 8 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   rw 9 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 10 2 [] ∷
   narrow 6 3 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 7 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 7 2 (CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   narrow 8 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 10 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   narrow 9 1 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 12 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₂ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 3 (CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 10 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 11 2 [] ∷
   narrow 8 1 (Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 12 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 12 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 13 (r7at ₀ ₂ ₁ ₃) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 6 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   narrow 19 1 (CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ []) ∷
   rw 15 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 16 2 [] ∷
   narrow 15 4 [] ∷
   narrow 14 0 (CXᵖ ₂ ₃ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷
   narrow 12 2 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 2 (CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 13 (r7at ₃ ₂ ₁ ₀) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₂ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 3 (CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 7 [] ∷
   rw 7 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   rw 4 (r7at ₂ ₀ ₃ ₁) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₂ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 6 4 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 6 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 8 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 8 0 (Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 11 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 1 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 14 (r7at ₁ ₀ ₃ ₂) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 15 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 19 4 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 18 3 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 3 (Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 5 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 15 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 1 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 12 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 13 2 [] ∷
   narrow 11 6 (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   narrow 12 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 10 2 [] ∷
   narrow 8 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   rw 9 (r7at ₁ ₃ ₀ ₂) ∷
   narrow 10 2 [] ∷
   narrow 7 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 12 3 (Xᵖ ₂ ∷ []) ∷
   narrow 6 3 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 7 3 (CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 9 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 10 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 9 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 11 0 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 2 (CXᵖ ₁ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₃ ₁ ₂ ₀)) ∷
   narrow 16 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₁ ₃ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   rw 14 (r7at ₃ ₁ ₂ ₀) ∷
   narrow 15 2 [] ∷
   narrow 16 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 17 0 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 16 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 20 3 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 14 3 (Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 3 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 16 3 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 3 (CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 14 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 15 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 4 (CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 11 (r7at ₁ ₃ ₀ ₂) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 4 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 12 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 11 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 10 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 11 (r7at ₀ ₁ ₂ ₃) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 11 2 [] ∷
   narrow 11 2 [] ∷
   narrow 10 2 [] ∷
   narrow 9 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 5 4 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (Xᵖ ₀ ∷ []) ∷
   narrow 7 4 (Xᵖ ₀ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 2 (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 2 (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 5 3 (CXᵖ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 2 3 (Xᵖ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 0 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 7 0 (Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 7 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 10 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 1 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 13 (r7at ₂ ₀ ₃ ₁) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 0 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 18 4 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 17 3 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 5 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   narrow 7 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 14 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 1 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 11 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 12 2 [] ∷
   narrow 10 6 (CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   narrow 11 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 9 2 [] ∷
   narrow 7 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   rw 8 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 9 2 [] ∷
   narrow 6 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 11 3 (Xᵖ ₁ ∷ []) ∷
   narrow 5 3 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 6 3 (CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 9 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 8 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 10 0 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 2 (CXᵖ ₂ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷
   narrow 15 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   rw 13 (r7at ₃ ₂ ₁ ₀) ∷
   narrow 14 2 [] ∷
   narrow 15 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 16 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 15 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 19 3 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 13 3 (Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 15 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 13 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 14 2 [] ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 4 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 10 (r7at ₂ ₃ ₀ ₁) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 11 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 9 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 10 (r7at ₀ ₂ ₁ ₃) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 10 2 [] ∷
   narrow 10 2 [] ∷
   narrow 9 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 5 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 4 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 4 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 8 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 7 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 10 0 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 2 (CXᵖ ₂ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷
   narrow 15 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   rw 13 (r7at ₃ ₂ ₁ ₀) ∷
   narrow 14 2 [] ∷
   narrow 15 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 16 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 15 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 19 3 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 13 3 (Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 15 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 13 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 14 2 [] ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 4 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 10 (r7at ₂ ₃ ₀ ₁) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 11 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 9 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 10 (r7at ₀ ₂ ₁ ₃) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 10 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 2 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 7 2 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 6 2 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 10 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 7 3 (CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 8 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   narrow 10 0 (CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 11 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 12 2 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   narrow 11 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 13 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 16 4 (Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 15 2 [] ∷
   narrow 10 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CXᵖ ₃ ₂ ∷ []) ∷
   narrow 9 4 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 18 1 (CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 19 1 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 15 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 16 2 [] ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 4 [] ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 7 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 8 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 8 5 [] ∷
   narrow 6 4 [] ∷
   narrow 5 2 [] ∷
   narrow 4 3 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 0 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 1 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 2 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 2 0 (Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 2 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 2 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 1 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 5 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 5 1 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 6 1 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 8 (r7at ₁ ₀ ₃ ₂) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 0 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 4 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 3 (CXᵖ ₃ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 5 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   narrow 2 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 2 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 9 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   perm (CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 1 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 6 (r7at ₁ ₀ ₃ ₂) ∷
   narrow 7 2 [] ∷
   narrow 5 6 (CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   narrow 6 2 (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 4 2 [] ∷
   narrow 2 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 1 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₃ ∷ []) ∷
   rw 3 (r7at ₁ ₃ ₀ ₂) ∷
   narrow 4 2 [] ∷
   narrow 1 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   perm (Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 6 3 (Xᵖ ₂ ∷ []) ∷
   narrow 0 3 (CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 1 3 (CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 2 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 0 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 1 0 (CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   narrow 3 0 (CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   rw 2 (sym⁼ (r7at ₁ ₀ ₃ ₂)) ∷
   narrow 5 0 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 2 (CXᵖ ₁ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₁ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₃ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₃ ₁ ₂ ₀)) ∷
   narrow 10 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₃ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₁ ₃ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   rw 8 (r7at ₃ ₁ ₂ ₀) ∷
   narrow 9 2 [] ∷
   narrow 10 0 (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ []) ∷
   narrow 11 0 (CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 10 (sym⁼ (r7at ₁ ₃ ₀ ₂)) ∷
   narrow 14 3 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 8 3 (Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₃ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 3 (Xᵖ ₂ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 2 (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 8 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 10 3 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ 
         Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₃ ∷ 
         CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
   rw 8 (r7at ₀ ₁ ₂ ₃) ∷
   narrow 9 2 [] ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₃ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₂ ₃ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₀ ₂ ₃ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   rw 5 (r7at ₁ ₃ ₀ ₂) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 4 (CCXᵖ ₀ ₂ ₁ ∷ []) ∷
   narrow 6 0 (CXᵖ ₁ ₀ ∷ CXᵖ ₁ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₀ ₁ ₂ ₃)) ∷
   narrow 4 2 (Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ 
         CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 2 (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   rw 5 (r7at ₀ ₁ ₂ ₃) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ Xᵖ ₂ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 6 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         Xᵖ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ 
         CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₂ ₁ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₂ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₂ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 4 (CCXᵖ ₂ ₃ ₀ ∷ []) ∷
   narrow 5 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 3 2 [] ∷
   narrow 2 2 [] ∷
   narrow 1 2 [] ∷
   narrow 0 2 [] ∷
   narrow 4 2 [] ∷
   narrow 3 2 [] ∷
   narrow 2 2 [] ∷
   narrow 1 2 [] ∷
   narrow 0 2 [] ∷
   [])
  Eq.refl

-- Ḡ against G placed by CX_{0→1} CCX_{1,0→2} (union type 4).
BC4⁼ : Eqnᵖ
BC4⁼ = derive
  (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
   CXᵖ ₀ ₁ ∷ [])
  (CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
   Xᵖ ₃ ∷ [])
  (narrow 8 0 (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ []) ∷
   narrow 12 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 13 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 0 4 (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   narrow 7 4 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 4 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 0 (Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 9 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 1 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (r7at ₂ ₀ ₃ ₁) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 0 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 17 4 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 3 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 5 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 13 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 1 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 10 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 11 2 [] ∷
   narrow 9 6 (CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   narrow 10 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 8 2 [] ∷
   narrow 6 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   rw 7 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 8 2 [] ∷
   narrow 5 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 3 (Xᵖ ₁ ∷ []) ∷
   narrow 4 3 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 5 3 (CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 6 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 8 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 7 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 9 0 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CXᵖ ₂ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷
   narrow 14 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   rw 12 (r7at ₃ ₂ ₁ ₀) ∷
   narrow 13 2 [] ∷
   narrow 14 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 15 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 18 3 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 12 3 (Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 14 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 12 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 13 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 4 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 9 (r7at ₂ ₃ ₀ ₁) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 8 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (r7at ₀ ₂ ₁ ₃) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 9 2 [] ∷
   narrow 9 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 4 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 6 3 (Xᵖ ₃ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 5 2 [] ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₁ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 4 5 (Xᵖ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ []) ∷
   perm (Xᵖ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 0 4 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ []) ∷
   narrow 3 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 0 5 (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 2 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 3 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 4 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 0 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   narrow 6 0 (Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   rw 5 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 9 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 9 1 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ 
         CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ 
         Xᵖ ₃ ∷ []) ∷
   narrow 10 1 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (r7at ₂ ₀ ₃ ₁) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 12 0 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 13 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 17 4 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 16 3 (CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 5 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   narrow 6 1 (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ 
         CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 2 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 13 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 14 1 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 10 (r7at ₂ ₀ ₃ ₁) ∷
   narrow 11 2 [] ∷
   narrow 9 6 (CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   narrow 10 2 (CXᵖ ₀ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 8 2 [] ∷
   narrow 6 3 (CXᵖ ₃ ₀ ∷ []) ∷
   narrow 5 3 (CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₃ ∷ []) ∷
   rw 7 (r7at ₂ ₃ ₀ ₁) ∷
   narrow 8 2 [] ∷
   narrow 5 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 3 (Xᵖ ₁ ∷ []) ∷
   narrow 4 3 (CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 5 3 (CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 6 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 7 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 8 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 4 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 5 0 (CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   narrow 7 0 (CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₂ ∷ []) ∷
   rw 6 (sym⁼ (r7at ₂ ₀ ₃ ₁)) ∷
   narrow 9 0 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₀ ₃ ∷ CXᵖ ₀ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CXᵖ ₂ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ 
         CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷
   narrow 14 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   rw 12 (r7at ₃ ₂ ₁ ₀) ∷
   narrow 13 2 [] ∷
   narrow 14 0 (CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ []) ∷
   narrow 15 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 14 (sym⁼ (r7at ₂ ₃ ₀ ₁)) ∷
   narrow 18 3 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 12 3 (Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₀ ₂ ∷ CXᵖ ₀ ₃ ∷ 
         CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ CXᵖ ₀ ₃ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 3 (Xᵖ ₁ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 13 2 (CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   rw 12 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 14 3 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₂ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 3 (CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ []) ∷
   rw 12 (r7at ₀ ₂ ₁ ₃) ∷
   narrow 13 2 [] ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₀ ₃ ∷ CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ 
         CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 4 (CCXᵖ ₀ ₁ ₃ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   rw 9 (r7at ₂ ₃ ₀ ₁) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₀ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 7 4 (CCXᵖ ₀ ₁ ₂ ∷ []) ∷
   narrow 10 0 (CXᵖ ₂ ₀ ∷ CXᵖ ₂ ₀ ∷ []) ∷
   rw 9 (sym⁼ (r7at ₀ ₂ ₁ ₃)) ∷
   narrow 8 2 (Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 11 2 (CCXᵖ ₁ ₃ ₂ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   rw 9 (r7at ₀ ₂ ₁ ₃) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ CXᵖ ₂ ₀ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₀ ∷ 
         Xᵖ ₁ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 10 3 (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ []) ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ Xᵖ ₁ ∷ CCXᵖ ₁ ₃ ₀ ∷ Xᵖ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₂ ∷ 
         CXᵖ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₀ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 8 4 (CCXᵖ ₁ ₃ ₀ ∷ []) ∷
   narrow 9 2 [] ∷
   narrow 9 2 [] ∷
   narrow 8 2 [] ∷
   narrow 7 2 [] ∷
   narrow 6 2 [] ∷
   narrow 5 2 [] ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 3 4 [] ∷
   perm (CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CCXᵖ ₁ ₃ ₂ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₁ ₃ ₂ ∷ 
         CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₀ ₁ ∷ CCXᵖ ₀ ₁ ₂ ∷ 
         CXᵖ ₃ ₀ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₀ ₁ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) ∷
   narrow 2 2 [] ∷
   narrow 1 2 [] ∷
   narrow 5 2 [] ∷
   narrow 4 2 [] ∷
   narrow 3 2 [] ∷
   narrow 2 2 [] ∷
   narrow 0 4 [] ∷
   [])
  Eq.refl
