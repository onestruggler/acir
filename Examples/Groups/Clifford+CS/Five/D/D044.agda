{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D044 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-sym-ab-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-CXbc-box-at0312243140 ; lem-box-tQ-at0312243140 ; lem-pairs-at032032)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CX21-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CSd04-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS04-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-SWAP14-BOX⟨3·20⟩)
-- CXcb-box @0312243140: 18 steps
lem-CXcb-box-at0312243140 : Complete 4 → ⟪ (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) (Toff324 ∷ CCZ013 ∷ CX14 ∷ Toff312 ∷ CS01 ∷ CX21 ∷ Toff324 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CCZ013 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4) ▸
       at 0 2 (Toff324 ∷ CX14 ∷ Toff312 ∷ []) (lw0 c4 (CX14 ∷ Toff324 ∷ []) (Toff324 ∷ CX14 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (lw4 c4 (Toff312 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX14 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff324 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ Toff324 ∷ []) (Toff324 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX14 ∷ Toff312 ∷ CS01 ∷ CX21 ∷ Toff324 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ CCZ013 ∷ CX14 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ Toff324 ∷ []) (Toff324 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CX14 ∷ Toff312 ∷ []) (lw0 c4 (CX14 ∷ Toff324 ∷ []) (Toff324 ∷ CX14 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX14 ∷ []) (lw0 c4 (CX14 ∷ Toff312 ∷ Toff312 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX14 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-2410 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ CX14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0312243140: 11 steps
lem-SWbc-box-at0312243140 : Complete 4 → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (CX41 ∷ Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-2410 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243140 c4) ▸
       at 4 2 (CX41 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX41 ∷ Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (Bx3-2410 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-2410 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0312243140 c4) ▸
       at 1 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0312243140: 23 steps
lem-nat-SWbc-at0312243140 : Complete 4 → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ Sw14 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸
       at 5 2 (Toff234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ Sw14 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Sw14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸
       at 8 2 (Toff312 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Sw14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Sw14 ∷ []) (Bx3-2140 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-340 ∷ []) (refl) ▸
       at 5 6 (Bx2-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- sym-bc @0312243140: 2 steps
lem-sym-bc-at0312243140 : Complete 4 → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-bc-at0312243140 c4 = run b0
  where
  b0 : Chain (Bx3-2410 ∷ []) (Bx3-2140 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0312243140 c4)) ▸
       at 0 3 (Bx3-2140 ∷ []) (lem-nat-SWbc-at0312243140 c4) ▸ done


-- sym-ab @0312213440: 18 steps
lem-sym-ab-at0312213440 : Complete 4 → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym-ab-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2140 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (pw2 c4 (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-10 ∷ []) (refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ [])
  b1 = at 2 6 (Bx1-340 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (pw2 c4 (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 10 1 (Bx3-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (Bx3-1240 ∷ [])
  b2 = at 5 6 (Bx1-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-1240 ∷ []) (refl) ▸ done


-- box-perm-2341 @03102132: 4 steps
lem-box-perm-2341-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-2341-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-2410 ∷ []) (lem-pairs-at032032 c4) ▸
       at 0 1 (Bx3-2140 ∷ []) (lem-sym-bc-at0312243140 c4) ▸
       at 0 1 (Bx3-1240 ∷ []) (lem-sym-ab-at0312213440 c4) ▸ done


-- cQ @033440: 7 steps
lem-cQ-at033440 : Complete 4 → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at033440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @033440: 13 steps
lem-box-tQ-at033440 : Complete 4 → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at033440 c4) ▸
       at 2 4 (Toff312 ∷ []) (lw4 c4 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸ done


-- sym-ab @033440: 18 steps
lem-sym-ab-at033440 : Complete 4 → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-sym-ab-at033440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-20 ∷ []) (refl) ▸
       at 7 1 (Bx3-20 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ [])
  b1 = at 2 6 (Bx2-340 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-20 ∷ []) (refl) ▸
       at 10 1 (Bx3-20 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (Bx3-2140 ∷ [])
  b2 = at 5 6 (Bx2-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- cQ @0312213440: 7 steps
lem-cQ-at0312213440 : Complete 4 → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0312213440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (pw2 c4 (CS13⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0312213440: 13 steps
lem-box-tQ-at0312213440 : Complete 4 → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0312213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2140 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0312213440 c4) ▸
       at 2 4 (Toff312 ∷ []) (lw4 c4 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @0312213440: 17 steps
lem-CXbc-box-at0312213440 : Complete 4 → ⟪ (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX14 ∷ CCZ013 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CCZ034 ∷ CX21 ∷ CS02 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0312213440 c4) ▸
       at 0 2 (Toff312 ∷ CX14 ∷ []) (lw0 c4 (CX14 ∷ Toff312 ∷ []) (Toff312 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (pw2 c4 (CX14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CX14 ∷ []) (lw0 c4 (CX14 ∷ Toff312 ∷ []) (Toff312 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX14 ∷ CCZ013 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CCZ034 ∷ CX21 ∷ CS02 ∷ CX14 ∷ []) (Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS01⁻ ∷ []) (pw2 c4 (CS01⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (pw2 c4 (CX14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX14 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-2140 ∷ []) (sym (lem-box-tQ-at0312213440 c4)) ▸ done

  b2 : Chain (Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-2140 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ CX14 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0312213440: 18 steps
lem-CXcb-box-at0312213440 : Complete 4 → ⟪ (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) (Toff312 ∷ CCZ034 ∷ CX41 ∷ Toff324 ∷ CS04 ∷ CX24 ∷ Toff312 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ CCZ034 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0312213440 c4) ▸
       at 0 2 (Toff312 ∷ CX41 ∷ Toff324 ∷ []) (lw0 c4 (CX41 ∷ Toff312 ∷ []) (Toff312 ∷ CX41 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (pw1 c4 (Toff324 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff312 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX24 ∷ []) (lw0 c4 (CX24 ∷ Toff312 ∷ []) (Toff312 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX41 ∷ Toff324 ∷ CS04 ∷ CX24 ∷ Toff312 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ CCZ034 ∷ CX41 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX24 ∷ []) (lw0 c4 (CX24 ∷ Toff312 ∷ []) (Toff312 ∷ CX24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 c4) ▸
       at 5 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ CX41 ∷ Toff324 ∷ []) (lw0 c4 (CX41 ∷ Toff312 ∷ []) (Toff312 ∷ CX41 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX41 ∷ []) (lw0 c4 (CX41 ∷ Toff324 ∷ Toff324 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-2140 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-2140 ∷ []) (sym (lem-box-tQ-at0312213440 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ CX41 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0312213440: 11 steps
lem-SWbc-box-at0312213440 : Complete 4 → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-SWbc-box-at0312213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (CX14 ∷ Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX14 ∷ CX41 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX14 ∷ CX41 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-2140 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0312213440 c4) ▸
       at 4 2 (CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX14 ∷ Bx3-2140 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (Bx3-2140 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-2140 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312213440 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0312213440: 23 steps
lem-nat-SWbc-at0312213440 : Complete 4 → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ Sw14 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸
       at 5 2 (Toff213 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ Sw14 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Sw14 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸
       at 8 2 (Toff324 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff213 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Sw14 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Sw14 ∷ []) (Bx3-2410 ∷ [])
  b2 = at 13 2 (Toff213 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-310 ∷ []) (refl) ▸
       at 5 6 (Bx2-310 ∷ []) (refl) ▸
       at 0 6 (Bx3-2410 ∷ []) (refl) ▸ done


-- sym-bc @0312213440: 2 steps
lem-sym-bc-at0312213440 : Complete 4 → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-sym-bc-at0312213440 c4 = run b0
  where
  b0 : Chain (Bx3-2140 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0312213440 c4)) ▸
       at 0 3 (Bx3-2410 ∷ []) (lem-nat-SWbc-at0312213440 c4) ▸ done

