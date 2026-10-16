{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D150 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-inv)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-inv-at243243 ; lem-sym34-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym34-at0310213442 ; lem-sym34-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 ; lem-sym12-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D139 using (lem-T312-beta-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D143 using (lem-TW-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 ; lem-sym12-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D149 using (lem-TW-at132132 ; lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩ ; lem-auto-BOX⟨0·1234⟩-∣-CCZ042 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF021 ; lem-auto-CCZ012-∣-TOFF342)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨3·0214⟩ ; lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-0-BOX⟨3·1204⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134 ; lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·3124⟩ ; lem-nat-0-BOX⟨1·3024⟩ ; lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·3014⟩ ; lem-nat-0-BOX⟨2·3104⟩ ; lem-nat-1-BOX⟨1·3024⟩ ; lem-nat-1-BOX⟨2·3014⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-0-BOX⟨2·3401⟩ ; lem-nat-0-BOX⟨2·3410⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-1-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-1-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-1-BOX⟨3·1042⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-BOX⟨0·3421⟩ ; lem-nat-0-BOX⟨1·3420⟩ ; lem-nat-0-BOX⟨3·0124⟩ ; lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-0-BOX⟨3·2014⟩ ; lem-nat-0-BOX⟨3·2104⟩ ; lem-nat-1-BOX⟨0·3412⟩ ; lem-nat-1-BOX⟨0·3421⟩ ; lem-nat-1-BOX⟨1·3420⟩ ; lem-nat-1-BOX⟨2·3410⟩ ; lem-nat-1-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨3·1204⟩ ; lem-nat-1-BOX⟨3·2014⟩ ; lem-nat-1-BOX⟨3·2041⟩ ; lem-nat-1-BOX⟨3·2104⟩)
-- TW @01132032: 8 steps
lem-TW-at01132032 : Complete 4 → ⟪ (Toff301 ∷ Bx1-3024 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-TW-at01132032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx1-3024 ∷ Toff301 ∷ []) (Bx1-3024 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3024⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-TW-at132132 c4) ▸
       at 0 2 (Bx1-3024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @02132031: 8 steps
lem-TW-at02132031 : Complete 4 → ⟪ (Toff302 ∷ Bx2-3014 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-TW-at02132031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx2-3014 ∷ Toff302 ∷ []) (Bx2-3014 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-3024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3014⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 1 3 (Bx1-3024 ∷ Bx3-1024 ∷ []) (lem-TW-at01132032 c4) ▸
       at 0 2 (Bx2-3014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3024⟩ c4) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @02132130: 8 steps
lem-TW-at02132130 : Complete 4 → ⟪ (Toff312 ∷ Bx2-3104 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-TW-at02132130 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx2-3104 ∷ Toff312 ∷ []) (Bx2-3104 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-3014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3104⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-3014 ∷ Bx3-2014 ∷ []) (lem-TW-at02132031 c4) ▸
       at 0 2 (Bx2-3104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3014⟩ c4) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0220: 5 steps
lem-sym12-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym12-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0214) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx3-1204 ∷ []) (Bx3-1204 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (Bx3-0214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1204⟩ c4) ▸
       at 1 2 (Bx3-0214 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩ c4) ▸
       at 0 2 (Bx3-1204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0214) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx3-2104 ∷ []) (Bx3-2104 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (Bx3-1204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2104⟩ c4) ▸
       at 1 2 (Bx3-1204 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0214⟩-at0110 c4) ▸
       at 0 2 (Bx3-2104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1204⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @12243143: 8 steps
lem-T312-beta-at12243143 : Complete 4 → ⟪ (Toff124 ∷ Bx0-2413 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at12243143 c4 = run b0
  where
  b0 : Chain (Toff124 ∷ Bx0-2413 ∷ Toff124 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @13243142: 8 steps
lem-T312-beta-at13243142 : Complete 4 → ⟪ (Toff134 ∷ Bx0-3412 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at13243142 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ Bx0-3412 ∷ Toff134 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 1 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-T312-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0113243042: 8 steps
lem-T312-beta-at0113243042 : Complete 4 → ⟪ (Toff034 ∷ Bx1-3402 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at0113243042 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx1-3402 ∷ Toff034 ∷ []) (Bx1-3402 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 1 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-T312-beta-at13243142 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0213243041: 8 steps
lem-T312-beta-at0213243041 : Complete 4 → ⟪ (Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx2-3401 ∷ Toff034 ∷ []) (Bx2-3401 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 1 3 (Bx1-3402 ∷ CCZ234 ∷ []) (lem-T312-beta-at0113243042 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @032032: 5 steps
lem-sym34-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym34-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03122031: 5 steps
lem-sym34-at03122031 : Complete 4 → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym34-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym34-at032032 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @03203442: 5 steps
lem-sym12-at03203442 : Complete 4 → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym12-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ c4) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym12-at0310213442 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0312203441: 5 steps
lem-sym12-at0312203441 : Complete 4 → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym12-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym12-at03203442 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0310243241: 8 steps
lem-TW-at0310243241 : Complete 4 → ⟪ (Toff034 ∷ Bx3-0421 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-TW-at0310243241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx3-0421 ∷ Toff034 ∷ []) (Bx3-0421 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 1 3 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-TW-at0310243142 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03103441: 5 steps
lem-sym34-at03103441 : Complete 4 → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym34-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @032032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ Bx2-3410 ∷ []) (Bx2-3410 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 2 2 (Bx2-3401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3410⟩ c4) ▸
       at 1 2 (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4) ▸
       at 0 2 (Bx2-3410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @03122031: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122031 : Complete 4 → ⟪ (Bx3-2014 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ Bx1-3420 ∷ []) (Bx1-3420 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 2 2 (Bx2-3410 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3420⟩ c4) ▸
       at 1 2 (Bx2-3410 ∷ Bx3-1024 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at032032 c4) ▸
       at 0 2 (Bx1-3420 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3410⟩ c4) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @03122130: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 : Complete 4 → ⟪ (Bx3-2104 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ Bx0-3421 ∷ []) (Bx0-3421 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ c4) ▸
       at 2 2 (Bx1-3420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3421⟩ c4) ▸
       at 1 2 (Bx1-3420 ∷ Bx3-2014 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03122031 c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3420⟩ c4) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ042 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ024 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ042 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at0110 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ042 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at021021 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ042 @032032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03102132 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ042 @03122031: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122031 : Complete 4 → ⟪ (Bx3-2014 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ Bx3-1024 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at032032 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ042 @03122130: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 : Complete 4 → ⟪ (Bx3-2104 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (CCZ034 ∷ Bx3-2014 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ042-at03122031 c4) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at12243143 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at13243142 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF021 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Toff102 ∷ []) (Toff102 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021 c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF021 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Toff201 ∷ []) (Toff201 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at0110 c4) ▸
       at 0 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF021 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Toff301 ∷ []) (Toff301 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 1 2 (Toff201 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at021021 c4) ▸
       at 0 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF021 @032032: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ Toff301 ∷ []) (Toff301 ∷ Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 2 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF021 @03122031: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122031 : Complete 4 → ⟪ (Bx3-2014 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Bx3-2014 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ Toff302 ∷ []) (Toff302 ∷ Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 2 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 1 2 (Toff301 ∷ Bx3-1024 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at032032 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 1 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF021 @03122130: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 : Complete 4 → ⟪ (Bx3-2104 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ Toff312 ∷ []) (Toff312 ∷ Bx3-2104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ c4) ▸
       at 2 2 (Toff302 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Bx3-2014 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF021-at03122031 c4) ▸
       at 0 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2014⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @13243241: 5 steps
lem-sym23-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym23-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @133441: 5 steps
lem-sym34-at133441 : Complete 4 → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym34-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 0 2 (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @133441: 5 steps
lem-sym23-at133441 : Complete 4 → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym23-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4) ▸
       at 1 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at12243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at13243142 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012 @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ Toff024 ∷ []) (Toff024 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 2 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 1 2 (Toff014 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012 @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 2 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 1 2 (Toff024 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at12243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012 @13243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Bx0-3421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ Toff034 ∷ []) (Toff034 ∷ Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 1 2 (Toff034 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 1 2 (Bx0-3421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @12243143: 5 steps
lem-beta-inv-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ Bx0-2413 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @13243142: 5 steps
lem-beta-inv-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ Bx0-3412 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at12243143 c4) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @13243241: 5 steps
lem-beta-inv-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ Bx0-3421 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at13243142 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @0110: 5 steps
lem-beta-inv-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx1-0234 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 2 [] (lem-beta-inv c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @021021: 5 steps
lem-beta-inv-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx2-0134 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at0110 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @03102132: 5 steps
lem-beta-inv-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Bx3-0124 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at021021 c4) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @032032: 5 steps
lem-beta-inv-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ Bx3-1024 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 2 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at03102132 c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @03122031: 5 steps
lem-beta-inv-at03122031 : Complete 4 → ⟪ (Bx3-2014 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ Bx3-2014 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 2 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at032032 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @03122130: 5 steps
lem-beta-inv-at03122130 : Complete 4 → ⟪ (Bx3-2104 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ Bx3-2104 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ c4) ▸
       at 2 2 (Bx3-2014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·2104⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at03122031 c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @2332: 7 steps
lem-auto-CCZ012-∣-TOFF342-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF342 c4) ▸
       at 0 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @243243: 7 steps
lem-auto-CCZ012-∣-TOFF342-at243243 : Complete 4 → ⟪ (CCZ014 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at2332 c4) ▸
       at 0 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @0110243243: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0110243243 : Complete 4 → ⟪ (CCZ014 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0110243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 1 2 (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at243243 c4) ▸
       at 0 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @0210243143: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0210243143 : Complete 4 → ⟪ (CCZ024 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0110243243 c4) ▸
       at 0 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @02243043: 7 steps
lem-auto-CCZ012-∣-TOFF342-at02243043 : Complete 4 → ⟪ (CCZ124 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at02243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 1 2 (Toff134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at0210243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @12243143: 7 steps
lem-auto-CCZ012-∣-TOFF342-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at243243 c4) ▸
       at 0 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF342 @0112243043: 7 steps
lem-auto-CCZ012-∣-TOFF342-at0112243043 : Complete 4 → ⟪ (CCZ124 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF342-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 1 2 (Toff134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF342-at12243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

