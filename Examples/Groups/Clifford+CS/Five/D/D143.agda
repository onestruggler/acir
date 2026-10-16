{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D143 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym12)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta ; lem-beta-inv-at0310243142 ; lem-sym12-at1221 ; lem-sym23-at1221 ; lem-sym34-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-T312-beta-at122331 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234 ; lem-sym12-at0110 ; lem-sym12-at011220 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331 ; lem-sym34-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-TW ; lem-sym12-at03102132 ; lem-sym23-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-beta-T-at0330 ; lem-sym23-at0310213442 ; lem-sym23-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-beta-T-at01122330 ; lem-sym12-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-sym12-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym23-at0213243041 ; lem-sym34-at0213203441)
open import Examples.Groups.Clifford+CS.Five.D.D142 using (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ ; lem-auto-BOX⟨0·1234⟩-∣-CCZ104 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ304 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 ; lem-auto-CCZ012-∣-CCZ342-at2332)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF103 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨3·1024⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-BOX⟨3·0412⟩ ; lem-nat-1-BOX⟨3·1402⟩ ; lem-nat-2-BOX⟨3·2401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-3-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-3-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-1-BOX⟨3·1042⟩ ; lem-nat-2-BOX⟨2·1043⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-BOX⟨3·0124⟩ ; lem-nat-0-BOX⟨3·0142⟩ ; lem-nat-0-BOX⟨3·1042⟩ ; lem-nat-1-BOX⟨3·1024⟩ ; lem-nat-1-BOX⟨3·2014⟩ ; lem-nat-1-BOX⟨3·2041⟩ ; lem-nat-1-BOX⟨3·2401⟩ ; lem-nat-2-BOX⟨2·3401⟩)
-- auto CCZ012 | CCZ342 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at243243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0110243243: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0110243243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0110243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234): 27 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-0234 ∷ []) (Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4) ▸
       at 0 0 (Toff123 ∷ Toff123 ∷ []) (lw4 c4 [] (Toff123 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 1 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸ done

  b1 : Chain (Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (Toff123 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 2 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4) ▸
       at 3 0 (Toff123 ∷ Toff123 ∷ []) (lw4 c4 [] (Toff123 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 4 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸ done

  b2 : Chain (Toff123 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ Bx0-2134 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ Bx0-1234 ∷ [])
  b2 = at 4 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 5 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4) ▸
       at 0 2 (CCZ234 ∷ Toff123 ∷ []) (lw0 c4 (Toff123 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Toff123 ∷ []) (lw0 c4 (Toff123 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4) ▸
       at 1 2 (CCZ234 ∷ Toff123 ∷ []) (lw0 c4 (Toff123 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff123 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done

  b3 : Chain (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ [])
  b3 = at 0 4 (Bx1-2304 ∷ []) (sym (lem-beta-T-at01122330 c4)) ▸
       at 0 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸ done


-- boxify-4 [nf of rhs]: 0 steps
lem-boxify-4-nf-of-rhs : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-4-nf-of-rhs c4 = refl

-- sym34 @031031: 5 steps
lem-sym34-at031031 : Complete 4 → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym34-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0310213442: 5 steps
lem-sym12-at0310213442 : Complete 4 → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym12-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ c4) ▸
       at 1 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1043⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @03103441: 5 steps
lem-sym12-at03103441 : Complete 4 → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym12-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym12-at0310213442 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @03203442: 5 steps
lem-sym23-at03203442 : Complete 4 → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym23-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0312203441: 5 steps
lem-sym23-at0312203441 : Complete 4 → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym23-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ c4) ▸
       at 1 1 (Bx3-1402 ∷ []) (lem-sym23-at03203442 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @2332: 8 steps
lem-TW-at2332 : Complete 4 → ⟪ (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Bx1-0324 ∷ []) ⟫ʷ
lem-TW-at2332 c4 = run b0
  where
  b0 : Chain (Toff103 ∷ Bx0-1324 ∷ Toff103 ∷ []) (Bx0-1324 ∷ Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 1 3 (Bx0-1234 ∷ Bx1-0234 ∷ []) (lem-TW c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @243243: 8 steps
lem-TW-at243243 : Complete 4 → ⟪ (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-TW-at243243 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx0-1423 ∷ Toff104 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 1 3 (Bx0-1324 ∷ Bx1-0324 ∷ []) (lem-TW-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0110243243: 8 steps
lem-TW-at0110243243 : Complete 4 → ⟪ (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-TW-at0110243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx1-0423 ∷ Toff014 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 3 (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-TW-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0210243143: 8 steps
lem-TW-at0210243143 : Complete 4 → ⟪ (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-TW-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx2-0413 ∷ Toff024 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 1 3 (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-TW-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0310243142: 8 steps
lem-TW-at0310243142 : Complete 4 → ⟪ (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-TW-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx3-0412 ∷ Toff034 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 1 3 (Bx2-0413 ∷ Bx0-2413 ∷ []) (lem-TW-at0210243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @03243042: 8 steps
lem-TW-at03243042 : Complete 4 → ⟪ (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ
lem-TW-at03243042 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ Bx3-1402 ∷ Toff134 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 1 3 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-TW-at0310243142 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0312243041: 8 steps
lem-TW-at0312243041 : Complete 4 → ⟪ (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-TW-at0312243041 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx3-2401 ∷ Toff234 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-1402 ∷ Bx1-3402 ∷ []) (lem-TW-at03243042 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @03243042: 5 steps
lem-sym23-at03243042 : Complete 4 → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym23-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 0 2 (Bx3-1042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0142⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0312243041: 5 steps
lem-sym23-at0312243041 : Complete 4 → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym23-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 1 (Bx3-1042 ∷ []) (lem-sym23-at03243042 c4) ▸
       at 0 2 (Bx3-2041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1042⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03203442: 5 steps
lem-sym34-at03203442 : Complete 4 → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym34-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1042⟩ c4) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸
       at 0 2 (Bx3-1024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0312203441: 5 steps
lem-sym34-at0312203441 : Complete 4 → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym34-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2041⟩ c4) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-sym34-at03203442 c4) ▸
       at 0 2 (Bx3-2014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1024⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @032032: 5 steps
lem-sym12-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym12-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @03122031: 5 steps
lem-sym12-at03122031 : Complete 4 → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym12-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2014⟩ c4) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym12-at032032 c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @031031: 5 steps
lem-sym23-at031031 : Complete 4 → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym23-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ c4) ▸
       at 1 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩ c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at0110 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;0412) @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 2 2 (Bx3-2401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Bx3-2401 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at021021 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @12243143: 8 steps
lem-TW-at12243143 : Complete 4 → ⟪ (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-TW-at12243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx0-2413 ∷ Toff204 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 1 3 (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-TW-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @13243142: 8 steps
lem-TW-at13243142 : Complete 4 → ⟪ (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-TW-at13243142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx0-3412 ∷ Toff304 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 1 3 (Bx0-2413 ∷ Bx2-0413 ∷ []) (lem-TW-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0113243042: 8 steps
lem-TW-at0113243042 : Complete 4 → ⟪ (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ
lem-TW-at0113243042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx1-3402 ∷ Toff314 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 1 3 (Bx0-3412 ∷ Bx3-0412 ∷ []) (lem-TW-at13243142 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW @0213243041: 8 steps
lem-TW-at0213243041 : Complete 4 → ⟪ (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-TW-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx1-3402 ∷ Bx3-1402 ∷ []) (lem-TW-at0113243042 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @12243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @13243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ Bx0-2413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at12243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0113243042: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 : Complete 4 → ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 c4 = run b0
  where
  b0 : Chain (Bx1-3402 ∷ Bx3-1402 ∷ []) (Bx3-1402 ∷ Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at13243142 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0213243041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 : Complete 4 → ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Bx1-3402 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0113243042 c4) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0110243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0210243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @03243042: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 : Complete 4 → ⟪ (Bx3-1402 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Bx3-1402 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 2 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Bx0-3412 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0310243142 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0234) @0312243041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 : Complete 4 → ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 2 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Bx1-3402 ∷ Bx3-1402 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at03243042 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @03243042: 5 steps
lem-beta-inv-at03243042 : Complete 4 → ⟪ (Bx3-1402 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ Bx3-1402 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at0310243142 c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @0312243041: 5 steps
lem-beta-inv-at0312243041 : Complete 4 → ⟪ (Bx3-2401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ Bx3-2401 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 2 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at03243042 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- boxify-4: 31 steps
lem-boxify-4 : Complete 4 → ⟪ (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-boxify-4 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Toff324 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-2401 ∷ Bx2-3401 ∷ Toff324 ∷ [])
  b0 = at 2 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff234 ∷ []) (lw0 c4 (Toff234 ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff234 ∷ []) (lw0 c4 (Toff234 ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 4 1 (Bx3-0241 ∷ []) (lem-sym34-at031031 c4) ▸
       at 4 1 (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4) ▸
       at 4 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸
       at 3 3 (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-TW-at0312243041 c4) ▸ done

  b1 : Chain (Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-2401 ∷ Bx2-3401 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ Bx3-0124 ∷ [])
  b1 = at 3 1 (Bx3-2041 ∷ []) (lem-sym23-at0312243041 c4) ▸
       at 3 1 (Bx3-2014 ∷ []) (lem-sym34-at0312203441 c4) ▸
       at 3 1 (Bx3-0214 ∷ []) (lem-sym12-at03122031 c4) ▸
       at 3 1 (Bx3-0124 ∷ []) (lem-sym23-at031031 c4) ▸
       at 3 2 (Bx2-3401 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·0412⟩-at03102132 c4) ▸
       at 4 2 (Toff324 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF043-at03102132 c4) ▸
       at 3 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx2-3401 ∷ Toff324 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Bx2-3401 ∷ Bx3-2401 ∷ Bx3-2401 ∷ [])
  b2 = at 6 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-TW-at0213243041 c4) ▸
       at 4 2 (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0213243041 c4) ▸
       at 4 2 (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0234⟩-at0312243041 c4) ▸
       at 6 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 6 1 (Bx3-0241 ∷ []) (lem-sym34-at031031 c4) ▸
       at 6 1 (Bx3-2041 ∷ []) (lem-sym12-at03103441 c4) ▸
       at 6 1 (Bx3-2401 ∷ []) (lem-sym23-at0312203441 c4) ▸ done

  b3 : Chain (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ Bx2-3401 ∷ Bx3-2401 ∷ Bx3-2401 ∷ []) (Bx2-0134 ∷ [])
  b3 = at 5 2 [] (lem-beta-inv-at0312243041 c4) ▸
       at 4 1 (Bx2-3041 ∷ []) (lem-sym23-at0213243041 c4) ▸
       at 4 1 (Bx2-3014 ∷ []) (lem-sym34-at0213203441 c4) ▸
       at 4 1 (Bx2-0314 ∷ []) (lem-sym12-at02132031 c4) ▸
       at 4 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 4 [] (lw0 c4 (Toff324 ∷ Toff234 ∷ Toff234 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (Bx2-0134 ∷ []) (sym (lem-boxify-4-nf-of-rhs c4)) ▸ done


-- auto CCZ012 | CCZ342 @0210243143: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0210243143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @0310243142: 7 steps
lem-auto-CCZ012-∣-CCZ342-at0310243142 : Complete 4 → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0210243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(3;1204): 15 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨3·1204⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Bx3-1204 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ Bx0-1234 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at0330 c4) ▸
       at 0 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸
       at 2 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4) ▸
       at 3 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 4 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ Bx0-1234 ∷ CCZ034 ∷ []) (Bx3-1204 ∷ Bx0-1234 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ304 c4) ▸
       at 0 2 (CCZ124 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0310243142 c4) ▸
       at 1 2 (CCZ124 ∷ Toff312 ∷ []) (lw0 c4 (Toff312 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-beta-T-at0330 c4)) ▸ done


-- boxify-5 [nf of rhs]: 0 steps
lem-boxify-5-nf-of-rhs : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-5-nf-of-rhs c4 = refl
