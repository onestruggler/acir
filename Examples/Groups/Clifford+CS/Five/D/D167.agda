{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D167 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0244 ; wl0265 ; wl0351 ; wl0503 ; wl0616 ; wl0618 ; wl0619 ; wl0620 ; wl0622 ; wl0627 ; wl0628 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-T312-beta-at14213243 ; lem-sym12 ; lem-sym12-at1221 ; lem-sym12-at14213243 ; lem-sym23-at1221 ; lem-sym23-at14213243 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta-at122331 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 ; lem-sym12-at243243 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331 ; lem-sym23-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-beta-T-at01122330)
open import Examples.Groups.Clifford+CS.Five.D.D161 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D164 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 ; lem-auto-CCZ012-∣-CCZ342-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.D166 using (lem-T312-beta-at122441 ; lem-T312-beta-at14233142 ; lem-T312-beta-at14233241 ; lem-T312-beta-at1441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 ; lem-beta-inv-at122441 ; lem-boxify-9-nf-of-rhs ; lem-sym12-at122441 ; lem-sym12-at1441 ; lem-sym23-at14233241 ; lem-sym23-at143143 ; lem-sym23-at1441 ; lem-sym34-at14233142 ; lem-sym34-at14233241 ; lem-sym34-at143143 ; lem-sym34-at1441)
-- boxify-9: 331 steps
lem-boxify-9 : Ws → ⟪ (Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-boxify-9 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (run b41)))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 11 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 18 1 (CS13 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b1 = at 20 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 18 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 18 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 18 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 17 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 17 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 17 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-4231 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b2 = at 17 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 17 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 18 2 (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4) ▸
       at 19 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 21 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 21 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 21 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 20 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-4231 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-4213 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b3 = at 20 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 20 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 20 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 20 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 21 2 (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4) ▸
       at 22 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 24 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 24 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-4213 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4123 ∷ Toff234 ∷ Toff324 ∷ [])
  b4 = at 24 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 23 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 23 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 23 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 23 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 23 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 24 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0620 (lit c4))) ▸
       at 26 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸ done

  b5 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4123 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-1423 ∷ CCZ134 ∷ Toff324 ∷ [])
  b5 = at 26 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 26 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 26 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 25 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 25 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 25 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 25 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 25 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸ done

  b6 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-1423 ∷ CCZ134 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ [])
  b6 = at 25 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4) ▸
       at 26 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 28 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 28 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 28 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 27 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 27 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 27 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸ done

  b7 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b7 = at 27 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 27 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 7 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 9 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 9 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 9 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 8 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 8 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸ done

  b8 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b8 = at 8 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 8 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 8 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 9 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 10 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 12 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 12 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 12 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸ done

  b9 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b9 = at 11 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 11 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 11 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 11 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 11 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 12 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸
       at 13 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 15 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b10 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b10 = at 15 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 15 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 14 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 14 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 14 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 14 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 14 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸
       at 15 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸ done

  b11 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b11 = at 16 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 18 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 16 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 16 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 17 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0620 (lit c4))) ▸
       at 19 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 19 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 18 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸ done

  b12 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b12 = at 18 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 18 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 18 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 19 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 20 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 22 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 20 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 20 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸ done

  b13 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b13 = at 21 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 22 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 24 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 22 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 22 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 23 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 24 2 (CS13 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 c4) ▸
       at 25 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸ done

  b14 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b14 = at 26 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 28 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 26 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 26 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 27 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 28 2 (CS13⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 c4) ▸
       at 29 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 30 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸ done

  b15 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b15 = at 32 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 30 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 30 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 31 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 32 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0620 (lit c4))) ▸
       at 34 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 34 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 33 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸ done

  b16 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b16 = at 33 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 33 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 33 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 34 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 35 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 36 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 38 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 36 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b17 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b17 = at 36 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 37 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 0 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 2 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 2 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 1 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 1 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸ done

  b18 : Chain (Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b18 = at 1 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 2 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 3 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 5 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 5 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 5 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸ done

  b19 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b19 = at 4 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 4 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 4 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 4 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 5 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸
       at 6 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b20 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b20 = at 8 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 8 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 7 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 7 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 7 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 7 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 7 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸
       at 8 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 c4) ▸ done

  b21 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b21 = at 9 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 11 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 11 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 11 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 10 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 10 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 10 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 10 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸ done

  b22 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Bx0-4312 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b22 = at 10 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 11 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 12 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 13 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 15 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 15 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 15 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 14 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸ done

  b23 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Bx0-4312 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b23 = at 14 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 14 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 14 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 14 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 15 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 16 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸
       at 17 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 19 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b24 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b24 = at 19 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 19 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 18 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 18 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 18 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 18 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 18 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸
       at 19 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸ done

  b25 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4231 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b25 = at 20 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 21 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 23 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 21 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 21 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 22 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 23 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0620 (lit c4))) ▸
       at 25 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b26 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4231 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b26 = at 25 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 24 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 24 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 24 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 24 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 25 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 26 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 27 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸ done

  b27 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b27 = at 29 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 27 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 27 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 28 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 29 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 30 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 32 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 30 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b28 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b28 = at 30 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 31 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 32 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 33 2 (CS13 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 c4) ▸
       at 34 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 35 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 37 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 35 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b29 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b29 = at 35 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 36 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 37 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 38 2 (CS13⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 c4) ▸
       at 39 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 40 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 42 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 40 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b30 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4231 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b30 = at 40 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 41 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 42 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 43 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0620 (lit c4))) ▸
       at 45 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 45 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 44 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 44 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸ done

  b31 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4231 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b31 = at 44 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 44 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 45 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 46 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 47 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 48 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 50 1 (Toff324 ∷ []) (wl0622 (lit c4)) ▸
       at 48 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b32 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b32 = at 48 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 49 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 50 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 51 2 [] (lem-beta-inv-at122441 c4) ▸
       at 51 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 51 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 46 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 45 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸ done

  b33 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b33 = at 44 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 42 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸
       at 44 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 43 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 41 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸
       at 43 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 42 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 40 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸ done

  b34 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b34 = at 42 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 41 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 28 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 27 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 27 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 26 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸ done

  b35 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b35 = at 26 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 22 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 26 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸ done

  b36 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b36 = at 21 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 19 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 21 2 (Toff234 ∷ CCZ134 ∷ []) (wl0631 (lit c4)) ▸ done

  b37 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b37 = at 22 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 20 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸ done

  b38 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b38 = at 22 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 18 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 20 2 (Toff234 ∷ CCZ134 ∷ []) (wl0631 (lit c4)) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 19 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0629 (lit c4)) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸ done

  b39 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b39 = at 23 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0628 (lit c4)) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 20 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ []) (wl0630 (lit c4)) ▸
       at 8 2 (Toff134 ∷ CCZ234 ∷ []) (wl0632 (lit c4)) ▸
       at 7 2 (Toff134 ∷ CZ34 ∷ CCZ134 ∷ []) (wl0633 (lit c4)) ▸
       at 65 2 [] (wl0351 (lit c4)) ▸
       at 66 3 (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl0634 (lit c4)) ▸ done

  b40 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b40 = at 65 2 [] (wl0503 (lit c4)) ▸
       at 65 2 [] (wl0351 (lit c4)) ▸
       at 65 2 [] (wl0351 (lit c4)) ▸
       at 66 2 (CCZ134 ∷ CCZ124 ∷ []) (wl0635 (lit c4)) ▸
       at 65 2 [] (wl0503 (lit c4)) ▸
       at 65 2 [] (wl0351 (lit c4)) ▸
       at 66 2 (CCZ134 ∷ CCZ124 ∷ []) (wl0635 (lit c4)) ▸
       at 65 2 [] (wl0503 (lit c4)) ▸ done

  b41 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ [])
  b41 = at 66 2 [] (wl0351 (lit c4)) ▸
       at 0 67 [] (wl0636 (lit c4)) ▸
       at 0 1 (Bx0-1234 ∷ []) (sym (lem-boxify-9-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | BOX(1;2034): 25 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·2034⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-2034 ∷ []) (Toff123 ∷ Bx0-1234 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 1 1 (Toff123 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (lem-beta-T-at01122330 c4) ▸
       at 0 0 (Toff123 ∷ Toff123 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 1 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (Toff123 ∷ Bx0-1234 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ CCZ014 ∷ []) (Toff123 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ Bx0-1234 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b1 = at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 2 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4) ▸
       at 3 0 (Toff123 ∷ Toff123 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 4 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b2 : Chain (Toff123 ∷ CCZ234 ∷ CCZ014 ∷ Toff123 ∷ Bx0-1234 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx1-2304 ∷ Bx0-1234 ∷ [])
  b2 = at 4 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸
       at 5 2 (CCZ014 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ104 c4) ▸
       at 0 2 (CCZ234 ∷ Toff123 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ Toff123 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110243243 c4) ▸
       at 1 2 (CCZ234 ∷ Toff123 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 0 2 [] (wl0265 (lit c4)) ▸
       at 0 4 (Bx1-2304 ∷ []) (sym (lem-beta-T-at01122330 c4)) ▸ done

  b3 : Chain (Bx1-2304 ∷ Bx0-1234 ∷ []) (Bx1-2034 ∷ Bx0-1234 ∷ [])
  b3 = at 0 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸ done


-- boxify-10 [nf of rhs]: 0 steps
lem-boxify-10-nf-of-rhs : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-boxify-10-nf-of-rhs c4 = refl
