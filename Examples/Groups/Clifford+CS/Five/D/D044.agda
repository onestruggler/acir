{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D044 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0019 ; wl0022 ; wl0024 ; wl0025 ; wl0043 ; wl0046 ; wl0061 ; wl0121 ; wl0132 ; wl0133 ; wl0478 ; wl0479 ; wl0480 ; wl0481 ; wl0482 ; wl0483 ; wl0484 ; wl0485)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-CS01-∣-BOX⟨1·2340⟩ ; lem-auto-CSd01-∣-BOX⟨1·2340⟩ ; lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ ; lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F1-CS-K0-rhs-shape-part0)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-F1-CS-K0-rhs-shape-part1)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-F1-CS-K0-rhs-shape-part2)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-F1-CS-K0-rhs-shape-part3)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-F1-CS-K0-rhs-shape-part4)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-F1-CS-K0-rhs-shape-part5)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-F1-CS-K0-rhs-shape-part6)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-F1-CS-K0-rhs-shape-part7)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F1-CS-K0-rhs-shape-part8)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-F1-CS-K0-rhs-shape-part9)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-F1-CS-K0-rhs-shape-part10)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-F1-CS-K0-rhs-shape-part11)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F1-CS-K0-rhs-shape-part12)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F1-CS-K0-rhs-shape-part13)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F1-CS-K0-rhs-shape-part14)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-F1-CS-K0-rhs-shape-part15)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F1-CS-K0-rhs-shape-part16)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F1-CS-K0-rhs-shape-part17)
open import Examples.Groups.Clifford+CS.Five.D.D024 using (lem-F1-CS-K0-rhs-shape-part18)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F1-CS-K0-rhs-shape-part19)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-CS-K0-rhs-shape-part20)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-CS-K0-rhs-shape-part21)
open import Examples.Groups.Clifford+CS.Five.D.D028 using (lem-F1-CS-K0-rhs-shape-part22)
open import Examples.Groups.Clifford+CS.Five.D.D029 using (lem-F1-CS-K0-rhs-shape-part23)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-F1-CS-K0-rhs-shape-part24)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-F1-CS-K0-rhs-shape-part25)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F1-CS-K0-rhs-shape-part26)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-F1-CS-K0-rhs-shape-part27)
open import Examples.Groups.Clifford+CS.Five.D.D034 using (lem-F1-CS-K0-rhs-shape-part28)
open import Examples.Groups.Clifford+CS.Five.D.D035 using (lem-F1-CS-K0-rhs-shape-part29)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-F1-CS-K0-rhs-shape-part30)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-F1-CS-K0-rhs-shape-part31)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-CS-K0-rhs-shape-part32)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-F1-CS-K0-rhs-shape-part33)
open import Examples.Groups.Clifford+CS.Five.D.D040 using (lem-F1-CS-K0-rhs-shape-part34)
open import Examples.Groups.Clifford+CS.Five.D.D041 using (lem-F1-CS-K0-rhs-shape-part35)
open import Examples.Groups.Clifford+CS.Five.D.D042 using (lem-F1-CS-K0-rhs-shape-part36)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-F1-CS-K0-rhs-shape-part37)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·2431⟩ ; lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩ ; lem-nat-3-BOX⟨1·2340⟩ ; lem-nat-3-BOX⟨1·2430⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-SBOX⟨0·2·13·4⟩ ; lem-nat-0-SBOX⟨1·2·03·4⟩ ; lem-nat-1-SBOX⟨0·1·23·4⟩ ; lem-nat-1-SBOX⟨0·2·13·4⟩)
-- F1 CS-K0 [rhs shape]: 38 steps
lem-F1-CS-K0-rhs-shape : Ws → ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 5 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ X1 ∷ K2 ∷ CCZ024 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part0 c4) ▸
       at 0 66 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ X1 ∷ CX41 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part1 c4) ▸
       at 0 64 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part2 c4) ▸
       at 0 64 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ K2 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ K2⁻ ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ X1 ∷ Toff204 ∷ X1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part3 c4) ▸
       at 0 109 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ K3 ∷ X1 ∷ CZ13 ∷ K3⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part4 c4) ▸
       at 0 94 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part5 c4) ▸
       at 0 78 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part6 c4) ▸
       at 0 82 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part7 c4) ▸ done

  b1 : Chain (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS12 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ CCZ034 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b1 = at 0 86 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part8 c4) ▸
       at 0 91 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part9 c4) ▸
       at 0 79 (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1⁻ ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part10 c4) ▸
       at 0 75 (CS04 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part11 c4) ▸
       at 0 82 (CS04 ∷ S1 ∷ CS14⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ X1 ∷ CS03 ∷ Sb2-0-41-3 ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part12 c4) ▸
       at 0 64 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part13 c4) ▸
       at 0 72 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Bx2-0431 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part14 c4) ▸
       at 0 82 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ CCZ034 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part15 c4) ▸ done

  b2 : Chain (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ CCZ034 ∷ X1 ∷ CCZ034 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b2 = at 0 66 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ ι ∷ S1⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part16 c4) ▸
       at 0 78 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part17 c4) ▸
       at 0 60 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part18 c4) ▸
       at 0 82 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ K3 ∷ X1 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ X1 ∷ CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part19 c4) ▸
       at 0 87 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ CX41 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part20 c4) ▸
       at 0 91 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ X1 ∷ Toff203 ∷ CX41 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff203 ∷ X1 ∷ X1 ∷ CCZ124 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part21 c4) ▸
       at 0 91 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ CX13 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part22 c4) ▸
       at 0 104 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part23 c4) ▸ done

  b3 : Chain (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b3 = at 0 104 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part24 c4) ▸
       at 0 70 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ CS03 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part25 c4) ▸
       at 0 64 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part26 c4) ▸
       at 0 78 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ X1 ∷ Bx2-0413 ∷ CS23 ∷ X1 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part27 c4) ▸
       at 0 83 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part28 c4) ▸
       at 0 82 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ X1 ∷ CS23⁻ ∷ Bx2-0413 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part29 c4) ▸
       at 0 83 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ X1 ∷ Bx2-0143 ∷ X1 ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part30 c4) ▸
       at 0 83 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part31 c4) ▸ done

  b4 : Chain (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  b4 = at 0 72 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ ι⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part32 c4) ▸
       at 0 78 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ X1 ∷ Bx2-0413 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ Toff204 ∷ CCZ123 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part33 c4) ▸
       at 0 79 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ K3 ∷ CCZ134 ∷ X1 ∷ K3⁻ ∷ Sb2-0-41-3 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part34 c4) ▸
       at 0 66 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ X1 ∷ X1 ∷ CCZ234 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part35 c4) ▸
       at 0 87 (CS04 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS23 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CS24 ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ CX13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ X1 ∷ CX04 ∷ X1 ∷ X1 ∷ CS02 ∷ X1 ∷ X1 ∷ Toff213 ∷ X1 ∷ X1 ∷ CCZ024 ∷ X1 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part36 c4) ▸
       at 0 104 (X1 ∷ Sb2-0-41-3 ∷ X1 ∷ Sb2-0-41-3 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CS14 ∷ S1⁻ ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K0-rhs-shape-part37 c4) ▸ done


-- auto Sd0 | SBOX(1;2;03;4) @0110: 7 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0110 : Ws → ⟪ (S1⁻ ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ S1⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0110 c4 = run b0
  where
  b0 : Chain (S1⁻ ∷ Sb0-2-13-4 ∷ []) (Sb0-2-13-4 ∷ S1⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (S0⁻ ∷ Sw01 ∷ []) (sym (wl0478 (lit c4))) ▸
       at 2 2 (Sb1-2-03-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-03-4 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ c4) ▸
       at 0 2 (Sb0-2-13-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·03·4⟩ (lit c4)) ▸
       at 1 2 (S1⁻ ∷ Sw01 ∷ []) (sym (wl0479 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4) @021021: 7 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at021021 : Ws → ⟪ (S2⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ S2⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at021021 c4 = run b0
  where
  b0 : Chain (S2⁻ ∷ Sb0-1-23-4 ∷ []) (Sb0-1-23-4 ∷ S2⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S1⁻ ∷ Sw12 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 2 (Sb0-2-13-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-13-4 ∷ S1⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0110 c4) ▸
       at 0 2 (Sb0-1-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·13·4⟩ (lit c4)) ▸
       at 1 2 (S2⁻ ∷ Sw12 ∷ []) (sym (wl0481 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4) @03102132: 7 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at03102132 : Ws → ⟪ (S3⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ S3⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4 = run b0
  where
  b0 : Chain (S3⁻ ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ S3⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (S2⁻ ∷ Sw23 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-23-4 ∷ S2⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at021021 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (S3⁻ ∷ Sw23 ∷ []) (sym (wl0483 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4) @0410213243: 7 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0410213243 : Ws → ⟪ (S4⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (S4⁻ ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (S3⁻ ∷ Sw34 ∷ []) (sym (wl0484 (lit c4))) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ S3⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at03102132 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (S4⁻ ∷ Sw34 ∷ []) (sym (wl0485 (lit c4))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4) @04203243: 7 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at04203243 : Ws → ⟪ (S4⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ S4⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4 = run b0
  where
  b0 : Chain (S4⁻ ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ S4⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (S4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((S • S • S) ↑ ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ S4⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (S4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((S • S • S) ↑ ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4) @0412203143: 7 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0412203143 : Ws → ⟪ (S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (S4⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (S4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((S • S • S) ↑)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ S4⁻ ∷ []) (lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩-at04203243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (S4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((S • S • S) ↑)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340) @3443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at3443 : Ws → ⟪ (CS01⁻ ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 (Bx1-2340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (Bx1-2340 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩ c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2340⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340) @01103443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at01103443 : Ws → ⟪ (CS01⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at01103443 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 2 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx1-2430 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at3443 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340) @0210213443: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0210213443 : Ws → ⟪ (CS02⁻ ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0210213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 2 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-2431 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at01103443 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340) @0310213442: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0310213442 : Ws → ⟪ (CS03⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0310213442 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS03⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0210213443 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340) @03203442: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at03203442 : Ws → ⟪ (CS13⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at03203442 c4 = run b0
  where
  b0 : Chain (CS13⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS13⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 (lit c4))) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS03⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0310213442 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340) @0312203441: 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 : Ws → ⟪ (CS23⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩-at0312203441 c4 = run b0
  where
  b0 : Chain (CS23⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS23⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 (lit c4))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS13⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨1·2340⟩-at03203442 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340) @3443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at3443 : Ws → ⟪ (CS01 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2430 ∷ []) (Bx1-2430 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Bx1-2340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (Bx1-2340 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩ c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2340⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340) @01103443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at01103443 : Ws → ⟪ (CS01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at01103443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (Bx1-2430 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at3443 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340) @0210213443: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0210213443 : Ws → ⟪ (CS02 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0210213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1432 ∷ []) (Bx0-1432 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (Bx0-2431 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at01103443 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340) @0310213442: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0310213442 : Ws → ⟪ (CS03 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0310213442 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1432 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0210213443 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340) @03203442: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at03203442 : Ws → ⟪ (CS13 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS13 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at03203442 c4 = run b0
  where
  b0 : Chain (CS13 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS13 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 (lit c4))) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS03 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at0310213442 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340) @0312203441: 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 : Ws → ⟪ (CS23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS23 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩-at0312203441 c4 = run b0
  where
  b0 : Chain (CS23 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS23 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CS13 ∷ []) (lem-auto-CS01-∣-BOX⟨1·2340⟩-at03203442 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(0;1;23;4) @2332: 7 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at2332 : Ws → ⟪ (Toff013 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Toff013 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4)) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-23-4 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(0;1;23;4) @243243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at243243 : Ws → ⟪ (Toff014 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Toff014 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4)) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Toff013 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at2332 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(0;1;23;4) @0110243243: 7 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0110243243 : Ws → ⟪ (Toff104 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Toff104 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Toff104 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Toff014 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(0;1;23;4) @0210243143: 7 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 : Ws → ⟪ (Toff204 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Toff204 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Toff104 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done

