{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0034 ; wl0037 ; wl0038 ; wl0044 ; wl0047 ; wl0070 ; wl0078 ; wl0084 ; wl0097 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0103 ; wl0110 ; wl0111 ; wl0113 ; wl0116 ; wl0130 ; wl0143 ; wl0154 ; wl0158 ; wl0167 ; wl0168 ; wl0169 ; wl0170 ; wl0171 ; wl0172 ; wl0173 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0182 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0187 ; wl0188 ; wl0189 ; wl0190 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0198 ; wl0199 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0205 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0210 ; wl0211 ; wl0212 ; wl0213 ; wl0214 ; wl0215 ; wl0216 ; wl0217 ; wl0218 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0223 ; wl0224 ; wl0225 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0230 ; wl0231 ; wl0232 ; wl0233 ; wl0234 ; wl0235 ; wl0236 ; wl0237 ; wl0238 ; wl0239 ; wl0240 ; wl0241 ; wl0242 ; wl0243 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0251 ; wp0001 ; wp0002 ; wp0003 ; wp0004 ; wp0005 ; wp0006 ; wp0007 ; wp0008 ; wp0009 ; wp0010 ; wp0011 ; wp0012 ; wp0013 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0024 ; wp0025 ; wp0026 ; wp0027 ; wp0028 ; wp0029 ; wp0030 ; wp0031 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0040 ; wp0041 ; wp0042 ; wp0043 ; wp0044 ; wp0045 ; wp0046 ; wp0047 ; wp0048 ; wp0049 ; wp0050 ; wp0051 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0056 ; wp0057 ; wp0058 ; wp0059)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CCZ034-CS12 ; lem-comm-CS12-CCZ034 ; lem-comm-CZ12-CCZ034 ; lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF203 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-BOX⟨1·034⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS03-TOFF214 ; lem-comm-CX12-CCZ034 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF314-CS02 ; lem-comm-TOFF314-CSd02 ; lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨1·4023⟩ ; lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-1-BOX⟨0·1243⟩ ; lem-nat-1-BOX⟨2·4013⟩ ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204 ; lem-nat-2-BOX⟨0·2143⟩ ; lem-nat-2-BOX⟨3·4012⟩ ; lem-nat-3-BOX⟨0·3142⟩ ; lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-0-BOX⟨3·4021⟩ ; lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-1-BOX⟨1·4032⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·2314⟩ ; lem-nat-2-BOX⟨2·4013⟩ ; lem-nat-2-BOX⟨2·4031⟩ ; lem-nat-2-TOFF104 ; lem-nat-3-BOX⟨0·3124⟩ ; lem-nat-3-BOX⟨0·3214⟩ ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨0·4213⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-BOX⟨2·4103⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·4203⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·4103⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CCZ014 ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-BOX⟨2·0314⟩ ; lem-nat-3-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-1-CZ01 ; lem-nat-1-CZ02)
-- beta-form: 9 steps
lem-beta-form : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0001 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0001 c4) ▸ done


-- CCZ012-CCZ034: 7 steps
lem-CCZ012-CCZ034 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CCZ012-CCZ034 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0002 c4) ▸
       at 0 2 (CS04 ∷ CCZ012 ∷ []) (wp0003 c4) ▸
       at 1 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 2 2 (CS04⁻ ∷ CCZ012 ∷ []) (wp0004 c4) ▸
       at 3 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 4 2 (CS03 ∷ CCZ012 ∷ []) (wl0167 (lit c4)) ▸
       at 0 5 (CCZ034 ∷ []) (sym (wp0002 c4)) ▸ done


-- P12-P34: 4 steps
lem-P12-P34 : Ws → ⟪ (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-P12-P34 c4 = run b0
  where
  b0 : Chain (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ [])
  b0 = at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ CS12 ∷ []) (c₃ (CS ↑) (CS • CS • CS)) ▸ done


-- Z0-beta: 8 steps
lem-Z0-beta : Ws → ⟪ (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-Z0-beta c4 = run b0
  where
  b0 : Chain (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CZ12 ∷ Z0 ∷ []) (sym (wl0168 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ Z0 ∷ []) (sym (wp0005 c4)) ▸
       at 4 3 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ Z0 ∷ []) (sym (wl0169 (lit c4))) ▸
       at 7 3 (CCZ034 ∷ []) (sym (wp0006 c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 3 4 (Toff012 ∷ CCZ012 ∷ []) (wl0170 (lit c4)) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- beta-mirror: 6 steps
lem-beta-mirror : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-mirror c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) (sym (lem-Z0-beta c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ Z0 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ Z0 ∷ []) (sym (wp0005 c4)) ▸
       at 3 3 (CCZ012 ∷ Toff012 ∷ Z0 ∷ []) (sym (wl0172 (lit c4))) ▸
       at 5 3 (CCZ034 ∷ []) (sym (wp0006 c4)) ▸ done


-- W-Q: 7 steps
lem-W-Q : Ws → ⟪ (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
lem-W-Q c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ [])
  b0 = at 0 0 (S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ []) (sym (wl0173 (lit c4))) ▸
       at 2 4 (CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 4 4 (CCZ034 ∷ CS34⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (sym (wp0007 c4)) ▸
       at 2 4 (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ []) (lem-P12-P34 c4) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ S0 ∷ K0 ∷ []) (wp0008 c4) ▸
       at 2 4 (CCZ012 ∷ Toff012 ∷ S0 ∷ K0 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 4 4 [] (wl0173 (lit c4)) ▸ done


-- V-Q: 3 steps
lem-V-Q : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-V-Q c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b0 = at 4 0 (CCZ012 ∷ Toff012 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (wl0176 (lit c4))) ▸
       at 2 4 (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-W-Q c4)) ▸
       at 0 4 [] (wl0177 (lit c4)) ▸ done


-- beta-T34: 4 steps
lem-beta-T34 : Ws → ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-beta-T34 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 2 1 (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (wp0009 c4) ▸
       at 7 1 (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (wp0009 c4) ▸
       at 3 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-V-Q c4)) ▸
       at 5 5 (Toff034 ∷ []) (wp0010 c4) ▸ done


-- K0-beta: 16 steps
lem-K0-beta : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-K0-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ Z0 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ CZ34 ∷ Z0 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ K0 ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff034 ∷ K0 ∷ []) (wp0011 c4) ▸
       at 3 3 (CCZ012 ∷ Toff012 ∷ K0 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 5 3 (Toff034 ∷ []) (wp0012 c4) ▸
       at 6 0 (Z0 ∷ Z0 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 5 2 (Z0 ∷ Toff034 ∷ CZ34 ∷ []) (wp0013 c4) ▸
       at 3 3 (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0172 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ Z0 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ CZ34 ∷ Z0 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 2 2 (Z0 ∷ Toff034 ∷ CZ34 ∷ []) (wp0013 c4) ▸
       at 0 3 (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0171 (lit c4)) ▸
       at 4 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 5 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 6 3 (Toff034 ∷ []) (wp0014 c4) ▸
       at 1 6 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (sym (lem-beta-T34 c4)) ▸
       at 1 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-Z0-beta c4) ▸ done


-- beta-T: 8 steps
lem-beta-T : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 4 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0181 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 2 3 (Toff012 ∷ CCZ012 ∷ []) (wl0182 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4) ▸
       at 4 2 [] (wl0183 (lit c4)) ▸ done


-- S0-beta: 10 steps
lem-S0-beta : Ws → ⟪ (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-S0-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CS12⁻ ∷ Toff012 ∷ S0 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ S0 ∷ []) (sym (wp0015 c4)) ▸
       at 3 3 (Toff012 ∷ CS12 ∷ S0 ∷ []) (wl0185 (lit c4)) ▸
       at 5 3 (CCZ034 ∷ []) (sym (wp0016 c4)) ▸
       at 3 2 (CS12 ∷ Toff012 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 2 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 1 2 (CS12 ∷ Toff012 ∷ []) (sym (wl0186 (lit c4))) ▸ done

  b1 : Chain (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 0 2 [] (wl0187 (lit c4)) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-beta-T c4)) ▸ done


-- S0-beta-c: 2 steps
lem-S0-beta-c : Ws → ⟪ (S0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0 ∷ []) ⟫ʷ
lem-S0-beta-c c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ [])
  b0 = at 2 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0188 (lit c4))) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-S0-beta c4) ▸ done


-- S0-beta-ci: 2 steps
lem-S0-beta-ci : Ws → ⟪ (S0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ
lem-S0-beta-ci c4 = run b0
  where
  b0 : Chain (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ [])
  b0 = at 1 1 (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) (sym (lem-S0-beta c4)) ▸
       at 0 2 [] (wl0188 (lit c4)) ▸ done


-- K0-pass: 1 steps
lem-K0-pass : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-K0-pass c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 3 (Bx0-1234 ∷ []) (lem-K0-beta c4) ▸ done


-- K0-pass-c: 2 steps
lem-K0-pass-c : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-K0-pass-c c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  b0 = at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-K0-pass c4) ▸ done


-- K0-pass-ci: 2 steps
lem-K0-pass-ci : Ws → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-K0-pass-ci c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (sym (lem-K0-pass c4)) ▸
       at 0 2 [] (wl0189 (lit c4)) ▸ done


-- CCZ134-W: 9 steps
lem-CCZ134-W : Ws → ⟪ (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CCZ134-W c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 4 3 (CCZ012 ∷ Toff012 ∷ CS13 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 2 3 (CCZ012 ∷ Toff012 ∷ CS14⁻ ∷ []) (sym (wp0017 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CS14 ∷ []) (sym (wp0018 c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ [])
  b1 = at 2 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸ done


-- CX10-beta: 8 steps
lem-CX10-beta : Ws → ⟪ (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-CX10-beta c4 = run b0
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ CX10 ∷ []) (wl0192 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CCZ134 ∷ CX10 ∷ []) (sym (wp0019 c4)) ▸
       at 4 3 (CCZ012 ∷ Toff012 ∷ CX10 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ []) (lem-CCZ134-W c4) ▸
       at 5 3 (CCZ034 ∷ []) (sym (wp0021 c4)) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-mirror c4)) ▸ done


-- CX10-beta-c: 2 steps
lem-CX10-beta-c : Ws → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CX10-beta-c c4 = run b0
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  b0 = at 2 0 (CX10 ∷ CX10 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-CX10-beta c4) ▸ done


-- CS20-beta: 10 steps
lem-CS20-beta : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-CS20-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CS12⁻ ∷ Toff012 ∷ CS02 ∷ []) (wl0195 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0022 c4)) ▸
       at 3 3 (Toff012 ∷ CS12 ∷ CS02 ∷ []) (wl0196 (lit c4)) ▸
       at 5 3 (CCZ034 ∷ []) (sym (wp0023 c4)) ▸
       at 3 2 (CS12 ∷ Toff012 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 2 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 1 2 (CS12 ∷ Toff012 ∷ []) (sym (wl0186 (lit c4))) ▸ done

  b1 : Chain (CS12⁻ ∷ CS12 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 0 2 [] (wl0187 (lit c4)) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-beta-T c4)) ▸ done


-- CS20-beta-c: 2 steps
lem-CS20-beta-c : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-CS20-beta-c c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  b0 = at 2 0 (CS02⁻ ∷ CS02 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 0 3 (Bx0-1234 ∷ []) (lem-CS20-beta c4) ▸ done


-- CS20-beta-ci: 2 steps
lem-CS20-beta-ci : Ws → ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ [])
  b0 = at 1 1 (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) (sym (lem-CS20-beta c4)) ▸
       at 0 2 [] (wl0197 (lit c4)) ▸ done


-- V-beta: 10 steps
lem-V-beta : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-V-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (S0 ∷ Bx0-1234 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 2 (S0 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) (sym (wl0198 (lit c4))) ▸
       at 7 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-S0-beta-ci c4) ▸
       at 6 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4) ▸
       at 5 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 4 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 3 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 1 2 (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4) ▸ done

  b1 : Chain (S0 ∷ Bx0-1234 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-S0-beta-c c4) ▸
       at 1 8 (Toff012 ∷ CCZ012 ∷ []) (wl0198 (lit c4)) ▸ done


-- beta-inv: 7 steps
lem-beta-inv : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) []
  b0 = at 1 1 (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-mirror c4) ▸
       at 0 3 (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (sym (lem-V-beta c4)) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 7 2 [] (wp0024 c4) ▸
       at 0 4 [] (wl0177 (lit c4)) ▸
       at 1 4 [] (wl0177 (lit c4)) ▸
       at 0 2 [] (wp0024 c4) ▸ done


-- beta-form @1221: 10 steps
lem-beta-form-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw12 ∷ CCZ034 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw12 ∷ CCZ034 ∷ Sw12 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 6 2 [] (wl0001 (lit c4)) ▸ done


-- sym12: 4 steps
lem-sym12 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym12 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ Toff012 ∷ []) (wl0199 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CCZ012 ∷ []) (wl0200 (lit c4)) ▸
       at 0 6 (Bx0-2134 ∷ []) (sym (lem-beta-form-at1221 c4)) ▸ done


-- beta-form @3443: 10 steps
lem-beta-form-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw34 ∷ CCZ034 ∷ Sw34 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ Sw34 ∷ CCZ034 ∷ Sw34 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 (lit c4)) ▸
       at 6 2 [] (wl0007 (lit c4)) ▸ done


-- sym34: 4 steps
lem-sym34 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym34 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 2 1 (CCZ034 ∷ []) (wp0025 c4) ▸
       at 5 1 (CCZ034 ∷ []) (wp0025 c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (sym (lem-beta-form-at3443 c4)) ▸ done


-- CS12-beta: 6 steps
lem-CS12-beta : Ws → ⟪ (CS12 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-beta c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CS12 ∷ []) (sym (wl0201 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 3 3 (Toff012 ∷ CCZ012 ∷ CS12 ∷ []) (wl0202 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- CSd12-beta: 5 steps
lem-CSd12-beta : Ws → ⟪ (CS12⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSd12-beta c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ [])
  b0 = at 0 1 (CS12 ∷ CS12 ∷ CS12 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 1 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 0 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 1 3 (CS12⁻ ∷ []) (wl0203 (lit c4)) ▸ done


-- Cz-beta: 7 steps
lem-Cz-beta : Ws → ⟪ (CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ []) (wl0204 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4) ▸
       at 3 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 2 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0204 (lit c4))) ▸ done


-- W-beta: 3 steps
lem-W-beta : Ws → ⟪ (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
lem-W-beta c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ [])
  b0 = at 3 0 (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 3 (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (sym (lem-V-beta c4)) ▸
       at 0 4 [] (wl0176 (lit c4)) ▸ done


-- T-beta: 4 steps
lem-T-beta : Ws → ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-beta c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) (sym (wl0205 (lit c4))) ▸
       at 1 3 (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ []) (lem-W-beta c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 1 3 (Toff012 ∷ []) (wl0205 (lit c4)) ▸ done


-- beta-T @2332: 8 steps
lem-beta-T-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @243243: 8 steps
lem-beta-T-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0007 (lit c4)) ▸ done


-- beta-T @12243143: 8 steps
lem-beta-T-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @13243142: 8 steps
lem-beta-T-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4)) ▸
       at 3 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- CX23-beta: 17 steps
lem-CX23-beta : Ws → ⟪ (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ CCZ024 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CX23 ∷ []) (sym (wl0206 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CCZ024 ∷ CX23 ∷ []) (sym (wp0026 c4)) ▸
       at 4 3 (Toff012 ∷ CCZ012 ∷ CX23 ∷ []) (wl0207 (lit c4)) ▸
       at 6 3 (CCZ034 ∷ CCZ024 ∷ []) (sym (wp0027 c4)) ▸
       at 3 3 (Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0028 c4) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0208 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0029 c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b1 = at 9 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0030 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0031 c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0208 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0033 c4)) ▸
       at 6 2 [] (wp0034 c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ124 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- CX32-beta: 16 steps
lem-CX32-beta : Ws → ⟪ (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CX32-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CCZ123 ∷ CX32 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0035 c4)) ▸
       at 6 3 (CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CX32 ∷ []) (sym (wl0210 (lit c4))) ▸
       at 11 3 (CCZ034 ∷ []) (sym (wp0036 c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0037 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0038 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0039 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 5 2 [] (wl0212 (lit c4)) ▸
       at 2 5 (CCZ134 ∷ CCZ034 ∷ []) (wp0040 c4) ▸
       at 0 3 (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) (sym (lem-CCZ134-W c4)) ▸
       at 1 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- c124-beta: 20 steps
lem-c124-beta : Ws → ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-c124-beta c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ124 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ012 ∷ CCZ124 ∷ []) (sym (wp0041 c4)) ▸
       at 1 2 (Toff012 ∷ CCZ124 ∷ []) (wp0042 c4) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0208 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0029 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0030 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ [])
  b1 = at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0031 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0208 (lit c4))) ▸
       at 3 2 (Toff012 ∷ CCZ124 ∷ []) (wp0042 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ124 ∷ []) (sym (wp0041 c4)) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0208 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0029 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0030 c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0031 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0208 (lit c4))) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- c134-beta: 32 steps
lem-c134-beta : Ws → ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-c134-beta c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CCZ134 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ CCZ134 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0213 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS14⁻ ∷ []) (sym (wp0043 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0044 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b1 : Chain (CCZ012 ∷ CCZ134 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ CCZ134 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 1 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff012 ∷ CS13 ∷ []) (wl0214 (lit c4)) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Toff012 ∷ CS14⁻ ∷ []) (wp0045 c4) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 1 2 (Toff012 ∷ CS14 ∷ []) (wp0046 c4) ▸
       at 2 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0047 c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ CCZ134 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b2 = at 3 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CS13 ∷ []) (wl0214 (lit c4)) ▸
       at 6 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 5 2 (Toff012 ∷ CS14⁻ ∷ []) (wp0045 c4) ▸
       at 4 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Toff012 ∷ CS14 ∷ []) (wp0046 c4) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4)) ▸ done

  b3 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  b3 = at 8 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0213 (lit c4))) ▸
       at 7 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 6 2 (CCZ012 ∷ CS14⁻ ∷ []) (sym (wp0043 c4)) ▸
       at 5 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 4 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0044 c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0047 c4)) ▸
       at 0 6 (Bx0-1234 ∷ []) (sym (lem-beta-form c4)) ▸ done


-- SW23-beta: 14 steps
lem-SW23-beta : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-SW23-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (CCZ134 ∷ CCZ124 ∷ CX23 ∷ Bx0-1234 ∷ CCZ124 ∷ CCZ134 ∷ CX23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0215 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0215 (lit c4))) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 3 0 (CX32 ∷ CX32 ∷ []) (sym (wl0216 (lit c4))) ▸
       at 1 3 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-CX32-beta c4) ▸
       at 3 3 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 0 3 (CCZ134 ∷ CCZ124 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b1 : Chain (CCZ134 ∷ CCZ124 ∷ CX23 ∷ Bx0-1234 ∷ CCZ124 ∷ CCZ134 ∷ CX23 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 4 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 4 4 (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4) ▸
       at 0 2 (Bx0-1234 ∷ CCZ134 ∷ []) (lem-c134-beta c4) ▸
       at 1 6 [] (wl0221 (lit c4)) ▸ done


-- sym23: 10 steps
lem-sym23 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (sym (lem-SW23-beta c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 2 2 (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ (lit c4)) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 5 2 (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ Sw23 ∷ []) (Bx0-1324 ∷ [])
  b1 = at 0 6 (Bx0-1324 ∷ []) (refl) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- CZ10-beta-c: 4 steps
lem-CZ10-beta-c : Ws → ⟪ (CZ02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ []) ⟫ʷ
lem-CZ10-beta-c c4 = run b0
  where
  b0 : Chain (CZ02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CS02 ∷ CS02 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 1 2 (CZ02 ∷ []) (wl0222 (lit c4)) ▸ done


-- BOXd-BOX: 22 steps
lem-BOXd-BOX : Ws → ⟪ (Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-BOXd-BOX c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx⁻0-1234 ∷ []) (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ CZ14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Bx0-1234 ∷ [])
  b0 = at 1 0 [] (wl0223 (lit c4)) ▸
       at 1 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-beta-inv c4)) ▸
       at 0 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 5 2 [] (wl0183 (lit c4)) ▸
       at 4 2 [] (wl0224 (lit c4)) ▸
       at 3 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 3 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ CZ14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Bx0-1234 ∷ []) (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Bx0-1234 ∷ [])
  b1 = at 6 1 (CZ14 ∷ []) (refl) ▸
       at 9 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 11 1 (CZ14 ∷ []) (refl) ▸
       at 14 1 (CZ14 ∷ []) (refl) ▸
       at 3 12 [] (wp0048 c4) ▸
       at 2 2 [] (wl0224 (lit c4)) ▸
       at 1 2 [] (wl0183 (lit c4)) ▸
       at 0 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸ done

  b2 : Chain (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx1-034 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 0 1 (CZ14 ∷ []) (refl) ▸
       at 3 1 (CZ14 ∷ []) (refl) ▸
       at 6 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 8 1 (CZ14 ∷ []) (refl) ▸
       at 11 1 (CZ14 ∷ []) (refl) ▸
       at 0 12 [] (wp0048 c4) ▸ done


-- auto TOFF012 | CCZ324: 7 steps
lem-auto-TOFF012-∣-CCZ324 : Ws → ⟪ (Toff012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0225 (lit c4)) ▸
       at 0 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸
       at 1 2 (CX24 ∷ Toff012 ∷ []) (sym (wp0049 c4)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 3 2 (CX24 ∷ Toff012 ∷ []) (sym (wp0049 c4)) ▸
       at 4 2 (CS23 ∷ Toff012 ∷ []) (sym (wl0226 (lit c4))) ▸
       at 0 5 (CCZ234 ∷ []) (sym (wl0225 (lit c4))) ▸ done


-- auto CCZ012 | CCZ314: 7 steps
lem-auto-CCZ012-∣-CCZ314 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0227 (lit c4)) ▸
       at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CX14 ∷ CCZ012 ∷ []) (wp0050 c4) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ []) (wp0050 c4) ▸
       at 4 2 (CS13 ∷ CCZ012 ∷ []) (wl0213 (lit c4)) ▸
       at 0 5 (CCZ134 ∷ []) (sym (wl0227 (lit c4))) ▸ done


-- auto CCZ012 | CCZ304: 7 steps
lem-auto-CCZ012-∣-CCZ304 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0051 c4) ▸
       at 0 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CX04 ∷ CCZ012 ∷ []) (wp0052 c4) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 3 2 (CX04 ∷ CCZ012 ∷ []) (wp0052 c4) ▸
       at 4 2 (CS03 ∷ CCZ012 ∷ []) (wl0167 (lit c4)) ▸
       at 0 5 (CCZ034 ∷ []) (sym (wp0051 c4)) ▸ done


-- auto CCZ012 | TOFF304: 5 steps
lem-auto-CCZ012-∣-TOFF304 : Ws → ⟪ (CCZ012 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0053 c4)) ▸
       at 0 2 (K3 ∷ CCZ012 ∷ []) (wl0228 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ304 c4) ▸
       at 2 2 (K3⁻ ∷ CCZ012 ∷ []) (wl0229 (lit c4)) ▸
       at 0 3 (Toff304 ∷ []) (wp0053 c4) ▸ done


-- beta-form @2332: 10 steps
lem-beta-form-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-form-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ Sw23 ∷ CCZ034 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ Sw23 ∷ CCZ034 ∷ Sw23 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 6 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | CCZ324 @0110: 7 steps
lem-auto-TOFF012-∣-CCZ324-at0110 : Ws → ⟪ (Toff102 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ324 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto TOFF012 | CCZ324 @021021: 7 steps
lem-auto-TOFF012-∣-CCZ324-at021021 : Ws → ⟪ (Toff201 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0110 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | CCZ324 @03102132: 7 steps
lem-auto-TOFF012-∣-CCZ324-at03102132 : Ws → ⟪ (Toff301 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at021021 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto TOFF012 | CCZ324 @031031: 7 steps
lem-auto-TOFF012-∣-CCZ324-at031031 : Ws → ⟪ (Toff302 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff302 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at031031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at03102132 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto TOFF012 | CCZ324 @0330: 7 steps
lem-auto-TOFF012-∣-CCZ324-at0330 : Ws → ⟪ (Toff312 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff312 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at0330 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Toff302 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at031031 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | CCZ314 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ314-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ314 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | CCZ314 @122331: 7 steps
lem-auto-CCZ012-∣-CCZ314-at122331 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at2332 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | CCZ314 @01122330: 7 steps
lem-auto-CCZ012-∣-CCZ314-at01122330 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at122331 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | TOFF304 @2332: 7 steps
lem-auto-CCZ012-∣-TOFF304-at2332 : Ws → ⟪ (CCZ013 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4)) ▸
       at 1 2 (Toff304 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF304 c4) ▸
       at 0 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | TOFF304 @243243: 7 steps
lem-auto-CCZ012-∣-TOFF304-at243243 : Ws → ⟪ (CCZ014 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 (lit c4)) ▸
       at 1 2 (Toff204 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at2332 c4) ▸
       at 0 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | TOFF304 @12243143: 7 steps
lem-auto-CCZ012-∣-TOFF304-at12243143 : Ws → ⟪ (CCZ024 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4)) ▸
       at 1 2 (Toff203 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at243243 c4) ▸
       at 0 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | TOFF304 @0112243043: 7 steps
lem-auto-CCZ012-∣-TOFF304-at0112243043 : Ws → ⟪ (CCZ124 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4)) ▸
       at 1 2 (Toff103 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at12243143 c4) ▸
       at 0 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | CCZ304 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ304-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ304 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | CCZ304 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ304-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at2332 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | CCZ304 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ304-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | CCZ304 @0112243043: 7 steps
lem-auto-CCZ012-∣-CCZ304-at0112243043 : Ws → ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at12243143 c4) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta: 17 steps
lem-T312-beta : Ws → ⟪ (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ CCZ024 ∷ CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ Toff312 ∷ Toff312 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 1 1 (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (lem-beta-form-at2332 c4) ▸
       at 3 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 0 4 (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ Toff312 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0330 c4) ▸
       at 9 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 6 4 (CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (wl0232 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ Toff312 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0330 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ CCZ024 ∷ CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ Toff312 ∷ Toff312 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
  b1 = at 12 2 [] (wl0230 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at01122330 c4) ▸
       at 5 2 [] (wl0212 (lit c4)) ▸
       at 2 5 (CCZ024 ∷ CCZ124 ∷ []) (wp0054 c4) ▸
       at 3 2 (Toff013 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at0112243043 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at0112243043 c4) ▸
       at 5 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0033 c4)) ▸
       at 0 6 (Bx0-1324 ∷ []) (sym (lem-beta-form-at2332 c4)) ▸ done

  b2 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 0 1 (Bx0-1234 ∷ []) (sym (lem-sym23 c4)) ▸ done


-- F0-A: 9 steps
lem-F0-A : Ws → ⟪ (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ
lem-F0-A c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ CX23 ∷ Toff214 ∷ Toff314 ∷ [])
  b0 = at 0 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 4 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 9 0 (CX23 ∷ CX23 ∷ []) (sym (wl0218 (lit c4))) ▸
       at 1 4 (Toff214 ∷ []) (wl0233 (lit c4)) ▸
       at 2 5 (CS03⁻ ∷ []) (sym (wl0234 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 0 2 (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 4 2 (CX23 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0236 (lit c4))) ▸ done

  b1 : Chain (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ CX23 ∷ Toff214 ∷ Toff314 ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ [])
  b1 = at 3 2 [] (wl0218 (lit c4)) ▸ done


-- F0-B: 6 steps
lem-F0-B : Ws → ⟪ (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-F0-B c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ [])
  b0 = at 2 1 (CS02 ∷ CS03 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (wl0237 (lit c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ []) (sym (wl0238 (lit c4))) ▸
       at 4 5 (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (sym (lem-F0-A c4)) ▸
       at 4 0 [] (wl0223 (lit c4)) ▸
       at 6 4 (CS03⁻ ∷ CS02⁻ ∷ []) (wl0239 (lit c4)) ▸
       at 4 2 (Toff314 ∷ Toff214 ∷ []) (wl0238 (lit c4)) ▸ done


-- F0-C: 8 steps
lem-F0-C : Ws → ⟪ (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-F0-C c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 2 (CS02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CS02 (lit c4)) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ []) (sym (wl0238 (lit c4))) ▸
       at 3 2 (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4)) ▸
       at 2 2 (Toff214 ∷ Toff314 ∷ []) (sym (wl0238 (lit c4))) ▸
       at 6 2 (CS02⁻ ∷ CS03⁻ ∷ []) (sym (wl0240 (lit c4))) ▸
       at 5 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 4 2 (CS02⁻ ∷ CS03 ∷ []) (sym (wl0241 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸ done


-- beta-T @1221: 8 steps
lem-beta-T-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @132132: 8 steps
lem-beta-T-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at1221 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @14213243: 8 steps
lem-beta-T-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at132132 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0007 (lit c4)) ▸ done


-- beta-T @0114203243: 8 steps
lem-beta-T-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @0214203143: 8 steps
lem-beta-T-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0114203243 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @0314203142: 8 steps
lem-beta-T-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0214203143 c4) ▸
       at 0 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 2 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @0314213042: 8 steps
lem-beta-T-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0314203142 c4) ▸
       at 0 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @1221: 5 steps
lem-sym34-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym34-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @132132: 5 steps
lem-sym34-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym34-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @14213243: 5 steps
lem-sym34-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym34-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym34-at132132 c4) ▸
       at 0 2 (Bx0-4132 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym34 @0114203243: 5 steps
lem-sym34-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ []) ⟫ʷ
lem-sym34-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Bx1-4032 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym34-at14213243 c4) ▸
       at 0 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0214203143: 5 steps
lem-sym34-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym34-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 1 (Bx1-4032 ∷ []) (lem-sym34-at0114203243 c4) ▸
       at 0 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @0314203142: 5 steps
lem-sym34-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym34-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4031⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @0314213042: 5 steps
lem-sym34-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym34-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym34-at0314203142 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @1221: 8 steps
lem-T312-beta-at1221 : Ws → ⟪ (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at1221 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @132132: 8 steps
lem-T312-beta-at132132 : Ws → ⟪ (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at132132 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 (lit c4)) ▸
       at 1 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-T312-beta-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @14213243: 8 steps
lem-T312-beta-at14213243 : Ws → ⟪ (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at14213243 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 (lit c4)) ▸
       at 2 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4)) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 (lit c4)) ▸
       at 1 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-T312-beta-at132132 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- T312-beta @0114203243: 8 steps
lem-T312-beta-at0114203243 : Ws → ⟪ (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0114203243 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) (Bx1-4023 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4)) ▸
       at 2 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4)) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4)) ▸
       at 1 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @0214203143: 8 steps
lem-T312-beta-at0214203143 : Ws → ⟪ (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 2 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4)) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 1 3 (Bx1-4023 ∷ CCZ034 ∷ []) (lem-T312-beta-at0114203243 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @0314203142: 8 steps
lem-T312-beta-at0314203142 : Ws → ⟪ (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 (lit c4)) ▸
       at 2 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 (lit c4)) ▸
       at 1 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-T312-beta-at0214203143 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @0314203241: 8 steps
lem-T312-beta-at0314203241 : Ws → ⟪ (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 2 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4)) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 1 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @0314213240: 8 steps
lem-T312-beta-at0314213240 : Ws → ⟪ (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 (lit c4)) ▸
       at 2 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ (lit c4)) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 (lit c4)) ▸
       at 1 3 (Bx3-4021 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314203241 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0314203241: 5 steps
lem-sym34-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym34-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym34-at0314203142 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @0314213240: 5 steps
lem-sym34-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym34-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ (lit c4)) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym34-at0314203241 c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @1221: 5 steps
lem-sym23-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym23-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @132132: 5 steps
lem-sym23-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym23-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (Bx0-3214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @14213243: 5 steps
lem-sym23-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym23-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3214⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym23 @0114203243: 5 steps
lem-sym23-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ []) ⟫ʷ
lem-sym23-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Bx1-4203 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 0 2 (Bx1-4203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4213⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0214203143: 5 steps
lem-sym23-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym23-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 1 (Bx1-4203 ∷ []) (lem-sym23-at0114203243 c4) ▸
       at 0 2 (Bx2-4103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4203⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @0314203142: 5 steps
lem-sym23-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym23-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4103⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @0314213042: 5 steps
lem-sym23-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym23-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @1221: 5 steps
lem-sym12-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym12-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @132132: 5 steps
lem-sym12-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym12-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym12 @14213243: 5 steps
lem-sym12-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym12-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym12 @0114203243: 5 steps
lem-sym12-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym12-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0214203143: 5 steps
lem-sym12-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym12-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @0314203142: 5 steps
lem-sym12-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym12-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- beta-inv @2332: 5 steps
lem-beta-inv-at2332 : Ws → ⟪ (Bx0-1324 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Bx0-1324 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv c4) ▸
       at 0 2 [] (wl0006 (lit c4)) ▸ done


-- beta-inv @243243: 5 steps
lem-beta-inv-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Bx0-1423 ∷ []) []
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at2332 c4) ▸
       at 0 2 [] (wl0007 (lit c4)) ▸ done


-- beta-inv @0110243243: 5 steps
lem-beta-inv-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Bx1-0423 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 2 [] (wl0002 (lit c4)) ▸ done


-- beta-inv @0210243143: 5 steps
lem-beta-inv-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ Bx2-0413 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at0110243243 c4) ▸
       at 0 2 [] (wl0001 (lit c4)) ▸ done


-- beta-inv @0310243142: 5 steps
lem-beta-inv-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ Bx3-0412 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 [] (lem-beta-inv-at0210243143 c4) ▸
       at 0 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @0214213043: 8 steps
lem-beta-T-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4)) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0214203143 c4) ▸
       at 0 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0214213043: 5 steps
lem-sym23-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym23-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4)) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- F0-D: 15 steps
lem-F0-D : Ws → ⟪ (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-F0-D c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ Bx3-4012 ∷ CCZ014 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b0 = at 4 1 (CCZ023 ∷ []) (wl0242 (lit c4)) ▸
       at 6 0 (CCZ023 ∷ CCZ023 ∷ []) (sym (wl0243 (lit c4))) ▸
       at 3 4 (Bx3-4102 ∷ []) (sym (lem-beta-T-at0314213042 c4)) ▸
       at 3 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 4 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 2 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 2 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 2 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Bx3-0412 ∷ Bx3-4012 ∷ CCZ014 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-0413 ∷ [])
  b1 = at 2 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 1 2 [] (lem-beta-inv-at0310243142 c4) ▸
       at 0 2 [] (wp0055 c4) ▸
       at 1 1 (CCZ023 ∷ []) (wl0242 (lit c4)) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-beta-T-at0214213043 c4)) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done


-- sym34 @0110: 5 steps
lem-sym34-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym34-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @021021: 5 steps
lem-sym34-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym34-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 1 (Bx1-0243 ∷ []) (lem-sym34-at0110 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @03102132: 5 steps
lem-sym34-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym34-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-sym34-at021021 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- c124-beta @3443: 7 steps
lem-c124-beta-at3443 : Ws → ⟪ (CCZ123 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-c124-beta-at3443 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- c124-beta @01103443: 7 steps
lem-c124-beta-at01103443 : Ws → ⟪ (CCZ023 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CCZ023 ∷ []) ⟫ʷ
lem-c124-beta-at01103443 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 2 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-c124-beta-at3443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- c124-beta @0210213443: 7 steps
lem-c124-beta-at0210213443 : Ws → ⟪ (CCZ013 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ013 ∷ []) ⟫ʷ
lem-c124-beta-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0143 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 2 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 2 (Bx1-0243 ∷ CCZ023 ∷ []) (lem-c124-beta-at01103443 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- c124-beta @0310213442: 7 steps
lem-c124-beta-at0310213442 : Ws → ⟪ (CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0310213442 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 (Bx2-0143 ∷ CCZ013 ∷ []) (lem-c124-beta-at0210213443 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @3443: 5 steps
lem-sym34-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym34-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym34 @01103443: 5 steps
lem-sym34-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym34-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0210213443: 5 steps
lem-sym34-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym34-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @0310213442: 5 steps
lem-sym34-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym34-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0124): 3 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸ done


-- auto CCZ012 | BOX(3;0124) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (Bx3-0124 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩ c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0124) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 (Bx3-0214 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0124) @14213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 : Ws → ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Bx2-0314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx2-0314 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0124) @142142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 : Ws → ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- F0: 13 steps
lem-F0 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Bx3-0412 ∷ CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (sym (lem-F0-D c4)) ▸
       at 2 6 (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (lem-F0-B c4) ▸
       at 2 8 (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (lem-F0-C c4) ▸
       at 6 8 (CCZ014 ∷ []) (sym (wp0056 c4)) ▸
       at 0 2 (Bx3-0412 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 c4) ▸ done

  b1 : Chain (Bx3-0412 ∷ CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) (Sb3-0-41-2 ∷ [])
  b1 = at 1 5 (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) (wp0057 c4) ▸
       at 5 2 [] (wp0055 c4) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- F0d: 61 steps
lem-F0d : Ws → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-41-2 ∷ []) ⟫ʷ
lem-F0d c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ Toff304 ∷ CCZ034 ∷ [])
  b0 = at 1 0 (CCZ034 ∷ CCZ034 ∷ []) (sym (wp0024 c4)) ▸
       at 2 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0058 c4)) ▸
       at 3 0 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 5 1 (Bx3-02 ∷ []) (refl) ▸
       at 8 1 (Bx3-02 ∷ []) (refl) ▸
       at 3 6 (Bx0-312 ∷ []) (refl) ▸
       at 4 1 (Bx⁻3-02 ∷ []) (refl) ▸
       at 7 1 (Bx⁻3-02 ∷ []) (refl) ▸ done

  b1 : Chain (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ Toff304 ∷ CCZ034 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 6 (Bx⁻0-312 ∷ []) (refl) ▸
       at 4 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0058 c4)) ▸
       at 5 0 (CCZ034 ∷ CCZ034 ∷ []) (sym (wp0024 c4)) ▸
       at 6 0 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 8 1 (Bx3-02 ∷ []) (refl) ▸
       at 11 1 (Bx3-02 ∷ []) (refl) ▸
       at 6 6 (Bx0-312 ∷ []) (refl) ▸
       at 7 1 (Bx⁻3-02 ∷ []) (refl) ▸ done

  b2 : Chain (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (Sb⁻2-0-41-3 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ [])
  b2 = at 10 1 (Bx⁻3-02 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-312 ∷ []) (refl) ▸
       at 1 6 (Bx3-0412 ∷ []) (refl) ▸
       at 2 6 (Bx⁻3-0412 ∷ []) (refl) ▸
       at 2 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 3 0 (CS02 ∷ CS02⁻ ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b3 : Chain (Sb⁻2-0-41-3 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b3 = at 4 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 5 0 (CS02⁻ ∷ CS02 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 5 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 1 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 2 5 (Sb⁻3-0-41-2 ∷ []) (refl) ▸
       at 1 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b4 : Chain (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b4 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 9 2 [] (wp0034 c4) ▸
       at 8 2 [] (wp0059 c4) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b5 = at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (wl0247 (lit c4)) ▸
       at 6 2 [] (wp0059 c4) ▸
       at 5 2 [] (wp0034 c4) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b6 = at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (wl0247 (lit c4)) ▸
       at 3 2 [] (wl0248 (lit c4)) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻3-0-41-2 ∷ [])
  b7 = at 2 2 [] (wl0249 (lit c4)) ▸
       at 1 2 [] (wl0248 (lit c4)) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (wl0250 (lit c4)) ▸ done


-- sym12 @011220: 5 steps
lem-sym12-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym12-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- CX10-beta-c @0110: 7 steps
lem-CX10-beta-c-at0110 : Ws → ⟪ (CX01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CX01 ∷ []) ⟫ʷ
lem-CX10-beta-c-at0110 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CX01 ∷ Sw01 ∷ []) (sym (wl0251 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0110: 5 steps
lem-sym12-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym12-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Bx1-2034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto CX01 | BOX(1;2034): 3 steps
lem-auto-CX01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CX01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CX01 ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 0 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-CX10-beta-c-at0110 c4) ▸
       at 0 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸ done


-- CZ10-beta-c @1221: 7 steps
lem-CZ10-beta-c-at1221 : Ws → ⟪ (CZ01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at1221 c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CZ02 ∷ []) (lem-CZ10-beta-c c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- CZ10-beta-c @011220: 7 steps
lem-CZ10-beta-c-at011220 : Ws → ⟪ (CZ01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at011220 c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 (lit c4))) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done

