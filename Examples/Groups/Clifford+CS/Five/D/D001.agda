{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0155 ; wl0156 ; wl0157 ; wl0158 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0163 ; wl0164 ; wl0165 ; wl0166 ; wl0167 ; wl0168 ; wl0169 ; wl0170 ; wl0171 ; wl0172 ; wl0173 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0182 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0187 ; wl0188 ; wl0189 ; wl0190 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0198 ; wl0199 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0205 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0210 ; wl0211 ; wl0212 ; wl0213 ; wl0214 ; wl0215 ; wl0216 ; wl0217 ; wl0218 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0223 ; wl0224 ; wl0225 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0230 ; wl0231 ; wl0232 ; wl0233 ; wl0234 ; wl0235 ; wl0236 ; wl0237 ; wl0238 ; wl0239 ; wl0240 ; wl0241 ; wl0242 ; wl0243 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0251 ; wl0252 ; wl0253 ; wl0254 ; wl0255 ; wl0256 ; wl0257 ; wl0258 ; wl0259 ; wl0260 ; wl0261 ; wl0262 ; wl0263 ; wl0264 ; wl0265 ; wl0266 ; wl0267 ; wl0268 ; wl0269 ; wl0270 ; wl0271 ; wl0272 ; wl0273 ; wl0274 ; wl0275 ; wl0276 ; wl0277 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wp0001 ; wp0002 ; wp0003 ; wp0004 ; wp0005 ; wp0006 ; wp0007 ; wp0008 ; wp0009 ; wp0010 ; wp0011 ; wp0012 ; wp0013 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0024 ; wp0025 ; wp0026 ; wp0027 ; wp0028 ; wp0029 ; wp0030 ; wp0031 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0040 ; wp0041 ; wp0042 ; wp0043 ; wp0044 ; wp0045 ; wp0046 ; wp0047 ; wp0048 ; wp0049 ; wp0050 ; wp0051 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0056 ; wp0057 ; wp0058 ; wp0059 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0073 ; wp0074 ; wp0075 ; wp0076 ; wp0077 ; wp0078 ; wp0079 ; wp0080 ; wp0081 ; wp0082 ; wp0083 ; wp0084 ; wp0085 ; wp0086 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0093 ; wp0094 ; wp0095 ; wp0096 ; wp0097 ; wp0098 ; wp0099 ; wp0100 ; wp0101 ; wp0102 ; wp0103 ; wp0104 ; wp0105 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0110 ; wp0111 ; wp0112 ; wp0113 ; wp0114 ; wp0115 ; wp0116 ; wp0117 ; wp0118 ; wp0119 ; wp0120 ; wp0121 ; wp0122 ; wp0123 ; wp0124 ; wp0125 ; wp0126 ; wp0127 ; wp0128 ; wp0129)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-TOFF034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-CCZ123 ; lem-comm-CX04-TOFF213 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CZ04-CCZ123 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX14-TOFF023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX24-TOFF013 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ14-TOFF023 ; lem-comm-CZ24-CCZ013 ; lem-comm-CZ24-TOFF013 ; lem-comm-SWAP23-BOX⟨0·14⟩ ; lem-comm-TOFF024-CSd13)
-- cQ: 7 steps
lem-cQ : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done


-- tP: 7 steps
lem-tP : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff034 ∷ []) (wp0004 c4) ▸
       at 1 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸ done


-- VPQ: 14 steps
lem-VPQ : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸ done


-- QVQ: 3 steps
lem-QVQ : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-tQ: 13 steps
lem-box-tQ : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0160 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ c4) ▸
       at 2 4 (Toff012 ∷ []) (wl0161 (lit c4)) ▸ done


-- box-cP: 12 steps
lem-box-cP : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done


-- t-cP: 5 steps
lem-t-cP : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-t-cP c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) (sym (wl0163 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸
       at 2 3 (CCZ012 ∷ Toff012 ∷ []) (sym (wl0164 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP c4) ▸ done


-- box2: 11 steps
lem-box2 : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 4 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 5 5 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ []) (lem-t-cP c4) ▸
       at 5 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸
       at 5 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) []
  b1 = at 2 2 [] (wl0162 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0162 (lit c4)) ▸ done


-- Xb-box: 18 steps
lem-Xb-box : Ws → ⟪ (X2 ∷ Bx0-1234 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-Xb-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ Bx0-1234 ∷ X2 ∷ []) (CCZ012 ∷ Toff034 ∷ X2 ∷ CZ01 ∷ CS34 ∷ CX13 ∷ CCZ012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ X2 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) (wp0009 c4) ▸
       at 1 2 (Toff034 ∷ X2 ∷ []) (sym (wp0010 c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ X2 ∷ CZ01 ∷ CS34 ∷ CX13 ∷ CCZ012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ X2 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ X2 ∷ CCZ134 ∷ X2 ∷ [])
  b1 = at 5 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0168 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 3 3 (X2 ∷ []) (wl0169 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 3 2 (Toff034 ∷ X2 ∷ []) (sym (wp0010 c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ X2 ∷ CCZ134 ∷ X2 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0170 (lit c4))) ▸ done


-- cQ @0210243143: 7 steps
lem-cQ-at0210243143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 4 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸ done


-- tP @0210243143: 7 steps
lem-tP-at0210243143 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0210243143 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸
       at 1 3 (Toff204 ∷ []) (wp0014 c4) ▸ done


-- VPQ @0210243143: 14 steps
lem-VPQ-at0210243143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done


-- QVQ @0210243143: 3 steps
lem-QVQ-at0210243143 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0210243143 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @0210243143: 12 steps
lem-box-cP-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0210243143 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done


-- Xb-box @0210243143: 18 steps
lem-Xb-box-at0210243143 : Ws → ⟪ (X4 ∷ Bx2-0413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CCZ024 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CCZ024 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0024 c4)) ▸ done


-- box-tQ @0210243143: 13 steps
lem-box-tQ-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0025 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0210243143 c4) ▸
       at 2 4 (Toff204 ∷ []) (wp0026 c4) ▸ done


-- t-cP @0210243143: 5 steps
lem-t-cP-at0210243143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (sym (wp0027 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸
       at 2 3 (CCZ024 ∷ Toff204 ∷ []) (sym (wp0028 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4) ▸ done


-- box2 @0210243143: 11 steps
lem-box2-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at0210243143 c4) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) []
  b1 = at 2 2 [] (wp0019 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0019 c4) ▸ done


-- F5-01: 112 steps
lem-F5-01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 4 2 (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) (wl0188 (lit c4)) ▸
       at 7 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 2 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4)) ▸
       at 4 2 (CX13 ∷ Toff314 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 5 2 (CS01 ∷ Toff314 ∷ []) (sym (wp0029 c4)) ▸
       at 6 2 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (sym (wp0030 c4)) ▸
       at 2 6 (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (sym (wp0031 c4)) ▸
       at 0 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-Xb-box-at0210243143 c4) ▸
       at 9 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b3 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b5 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 1 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 2 6 (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (wp0040 c4) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b7 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 3 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 15 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 14 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 13 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 12 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 10 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b11 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 5 5 (Toff314 ∷ CS01 ∷ CS03 ∷ []) (wp0043 c4) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 10 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 13 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸ done

  b12 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 11 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 10 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 7 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b13 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CS01 ∷ [])
  b13 = at 4 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 5 3 (Toff314 ∷ []) (wl0198 (lit c4)) ▸
       at 8 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 10 (CS01 ∷ []) (sym (wp0045 c4)) ▸ done


-- cQ @243243: 7 steps
lem-cQ-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 4 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸ done


-- tP @243243: 7 steps
lem-tP-at243243 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at243243 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done


-- VPQ @243243: 14 steps
lem-VPQ-at243243 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸ done


-- QVQ @243243: 3 steps
lem-QVQ-at243243 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at243243 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at243243 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @243243: 12 steps
lem-box-cP-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at243243 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done


-- Xb-box @243243: 18 steps
lem-Xb-box-at243243 : Ws → ⟪ (X4 ∷ Bx0-1423 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done


-- box-tQ @243243: 13 steps
lem-box-tQ-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (wp0056 c4) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at243243 c4) ▸
       at 2 4 (Toff014 ∷ []) (wp0057 c4) ▸ done


-- t-cP @243243: 5 steps
lem-t-cP-at243243 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-t-cP-at243243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (sym (wp0058 c4)) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4)) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸
       at 2 3 (CCZ014 ∷ Toff014 ∷ []) (sym (wp0059 c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4) ▸ done


-- box2 @243243: 11 steps
lem-box2-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 5 5 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) (lem-t-cP-at243243 c4) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) []
  b1 = at 2 2 [] (wp0051 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wp0051 c4) ▸ done


-- F5-12: 112 steps
lem-F5-12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl0211 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 4 2 (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) (wl0212 (lit c4)) ▸
       at 7 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 2 2 (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl0211 (lit c4)) ▸
       at 4 2 (CX23 ∷ Toff324 ∷ []) (sym (wl0213 (lit c4))) ▸
       at 5 2 (CS12 ∷ Toff324 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (sym (wl0215 (lit c4))) ▸
       at 2 6 (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (sym (wl0216 (lit c4))) ▸
       at 0 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b2 = at 8 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b3 = at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 10 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b5 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b5 = at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 2 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b6 = at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 1 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 2 6 (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (wl0218 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b7 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b8 = at 3 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 10 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 15 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 14 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 13 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b9 = at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 9 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 10 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 7 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b10 = at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸ done

  b11 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b11 = at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 5 5 (Toff324 ∷ CS12 ∷ CS13 ∷ []) (wl0223 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 10 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 13 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 12 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸ done

  b12 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b12 = at 11 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 7 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b13 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (CS12 ∷ [])
  b13 = at 4 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 5 3 (Toff324 ∷ []) (wp0073 c4) ▸
       at 8 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 10 (CS12 ∷ []) (sym (wl0224 (lit c4))) ▸ done


-- cQ @122441: 7 steps
lem-cQ-at122441 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at122441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 4 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸ done


-- tP @122441: 7 steps
lem-tP-at122441 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at122441 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at122441 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done


-- VPQ @122441: 14 steps
lem-VPQ-at122441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸ done


-- QVQ @122441: 3 steps
lem-QVQ-at122441 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at122441 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at122441 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @122441: 12 steps
lem-box-cP-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at122441 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done


-- Xb-box @122441: 18 steps
lem-Xb-box-at122441 : Ws → ⟪ (X4 ∷ Bx0-2431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX23 ∷ CCZ024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ Toff013 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX23 ∷ CCZ024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ Toff013 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done


-- box-tQ @122441: 13 steps
lem-box-tQ-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (wp0083 c4) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at122441 c4) ▸
       at 2 4 (Toff024 ∷ []) (wp0084 c4) ▸ done


-- t-cP @122441: 5 steps
lem-t-cP-at122441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-t-cP-at122441 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) (sym (wp0085 c4)) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4)) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸
       at 2 3 (CCZ024 ∷ Toff024 ∷ []) (sym (wp0086 c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4) ▸ done


-- box2 @122441: 11 steps
lem-box2-at122441 : Ws → ⟪ (Bx0-2431 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ []) (lem-t-cP-at122441 c4) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 3 2 [] (wl0230 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) []
  b1 = at 2 2 [] (wp0080 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸
       at 0 2 [] (wp0080 c4) ▸ done


-- F5-23: 112 steps
lem-F5-23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-23 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻0-2-1-3 ∷ []) (c₃ ((CS • CS • CS) ↑) (X ↑)) ▸
       at 4 2 (X4 ∷ CX31 ∷ Toff134 ∷ []) (wl0235 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb0-2-1-3 ∷ []) (c₃ (CS ↑) (X ↑)) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) (wl0236 (lit c4)) ▸
       at 7 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 2 2 (X4 ∷ CX31 ∷ Toff134 ∷ []) (wl0235 (lit c4)) ▸
       at 4 2 (CX31 ∷ Toff134 ∷ []) (sym (wl0237 (lit c4))) ▸
       at 5 2 (CS23 ∷ Toff134 ∷ []) (sym (wl0238 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) (sym (wl0239 (lit c4))) ▸
       at 2 6 (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (sym (wl0240 (lit c4))) ▸
       at 0 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4) ▸
       at 9 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b4 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 3 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b5 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 1 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b6 : Chain (Bx0-2431 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 2 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 2 6 (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (wl0243 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 6 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸ done

  b7 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ Toff013 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b7 = at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 6 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 5 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸ done

  b8 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ Toff013 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b8 = at 3 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 10 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 15 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 14 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 13 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 12 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b9 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 10 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b10 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b10 = at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸ done

  b11 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b11 = at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 5 5 (Toff134 ∷ CS12 ∷ CS23 ∷ []) (wl0248 (lit c4)) ▸
       at 11 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 10 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 9 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 13 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 12 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸ done

  b12 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b12 = at 11 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 10 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 10 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 8 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 7 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 5 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸ done

  b13 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (CS23 ∷ [])
  b13 = at 4 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 9 4 (CS23 ∷ CCZ234 ∷ []) (sym (wp0098 c4)) ▸
       at 5 3 (Toff134 ∷ []) (wp0099 c4) ▸
       at 1 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 2 [] (lem-box2-at122441 c4) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 10 (CS23 ∷ []) (sym (wl0249 (lit c4))) ▸ done


-- CXcb-box: 18 steps
lem-CXcb-box : Ws → ⟪ (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (Toff012 ∷ CCZ034 ∷ CX32 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ Toff012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ034 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CX32 ∷ Toff013 ∷ []) (wl0250 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) (sym (wp0100 c4)) ▸
       at 1 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0101 c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (Toff012 ∷ CS14 ∷ []) (wp0102 c4) ▸
       at 7 2 (Toff012 ∷ CX13 ∷ []) (wl0251 (lit c4)) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX32 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ Toff012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ034 ∷ CX32 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX13 ∷ []) (wl0251 (lit c4)) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Toff013 ∷ []) (sym (wl0252 (lit c4))) ▸
       at 2 2 (Toff012 ∷ CX32 ∷ Toff013 ∷ []) (wl0250 (lit c4)) ▸
       at 3 3 (CX32 ∷ []) (wl0253 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 3 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0101 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0254 (lit c4))) ▸ done


-- CXbc-box: 17 steps
lem-CXbc-box : Ws → ⟪ (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX23 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CX23 ∷ []) (wl0255 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0105 c4) ▸
       at 2 2 (Toff012 ∷ CX23 ∷ []) (wl0255 (lit c4)) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX23 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CX23 ∷ []) (Bx0-1234 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 3 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 4 3 (CX23 ∷ []) (wp0110 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

  b2 : Chain (Bx0-1234 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0257 (lit c4))) ▸ done


-- SWbc-box: 11 steps
lem-SWbc-box : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-SWbc-box c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (CX23 ∷ Bx0-1234 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CXbc-box c4) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ134 ∷ []) (lem-CXcb-box c4) ▸
       at 4 2 (CX23 ∷ CCZ124 ∷ []) (wl0260 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx0-1234 ∷ CX23 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (Bx0-1234 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0262 (lit c4)) ▸
       at 0 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CXbc-box c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc: 23 steps
lem-nat-SWbc : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-nat-SWbc c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ Sw23 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (wl0265 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸
       at 4 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 5 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ Sw23 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Sw23 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Sw23 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 7 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 8 2 (Toff013 ∷ Sw23 ∷ []) (wl0265 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 11 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸
       at 12 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Sw23 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Sw23 ∷ []) (Bx0-1324 ∷ [])
  b2 = at 13 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 15 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-024 ∷ []) (refl) ▸
       at 5 6 (Bx1-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


-- sym-bc: 2 steps
lem-sym-bc : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-bc c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (sym (lem-SWbc-box c4)) ▸
       at 0 3 (Bx0-1324 ∷ []) (lem-nat-SWbc c4) ▸ done


-- sym-ab: 18 steps
lem-sym-ab : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-ab c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 4 1 (Bx0-24 ∷ []) (refl) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ [])
  b1 = at 2 6 (Bx2-034 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸
       at 10 1 (Bx0-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (Bx0-2134 ∷ [])
  b2 = at 5 6 (Bx2-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done


-- P-box: 8 steps
lem-P-box : Ws → ⟪ (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-P-box c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (sym (wp0112 c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (sym (wp0113 c4)) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0114 c4)) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- cQ @13243142: 7 steps
lem-cQ-at13243142 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 4 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸ done


-- box-tQ @13243142: 13 steps
lem-box-tQ-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243142 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done


-- pairs: 4 steps
lem-pairs : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-pairs c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) (sym (lem-P-box c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done


-- box-perm-2134: 1 steps
lem-box-perm-2134 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-2134 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸ done


-- box-perm-1324: 1 steps
lem-box-perm-1324 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-box-perm-1324 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸ done


-- box-perm-3412: 1 steps
lem-box-perm-3412 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3412 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸ done


-- cQ @1221: 7 steps
lem-cQ-at1221 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸ done


-- box-tQ @1221: 13 steps
lem-box-tQ-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0160 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at1221 c4) ▸
       at 2 4 (Toff012 ∷ []) (wl0161 (lit c4)) ▸ done


-- CXbc-box @1221: 17 steps
lem-CXbc-box-at1221 : Ws → ⟪ (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX13 ∷ CCZ014 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4) ▸
       at 0 2 (Toff012 ∷ CX13 ∷ []) (wl0251 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (sym (wp0121 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0122 c4) ▸
       at 2 2 (Toff012 ∷ CX13 ∷ []) (wl0251 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX13 ∷ CCZ014 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX13 ∷ []) (Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 3 2 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (sym (wp0121 c4)) ▸
       at 4 3 (CX13 ∷ []) (wp0125 c4) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done

  b2 : Chain (Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0272 (lit c4))) ▸ done


-- CXcb-box @1221: 18 steps
lem-CXcb-box-at1221 : Ws → ⟪ (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) (Toff012 ∷ CCZ034 ∷ CX31 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ Toff012 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4) ▸
       at 0 2 (Toff012 ∷ CX31 ∷ Toff023 ∷ []) (wl0273 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) (sym (wp0126 c4)) ▸
       at 1 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 8 2 (Toff012 ∷ CS24 ∷ []) (wp0128 c4) ▸
       at 7 2 (Toff012 ∷ CX23 ∷ []) (wl0255 (lit c4)) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX31 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ Toff012 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ CX31 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX23 ∷ []) (wl0255 (lit c4)) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Toff023 ∷ []) (sym (wl0275 (lit c4))) ▸
       at 2 2 (Toff012 ∷ CX31 ∷ Toff023 ∷ []) (wl0273 (lit c4)) ▸
       at 3 3 (CX31 ∷ []) (wl0276 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-2134 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0277 (lit c4))) ▸ done


-- SWbc-box @1221: 11 steps
lem-SWbc-box-at1221 : Ws → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-SWbc-box-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (CX13 ∷ Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 1 3 (Bx0-2134 ∷ CCZ234 ∷ []) (lem-CXcb-box-at1221 c4) ▸
       at 4 2 (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4)) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸ done

  b1 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (Bx0-2134 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0282 (lit c4)) ▸
       at 0 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

