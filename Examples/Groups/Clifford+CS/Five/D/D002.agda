{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0156 ; wl0157 ; wl0158 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0167 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0225 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0245 ; wl0268 ; wl0269 ; wl0272 ; wl0277 ; wl0279 ; wl0281 ; wl0283 ; wl0284 ; wl0285 ; wl0286 ; wl0287 ; wl0288 ; wl0289 ; wl0290 ; wl0291 ; wl0292 ; wl0293 ; wl0294 ; wl0295 ; wl0296 ; wl0297 ; wl0298 ; wl0299 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0305 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0313 ; wl0314 ; wl0315 ; wl0316 ; wl0317 ; wl0318 ; wl0319 ; wl0320 ; wl0321 ; wl0322 ; wl0323 ; wl0324 ; wl0325 ; wl0326 ; wl0327 ; wl0328 ; wl0329 ; wl0330 ; wl0331 ; wl0332 ; wl0333 ; wl0334 ; wl0335 ; wl0336 ; wl0337 ; wl0338 ; wl0339 ; wl0340 ; wl0341 ; wl0342 ; wl0343 ; wp0001 ; wp0002 ; wp0003 ; wp0004 ; wp0005 ; wp0006 ; wp0007 ; wp0011 ; wp0021 ; wp0032 ; wp0039 ; wp0049 ; wp0050 ; wp0051 ; wp0075 ; wp0076 ; wp0077 ; wp0078 ; wp0079 ; wp0080 ; wp0083 ; wp0084 ; wp0097 ; wp0111 ; wp0112 ; wp0113 ; wp0114 ; wp0115 ; wp0116 ; wp0117 ; wp0118 ; wp0119 ; wp0130 ; wp0131 ; wp0132 ; wp0133 ; wp0134 ; wp0135 ; wp0136 ; wp0137 ; wp0138 ; wp0139 ; wp0140 ; wp0141 ; wp0142 ; wp0143 ; wp0144 ; wp0145 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0151 ; wp0152 ; wp0153 ; wp0154 ; wp0155 ; wp0156 ; wp0157 ; wp0158 ; wp0159 ; wp0160 ; wp0161 ; wp0162 ; wp0163 ; wp0164 ; wp0165 ; wp0166 ; wp0167 ; wp0168 ; wp0169 ; wp0170 ; wp0171 ; wp0172 ; wp0173 ; wp0174 ; wp0175 ; wp0176 ; wp0177 ; wp0178 ; wp0179 ; wp0180 ; wp0181 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0188 ; wp0189 ; wp0190 ; wp0191 ; wp0192 ; wp0193 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0198 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205 ; wp0206 ; wp0207 ; wp0208 ; wp0209 ; wp0210 ; wp0211 ; wp0212 ; wp0213 ; wp0214 ; wp0215)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-SWbc-box-at1221 ; lem-box-tQ-at1221 ; lem-box-tQ-at122441 ; lem-box-tQ-at13243142 ; lem-box-tQ-at243243 ; lem-cQ-at1221 ; lem-pairs ; lem-sym-ab ; lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd23-TOFF014 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ14-TOFF023 ; lem-comm-CZ23-CCZ014 ; lem-comm-CZ24-CCZ013 ; lem-comm-CZ24-TOFF013 ; lem-comm-SWAP13-BOX⟨0·24⟩ ; lem-comm-SWAP14-BOX⟨0·32⟩ ; lem-comm-TOFF013-CSd24 ; lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-TOFF024 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-SWAP13-BOX⟨0·42⟩ ; lem-comm-SWAP14-BOX⟨0·23⟩ ; lem-comm-SWAP24-BOX⟨0·31⟩ ; lem-comm-TOFF034-CSd12)
-- nat-SWbc @1221: 23 steps
lem-nat-SWbc-at1221 : Ws → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-nat-SWbc-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ Sw13 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 4 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 5 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ Sw13 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Sw13 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 7 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 8 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 12 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Sw13 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Sw13 ∷ []) (Bx0-2314 ∷ [])
  b2 = at 13 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 15 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-014 ∷ []) (refl) ▸
       at 5 6 (Bx2-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- sym-bc @1221: 2 steps
lem-sym-bc-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-bc-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at1221 c4)) ▸
       at 0 3 (Bx0-2314 ∷ []) (lem-nat-SWbc-at1221 c4) ▸ done


-- box-perm-2314: 2 steps
lem-box-perm-2314 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-box-perm-2314 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸ done


-- tP @1221: 7 steps
lem-tP-at1221 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at1221 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at1221 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff034 ∷ []) (wp0004 c4) ▸
       at 1 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸ done


-- P-box @1221: 8 steps
lem-P-box-at1221 : Ws → ⟪ (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-P-box-at1221 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at1221 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (sym (wp0112 c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at1221 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (sym (wp0113 c4)) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0114 c4)) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done


-- VPQ @1221: 14 steps
lem-VPQ-at1221 : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸ done


-- QVQ @1221: 3 steps
lem-QVQ-at1221 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at1221 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at1221 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @1221: 12 steps
lem-box-cP-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at1221 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at1221 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done


-- cQ @13243241: 7 steps
lem-cQ-at13243241 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at13243241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 4 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸ done


-- box-tQ @13243241: 13 steps
lem-box-tQ-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243241 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done


-- pairs @1221: 4 steps
lem-pairs-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-pairs-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) (sym (lem-P-box-at1221 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done


-- box-perm-3421: 2 steps
lem-box-perm-3421 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-box-perm-3421 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸ done


-- sym-ab @2332: 18 steps
lem-sym-ab-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-ab-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 4 1 (Bx0-34 ∷ []) (refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ [])
  b1 = at 2 6 (Bx3-024 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸
       at 10 1 (Bx0-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (Bx0-3124 ∷ [])
  b2 = at 5 6 (Bx3-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- box-perm-3124: 2 steps
lem-box-perm-3124 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3124 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸ done


-- cQ @2332: 7 steps
lem-cQ-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done


-- box-tQ @2332: 13 steps
lem-box-tQ-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (wl0290 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at2332 c4) ▸
       at 2 4 (Toff013 ∷ []) (wl0291 (lit c4)) ▸ done


-- tP @2332: 7 steps
lem-tP-at2332 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at2332 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at2332 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff024 ∷ []) (wp0078 c4) ▸
       at 1 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸ done


-- P-box @2332: 8 steps
lem-P-box-at2332 : Ws → ⟪ (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-P-box-at2332 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at2332 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (sym (wp0132 c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at2332 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (sym (wp0133 c4)) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0134 c4)) ▸
       at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-tQ-at2332 c4)) ▸ done


-- VPQ @2332: 14 steps
lem-VPQ-at2332 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸ done


-- QVQ @2332: 3 steps
lem-QVQ-at2332 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at2332 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at2332 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @2332: 12 steps
lem-box-cP-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at2332 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done


-- cQ @12243143: 7 steps
lem-cQ-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 4 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸ done


-- box-tQ @12243143: 13 steps
lem-box-tQ-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (wp0083 c4) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at12243143 c4) ▸
       at 2 4 (Toff024 ∷ []) (wp0084 c4) ▸ done


-- pairs @2332: 4 steps
lem-pairs-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-pairs-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) (sym (lem-P-box-at2332 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at2332 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸ done


-- box-perm-2413: 2 steps
lem-box-perm-2413 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-2413 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸ done


-- sym-ab @13243142: 18 steps
lem-sym-ab-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-ab-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (wp0136 c4) ▸
       at 4 1 (Bx0-42 ∷ []) (refl) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ [])
  b1 = at 2 6 (Bx4-012 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (wp0136 c4) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸
       at 10 1 (Bx0-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (Bx0-4312 ∷ [])
  b2 = at 5 6 (Bx4-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- box-perm-4312: 2 steps
lem-box-perm-4312 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-4312 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸ done


-- CXbc-box @13243142: 17 steps
lem-CXbc-box-at13243142 : Ws → ⟪ (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX41 ∷ CCZ024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ012 ∷ CX34 ∷ CS23 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ CX41 ∷ []) (wp0137 c4) ▸
       at 1 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (sym (wp0138 c4)) ▸
       at 3 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0139 c4) ▸
       at 2 2 (Toff034 ∷ CX41 ∷ []) (wp0137 c4) ▸
       at 5 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX41 ∷ CCZ024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ012 ∷ CX34 ∷ CS23 ∷ CX41 ∷ []) (Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS24⁻ ∷ []) (sym (wp0140 c4)) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 3 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (sym (wp0138 c4)) ▸
       at 4 3 (CX41 ∷ []) (wp0143 c4) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done

  b2 : Chain (Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0295 (lit c4))) ▸ done


-- CXcb-box @13243142: 18 steps
lem-CXcb-box-at13243142 : Ws → ⟪ (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) (Toff034 ∷ CCZ012 ∷ CX14 ∷ Toff013 ∷ CS12 ∷ CX31 ∷ Toff034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ012 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ CX14 ∷ Toff013 ∷ []) (wp0144 c4) ▸
       at 2 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX14 ∷ []) (sym (wp0145 c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 7 2 (Toff034 ∷ CX31 ∷ []) (wp0147 c4) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX14 ∷ Toff013 ∷ CS12 ∷ CX31 ∷ Toff034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ012 ∷ CX14 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX31 ∷ []) (wp0147 c4) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 2 2 (Toff034 ∷ CX14 ∷ Toff013 ∷ []) (wp0144 c4) ▸
       at 3 3 (CX14 ∷ []) (wp0148 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX14 ∷ []) (sym (wp0145 c4)) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0299 (lit c4))) ▸ done


-- SWbc-box @13243142: 11 steps
lem-SWbc-box-at13243142 : Ws → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-SWbc-box-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (CX41 ∷ Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CXbc-box-at13243142 c4) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 1 3 (Bx0-3412 ∷ CCZ123 ∷ []) (lem-CXcb-box-at13243142 c4) ▸
       at 4 2 (CX41 ∷ CCZ234 ∷ []) (wl0302 (lit c4)) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 2 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸ done

  b1 : Chain (CX41 ∷ Bx0-3412 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (Bx0-3412 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0304 (lit c4)) ▸
       at 0 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CXbc-box-at13243142 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done


-- nat-SWbc @13243142: 23 steps
lem-nat-SWbc-at13243142 : Ws → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ Sw14 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 1 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 3 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 4 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 5 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ Sw14 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Sw14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 7 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 8 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 9 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 12 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Sw14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Sw14 ∷ []) (Bx0-3142 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 14 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 15 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-042 ∷ []) (refl) ▸
       at 5 6 (Bx3-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- sym-bc @13243142: 2 steps
lem-sym-bc-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-bc-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at13243142 c4)) ▸
       at 0 3 (Bx0-3142 ∷ []) (lem-nat-SWbc-at13243142 c4) ▸ done


-- box-perm-3142: 2 steps
lem-box-perm-3142 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3142 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸ done


-- sym-ab @122331: 18 steps
lem-sym-ab-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym-ab-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (sym (wp0154 c4)) ▸
       at 4 1 (Bx0-34 ∷ []) (refl) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ [])
  b1 = at 2 6 (Bx3-014 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (sym (wp0154 c4)) ▸
       at 7 1 (Bx0-34 ∷ []) (refl) ▸
       at 10 1 (Bx0-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (Bx0-3214 ∷ [])
  b2 = at 5 6 (Bx3-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- box-perm-3214: 3 steps
lem-box-perm-3214 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-box-perm-3214 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸ done


-- cQ @122331: 7 steps
lem-cQ-at122331 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸ done


-- box-tQ @122331: 13 steps
lem-box-tQ-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (wl0308 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at122331 c4) ▸
       at 2 4 (Toff023 ∷ []) (wl0309 (lit c4)) ▸ done


-- tP @122331: 7 steps
lem-tP-at122331 : Ws → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at122331 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at122331 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff014 ∷ []) (wp0049 c4) ▸
       at 1 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸ done


-- P-box @122331: 8 steps
lem-P-box-at122331 : Ws → ⟪ (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-P-box-at122331 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at122331 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (sym (wp0158 c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at122331 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ14 ∷ []) (sym (wp0159 c4)) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0160 c4)) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done


-- VPQ @122331: 14 steps
lem-VPQ-at122331 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (sym (wl0202 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸ done


-- QVQ @122331: 3 steps
lem-QVQ-at122331 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at122331 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at122331 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done


-- box-cP @122331: 12 steps
lem-box-cP-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2314 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (wp0153 c4) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at122331 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4) ▸
       at 2 2 [] (wl0203 (lit c4)) ▸ done


-- pairs @122331: 4 steps
lem-pairs-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-pairs-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) (sym (lem-P-box-at122331 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at122331 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done


-- box-perm-1423: 3 steps
lem-box-perm-1423 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1423 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸ done


-- sym-ab @13243241: 18 steps
lem-sym-ab-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-sym-ab-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 4 1 (Bx0-41 ∷ []) (refl) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ [])
  b1 = at 2 6 (Bx4-021 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 7 1 (Bx0-41 ∷ []) (refl) ▸
       at 10 1 (Bx0-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (Bx0-4321 ∷ [])
  b2 = at 5 6 (Bx4-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- box-perm-4321: 3 steps
lem-box-perm-4321 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-box-perm-4321 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-ab-at13243241 c4) ▸ done


-- CXbc-box @13243241: 17 steps
lem-CXbc-box-at13243241 : Ws → ⟪ (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX42 ∷ CCZ014 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ012 ∷ CX34 ∷ CS13 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ CX42 ∷ []) (wp0163 c4) ▸
       at 1 2 (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (sym (wp0164 c4)) ▸
       at 3 2 (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0165 c4) ▸
       at 2 2 (Toff034 ∷ CX42 ∷ []) (wp0163 c4) ▸
       at 5 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0310 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX42 ∷ CCZ014 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CCZ012 ∷ CX34 ∷ CS13 ∷ CX42 ∷ []) (Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS14⁻ ∷ []) (sym (wp0166 c4)) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 3 2 (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (sym (wp0164 c4)) ▸
       at 4 3 (CX42 ∷ []) (wp0168 c4) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done

  b2 : Chain (Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-3421 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0312 (lit c4))) ▸ done


-- CXcb-box @13243241: 18 steps
lem-CXcb-box-at13243241 : Ws → ⟪ (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) (Toff034 ∷ CCZ012 ∷ CX24 ∷ Toff023 ∷ CS12 ∷ CX32 ∷ Toff034 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ012 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ CX24 ∷ Toff023 ∷ []) (wp0169 c4) ▸
       at 2 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0313 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX24 ∷ []) (sym (wp0170 c4)) ▸
       at 4 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 7 2 (Toff034 ∷ CX32 ∷ []) (wp0172 c4) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX24 ∷ Toff023 ∷ CS12 ∷ CX32 ∷ Toff034 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ CCZ012 ∷ CX24 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX32 ∷ []) (wp0172 c4) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff023 ∷ []) (wp0173 c4) ▸
       at 2 2 (Toff034 ∷ CX24 ∷ Toff023 ∷ []) (wp0169 c4) ▸
       at 3 3 (CX24 ∷ []) (wp0174 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX24 ∷ []) (sym (wp0170 c4)) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-3421 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0315 (lit c4))) ▸ done


-- SWbc-box @13243241: 11 steps
lem-SWbc-box-at13243241 : Ws → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-SWbc-box-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (CX42 ∷ Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx0-3421 ∷ CCZ134 ∷ []) (lem-CXbc-box-at13243241 c4) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 1 3 (Bx0-3421 ∷ CCZ123 ∷ []) (lem-CXcb-box-at13243241 c4) ▸
       at 4 2 (CX42 ∷ CCZ134 ∷ []) (wl0318 (lit c4)) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 2 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸ done

  b1 : Chain (CX42 ∷ Bx0-3421 ∷ CX42 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (Bx0-3421 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0320 (lit c4)) ▸
       at 0 3 (Bx0-3421 ∷ CCZ134 ∷ []) (lem-CXbc-box-at13243241 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @13243241: 23 steps
lem-nat-SWbc-at13243241 : Ws → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ Sw24 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 1 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 3 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 4 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 5 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ Sw24 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Sw24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 7 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 8 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 9 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 12 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Sw24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Sw24 ∷ []) (Bx0-3241 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 14 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 15 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx3-041 ∷ []) (refl) ▸
       at 5 6 (Bx3-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- sym-bc @13243241: 2 steps
lem-sym-bc-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-bc-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at13243241 c4)) ▸
       at 0 3 (Bx0-3241 ∷ []) (lem-nat-SWbc-at13243241 c4) ▸ done


-- box-perm-3241: 3 steps
lem-box-perm-3241 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-box-perm-3241 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4) ▸ done


-- cQ @132132: 7 steps
lem-cQ-at132132 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸ done


-- box-tQ @132132: 13 steps
lem-box-tQ-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (wl0290 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at132132 c4) ▸
       at 2 4 (Toff013 ∷ []) (wl0291 (lit c4)) ▸ done


-- tP @132132: 7 steps
lem-tP-at132132 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at132132 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at132132 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff024 ∷ []) (wp0078 c4) ▸
       at 1 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸ done


-- P-box @132132: 8 steps
lem-P-box-at132132 : Ws → ⟪ (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-P-box-at132132 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at132132 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (sym (wp0132 c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at132132 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (sym (wp0133 c4)) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0134 c4)) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸ done


-- VPQ @132132: 14 steps
lem-VPQ-at132132 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸ done


-- QVQ @132132: 3 steps
lem-QVQ-at132132 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at132132 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at132132 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @132132: 12 steps
lem-box-cP-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at132132 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done


-- pairs @132132: 4 steps
lem-pairs-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-pairs-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) (sym (lem-P-box-at132132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done


-- box-perm-2431: 3 steps
lem-box-perm-2431 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-2431 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-pairs-at132132 c4) ▸ done


-- sym-ab @12243143: 18 steps
lem-sym-ab-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-ab-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (wp0180 c4) ▸
       at 4 1 (Bx0-43 ∷ []) (refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ [])
  b1 = at 2 6 (Bx4-013 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (wp0180 c4) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸
       at 10 1 (Bx0-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (Bx0-4213 ∷ [])
  b2 = at 5 6 (Bx4-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- box-perm-4213: 3 steps
lem-box-perm-4213 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-4213 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-ab-at12243143 c4) ▸ done


-- CXbc-box @12243143: 17 steps
lem-CXbc-box-at12243143 : Ws → ⟪ (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX41 ∷ CCZ034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CCZ013 ∷ CX24 ∷ CS23 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at12243143 c4) ▸
       at 0 2 (Toff024 ∷ CX41 ∷ []) (wp0181 c4) ▸
       at 1 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (sym (wp0182 c4)) ▸
       at 3 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0183 c4) ▸
       at 2 2 (Toff024 ∷ CX41 ∷ []) (wp0181 c4) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX41 ∷ CCZ034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CCZ013 ∷ CX24 ∷ CS23 ∷ CX41 ∷ []) (Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 3 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (sym (wp0182 c4)) ▸
       at 4 3 (CX41 ∷ []) (wp0187 c4) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸ done

  b2 : Chain (Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0295 (lit c4))) ▸ done


-- CXcb-box @12243143: 18 steps
lem-CXcb-box-at12243143 : Ws → ⟪ (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) (Toff024 ∷ CCZ013 ∷ CX14 ∷ Toff012 ∷ CS13 ∷ CX21 ∷ Toff024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ013 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at12243143 c4) ▸
       at 0 2 (Toff024 ∷ CX14 ∷ Toff012 ∷ []) (wp0188 c4) ▸
       at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 7 2 (Toff024 ∷ CX21 ∷ []) (wp0191 c4) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX14 ∷ Toff012 ∷ CS13 ∷ CX21 ∷ Toff024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ013 ∷ CX14 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX21 ∷ []) (wp0191 c4) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff012 ∷ []) (wp0192 c4) ▸
       at 2 2 (Toff024 ∷ CX14 ∷ Toff012 ∷ []) (wp0188 c4) ▸
       at 3 3 (CX14 ∷ []) (wp0193 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0299 (lit c4))) ▸ done


-- SWbc-box @12243143: 11 steps
lem-SWbc-box-at12243143 : Ws → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-SWbc-box-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (CX41 ∷ Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 1 3 (Bx0-2413 ∷ CCZ123 ∷ []) (lem-CXcb-box-at12243143 c4) ▸
       at 4 2 (CX41 ∷ CCZ234 ∷ []) (wl0302 (lit c4)) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 2 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸ done

  b1 : Chain (CX41 ∷ Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (Bx0-2413 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0304 (lit c4)) ▸
       at 0 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done


-- nat-SWbc @12243143: 23 steps
lem-nat-SWbc-at12243143 : Ws → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-nat-SWbc-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ Sw14 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 1 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 3 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 4 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 5 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ Sw14 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Sw14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 7 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 9 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 11 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 12 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Sw14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Sw14 ∷ []) (Bx0-2143 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 14 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 15 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-043 ∷ []) (refl) ▸
       at 5 6 (Bx2-043 ∷ []) (refl) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- sym-bc @12243143: 2 steps
lem-sym-bc-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym-bc-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at12243143 c4)) ▸
       at 0 3 (Bx0-2143 ∷ []) (lem-nat-SWbc-at12243143 c4) ▸ done


-- box-perm-2143: 3 steps
lem-box-perm-2143 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-2143 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4) ▸ done


-- cQ @14233142: 7 steps
lem-cQ-at14233142 : Ws → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 4 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (sym (wl0328 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸ done


-- box-tQ @14233142: 13 steps
lem-box-tQ-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233142 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done


-- CXbc-box @14233142: 17 steps
lem-CXbc-box-at14233142 : Ws → ⟪ (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX31 ∷ CCZ023 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CCZ012 ∷ CX43 ∷ CS24 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233142 c4) ▸
       at 0 2 (Toff034 ∷ CX31 ∷ []) (wp0147 c4) ▸
       at 1 2 (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) (sym (wl0329 (lit c4))) ▸
       at 3 2 (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) (wp0199 c4) ▸
       at 2 2 (Toff034 ∷ CX31 ∷ []) (wp0147 c4) ▸
       at 5 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 8 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX31 ∷ CCZ023 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CCZ012 ∷ CX43 ∷ CS24 ∷ CX31 ∷ []) (Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS23⁻ ∷ []) (sym (wl0331 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 5 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ023 ∷ []) (sym (wl0332 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) (sym (wl0329 (lit c4))) ▸
       at 4 3 (CX31 ∷ []) (wl0333 (lit c4)) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done

  b2 : Chain (Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-4312 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0277 (lit c4))) ▸ done


-- CXcb-box @14233142: 18 steps
lem-CXcb-box-at14233142 : Ws → ⟪ (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) (Toff034 ∷ CCZ012 ∷ CX13 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ Toff034 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ012 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233142 c4) ▸
       at 0 2 (Toff034 ∷ CX13 ∷ Toff014 ∷ []) (wp0200 c4) ▸
       at 2 2 (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) (sym (wp0201 c4)) ▸
       at 1 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS24 ∷ []) (wp0202 c4) ▸
       at 7 2 (Toff034 ∷ CX41 ∷ []) (wp0137 c4) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX13 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ Toff034 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ012 ∷ CX13 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX41 ∷ []) (wp0137 c4) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff014 ∷ []) (wp0203 c4) ▸
       at 2 2 (Toff034 ∷ CX13 ∷ Toff014 ∷ []) (wp0200 c4) ▸
       at 3 3 (CX13 ∷ []) (wp0204 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ124 ∷ []) (sym (wp0205 c4)) ▸
       at 3 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-4312 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0272 (lit c4))) ▸ done


-- SWbc-box @14233142: 11 steps
lem-SWbc-box-at14233142 : Ws → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-SWbc-box-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (CX31 ∷ Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-CXbc-box-at14233142 c4) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 1 3 (Bx0-4312 ∷ CCZ124 ∷ []) (lem-CXcb-box-at14233142 c4) ▸
       at 4 2 (CX31 ∷ CCZ234 ∷ []) (wl0336 (lit c4)) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸ done

  b1 : Chain (CX31 ∷ Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (Bx0-4312 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0337 (lit c4)) ▸
       at 0 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-CXbc-box-at14233142 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done


-- nat-SWbc @14233142: 23 steps
lem-nat-SWbc-at14233142 : Ws → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-nat-SWbc-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ Sw13 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 1 2 (Toff014 ∷ Sw13 ∷ []) (wp0207 c4) ▸
       at 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 3 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸
       at 4 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 5 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ Sw13 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ Sw13 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Sw13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 7 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 8 2 (Toff014 ∷ Sw13 ∷ []) (wp0207 c4) ▸
       at 9 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 11 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸
       at 12 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Sw13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Sw13 ∷ []) (Bx0-4132 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸
       at 14 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 15 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx4-032 ∷ []) (refl) ▸
       at 5 6 (Bx4-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- sym-bc @14233142: 2 steps
lem-sym-bc-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-bc-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at14233142 c4)) ▸
       at 0 3 (Bx0-4132 ∷ []) (lem-nat-SWbc-at14233142 c4) ▸ done


-- box-perm-4132: 3 steps
lem-box-perm-4132 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4132 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-bc-at14233142 c4) ▸ done


-- tP @14233142: 7 steps
lem-tP-at14233142 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done


-- P-box @14233142: 8 steps
lem-P-box-at14233142 : Ws → ⟪ (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-P-box-at14233142 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233142 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233142 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (sym (wl0338 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233142 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (sym (wl0339 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done


-- VPQ @14233142: 14 steps
lem-VPQ-at14233142 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸ done


-- QVQ @14233142: 3 steps
lem-QVQ-at14233142 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at14233142 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @14233142: 12 steps
lem-box-cP-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233142 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233142 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done


-- cQ @3443: 7 steps
lem-cQ-at3443 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done


-- box-tQ @3443: 13 steps
lem-box-tQ-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0160 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at3443 c4) ▸
       at 2 4 (Toff012 ∷ []) (wl0161 (lit c4)) ▸ done


-- pairs @14233142: 4 steps
lem-pairs-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-pairs-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (sym (lem-P-box-at14233142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233142 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done


-- box-perm-1243: 3 steps
lem-box-perm-1243 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1243 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4) ▸ done


-- sym-ab @13213442: 18 steps
lem-sym-ab-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-ab-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 4 1 (Bx0-12 ∷ []) (refl) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ [])
  b1 = at 2 6 (Bx1-042 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (sym (wp0212 c4)) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸
       at 10 1 (Bx0-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (Bx0-1342 ∷ [])
  b2 = at 5 6 (Bx1-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- box-perm-1342: 3 steps
lem-box-perm-1342 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1342 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4) ▸ done


-- cQ @13213442: 7 steps
lem-cQ-at13213442 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸ done


-- box-tQ @13213442: 13 steps
lem-box-tQ-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (wl0290 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at13213442 c4) ▸
       at 2 4 (Toff013 ∷ []) (wl0291 (lit c4)) ▸ done


-- tP @13213442: 7 steps
lem-tP-at13213442 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at13213442 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at13213442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff024 ∷ []) (wp0078 c4) ▸
       at 1 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸ done


-- P-box @13213442: 8 steps
lem-P-box-at13213442 : Ws → ⟪ (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-P-box-at13213442 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at13213442 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (sym (wp0132 c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at13213442 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (sym (wp0133 c4)) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0134 c4)) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done


-- VPQ @13213442: 14 steps
lem-VPQ-at13213442 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸ done


-- QVQ @13213442: 3 steps
lem-QVQ-at13213442 : Ws → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at13213442 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @13213442: 12 steps
lem-box-cP-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at13213442 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4) ▸
       at 2 2 [] (wl0229 (lit c4)) ▸ done


-- cQ @1441: 7 steps
lem-cQ-at1441 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at1441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 4 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS02⁻ ∷ []) (sym (wl0342 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸ done


-- box-tQ @1441: 13 steps
lem-box-tQ-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4231 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (wp0083 c4) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at1441 c4) ▸
       at 2 4 (Toff024 ∷ []) (wp0084 c4) ▸ done


-- pairs @13213442: 4 steps
lem-pairs-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-pairs-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) (sym (lem-P-box-at13213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done


-- box-perm-4231: 3 steps
lem-box-perm-4231 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-box-perm-4231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸
       at 0 1 (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4) ▸ done


-- cQ @1331: 7 steps
lem-cQ-at1331 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at1331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸ done


-- box-tQ @1331: 13 steps
lem-box-tQ-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (wl0308 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at1331 c4) ▸
       at 2 4 (Toff023 ∷ []) (wl0309 (lit c4)) ▸ done


-- tP @1331: 7 steps
lem-tP-at1331 : Ws → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at1331 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at1331 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff014 ∷ []) (wp0049 c4) ▸
       at 1 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸ done


-- P-box @1331: 8 steps
lem-P-box-at1331 : Ws → ⟪ (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-P-box-at1331 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4) ▸
       at 0 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at1331 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (sym (wp0158 c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at1331 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ14 ∷ []) (sym (wp0159 c4)) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0160 c4)) ▸
       at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸ done

