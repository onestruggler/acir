{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D032 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0263 ; wl1380 ; wp0066 ; wp0161 ; wl0214 ; wl0220 ; wl0221 ; wl0222 ; wp0053 ; wp0061 ; wp0065 ; wp0069 ; wp0070 ; wl0187 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0323 ; wl1182 ; wp0021 ; wp0032 ; wp0033 ; wp0034 ; wp0036 ; wp0037 ; wp0039 ; wp0041 ; wp0042 ; wp0044 ; wp0179 ; wp0651 ; wp0746 ; wp0905 ; wl0188 ; wl0189 ; wl0198 ; wl1411 ; wp0029 ; wp0030 ; wp0031 ; wp0038 ; wp1259 ; wp1260 ; wp1261 ; wp1262 ; wp1263 ; wl0211 ; wl0219 ; wl0314 ; wl1000 ; wl1113 ; wl1413 ; wp0060 ; wp0062 ; wp0064 ; wp0067 ; wp0068 ; wp0071 ; wp0072 ; wp0074 ; wp0265 ; wp0722 ; wl0212 ; wl0213 ; wl0215 ; wl0216 ; wl1414 ; wl1415 ; wl1416 ; wp0073 ; wp1265 ; wl1420 ; wp1267 ; wp1274 ; wl0807 ; wl0808 ; wl0921 ; wl1421 ; wl1422 ; wp0035 ; wp0760 ; wp1143 ; wp1275 ; wp1276 ; wp1277 ; wl1439 ; wl1441 ; wl1442 ; wl1443 ; wp1292 ; wp1294)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-K0 ; lem-F4-I-S0 ; lem-F4-K0-I ; lem-F4-K0-K0 ; lem-F4-K0-S0 ; lem-F4-S0-I ; lem-F4-S0-K0 ; lem-F4-S0-S0 ; lem-sym-ab-at03102132 ; lem-sym-ab-at032032 ; lem-sym-ab-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at03122130 ; lem-sym-ab-at0330 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at0310213442 ; lem-sym-ab-at0314213042 ; lem-sym-ab-at03203442 ; lem-sym-ab-at03243042 ; lem-sym-ab-at142142 ; lem-sym-ab-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-sym-bc-at03102132 ; lem-sym-bc-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at0214203143 ; lem-box-cP-at243243 ; lem-sym-bc-at0310243142 ; lem-sym-bc-at031031 ; lem-sym-bc-at132132 ; lem-sym-bc-at1331 ; lem-sym-bc-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-I-CS0 ; lem-F4-K0-CS0 ; lem-F4-S0-CS0 ; lem-Xb-box-at0210243143 ; lem-Xb-box-at243243 ; lem-box2-at0210243143 ; lem-box2-at243243 ; lem-pairs-at0310243142 ; lem-pairs-at0330 ; lem-pairs-at1331 ; lem-pairs-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-pairs-at031031 ; lem-pairs-at03243042 ; lem-pairs-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-box2-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-box-perm-1423-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX04-TOFF213 ; lem-comm-CX14-TOFF023 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX40-TOFF213)

-- box-perm-2341 @03122130: 4 steps
lem-box-perm-2341-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-box-perm-2341-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸
       at 0 1 (Bx3-1042 ∷ []) (lem-sym-ab-at0310213442 c4) ▸ done

-- box-perm-4123 @03203442: 4 steps
lem-box-perm-4123-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-box-perm-4123-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Bx3-0142 ∷ []) (lem-sym-ab-at03203442 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4) ▸ done

-- box-perm-4123 @032032: 4 steps
lem-box-perm-4123-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-4123-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4) ▸
       at 0 1 (Bx3-1402 ∷ []) (lem-pairs-at031031 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-sym-ab-at03243042 c4) ▸ done

-- box-perm-4123 @14213243: 4 steps
lem-box-perm-4123-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-4123-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym-bc-at243243 c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-pairs-at3443 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸ done

-- box-perm-2341 @0314213042: 4 steps
lem-box-perm-2341-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2341-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1402 ∷ []) (lem-sym-ab-at0314213042 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-pairs-at03243042 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸ done

-- box-perm-3241 @142142: 3 steps
lem-box-perm-3241-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3241-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-1432 ∷ []) (lem-sym-ab-at142142 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-pairs-at2442 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4) ▸ done

-- box-perm-4213 @132132: 3 steps
lem-box-perm-4213-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4213-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-pairs-at1331 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-ab-at2442 c4) ▸ done

-- S2-SBOX(0;2;43;1) @02132031: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at02132031 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ024 ∷ CS34 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 5 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 3 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 9 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ024 ∷ CS34 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 4 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 4 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 6 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸ done

  b3 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 12 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 11 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 10 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 7 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 5 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 11 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸ done

  b5 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 8 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ K3 ∷ CS14 ∷ CX31 ∷ CCZ024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 5 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 1 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 7 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸ done

  b7 : Chain (Bx2-0413 ∷ K3 ∷ CS14 ∷ CX31 ∷ CCZ024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ024 ∷ CS34 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 1 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 2 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 4 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ024 ∷ CS34 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ014 ∷ [])
  b10 = at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 0 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 2 2 [] (wp0161 c4) ▸
       at 0 8 (CCZ014 ∷ []) (sym (wp0905 c4)) ▸ done

-- F5-23 @02132031: 112 steps
lem-F5-23-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-23-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
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

  b2 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 11 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b3 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b5 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 4 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 2 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 2 6 (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) (wp1259 c4) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b7 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ Toff213 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS03 ∷ Toff213 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CCZ024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 3 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 15 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 14 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 13 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 12 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS14 ∷ CX31 ∷ CCZ024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 10 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 4 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b11 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 5 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 5 5 (Toff314 ∷ CS03 ∷ CS01 ∷ []) (wp1260 c4) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 10 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 13 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸ done

  b12 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 11 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 10 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 7 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b13 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CS01 ∷ [])
  b13 = at 4 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 9 4 (CS01 ∷ CCZ014 ∷ []) (sym (wp1261 c4)) ▸
       at 5 3 (Toff314 ∷ []) (wl0198 (lit c4)) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 10 (CS01 ∷ []) (sym (wp1262 c4)) ▸ done

-- S2-SBOX(0;2;43;1) @132132: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 9 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 3 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 4 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 4 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 6 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 12 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 11 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 10 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 6 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 7 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 5 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸ done

  b5 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 8 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 3 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ K3 ∷ CS24 ∷ CX32 ∷ CCZ014 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 5 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 1 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 5 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ K3 ∷ CS24 ∷ CX32 ∷ CCZ014 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 1 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 2 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 4 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CCZ014 ∷ CS34 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ124 ∷ [])
  b10 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 2 2 [] (wl0263 (lit c4)) ▸
       at 0 8 (CCZ124 ∷ []) (sym (wl1113 (lit c4))) ▸ done

-- F5-23 @132132: 112 steps
lem-F5-23-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-23-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
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

  b2 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b2 = at 8 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 11 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 9 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b3 = at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 10 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 9 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 7 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b5 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b5 = at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 4 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 2 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 1 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b6 = at 4 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 2 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 2 6 (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) (wl1414 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS13 ∷ Toff023 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b7 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS13 ∷ Toff023 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CCZ014 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b8 = at 3 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 10 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 9 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 15 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 14 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 13 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS24 ∷ CX32 ∷ CCZ014 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b9 = at 11 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 9 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 10 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 7 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 6 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b10 = at 4 1 (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1413 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸ done

  b11 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b11 = at 5 7 (Toff324 ∷ []) (wl1413 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 5 5 (Toff324 ∷ CS13 ∷ CS12 ∷ []) (wl1415 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 10 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 13 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 12 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸ done

  b12 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b12 = at 11 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 7 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b13 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (CS12 ∷ [])
  b13 = at 4 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 9 4 (CS12 ∷ CCZ124 ∷ []) (sym (wp1265 c4)) ▸
       at 5 3 (Toff324 ∷ []) (wp0073 c4) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 10 (CS12 ∷ []) (sym (wl1416 (lit c4))) ▸ done

-- ckt-Dinv: 73 steps
lem-ckt-Dinv : Ws → ⟪ (X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
lem-ckt-Dinv c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ K0 ∷ ι ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ [])
  b0 = at 0 1 (K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (sym (wl1420 (lit c4))) ▸
       at 8 1 (K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (sym (wl1420 (lit c4))) ▸
       at 0 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 4 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 3 4 (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S0-K0 c4)) ▸
       at 8 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 7 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S0-S0 c4)) ▸
       at 6 4 (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S0-K0 c4)) ▸ done

  b1 : Chain (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ K0 ∷ ι ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ [])
  b1 = at 12 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 11 4 (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-K0-S0 c4)) ▸
       at 10 4 (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-K0-S0 c4)) ▸
       at 9 4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-K0-K0 c4)) ▸
       at 16 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 15 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K0 c4)) ▸
       at 14 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S0 c4)) ▸
       at 13 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S0 c4)) ▸ done

  b2 : Chain (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ ι ∷ [])
  b2 = at 12 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K0 c4)) ▸
       at 23 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 27 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 26 4 (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S0-K0 c4)) ▸
       at 31 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4) ▸
       at 30 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-S0-S0 c4)) ▸
       at 29 4 (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S0-K0 c4)) ▸
       at 35 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸ done

  b3 : Chain (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ ι ∷ []) (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b3 = at 34 4 (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-K0-S0 c4)) ▸
       at 33 4 (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-K0-S0 c4)) ▸
       at 32 4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-K0-K0 c4)) ▸
       at 39 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 38 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K0 c4)) ▸
       at 37 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S0 c4)) ▸
       at 36 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-I-S0 c4)) ▸
       at 35 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K0 c4)) ▸ done

  b4 : Chain (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b4 = at 12 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K0 c4) ▸
       at 9 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-K0 c4) ▸
       at 6 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-K0 c4) ▸
       at 3 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-K0 c4) ▸
       at 0 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-K0 c4) ▸
       at 13 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S0 c4) ▸
       at 10 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-S0 c4) ▸
       at 7 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-S0 c4) ▸ done

  b5 : Chain (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b5 = at 4 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-S0 c4) ▸
       at 1 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-S0 c4) ▸
       at 14 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S0 c4) ▸
       at 11 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-S0 c4) ▸
       at 8 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-S0 c4) ▸
       at 5 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-S0 c4) ▸
       at 2 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-S0 c4) ▸
       at 15 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K0 c4) ▸ done

  b6 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b6 = at 12 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-K0 c4) ▸
       at 9 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-K0 c4) ▸
       at 6 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-K0 c4) ▸
       at 3 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-K0 c4) ▸
       at 16 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4) ▸
       at 13 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-I c4) ▸
       at 10 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-I c4) ▸
       at 7 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-I c4) ▸ done

  b7 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b7 = at 4 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-I c4) ▸
       at 17 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS0 c4) ▸
       at 14 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4) ▸
       at 11 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4) ▸
       at 8 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4) ▸
       at 5 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4) ▸
       at 18 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS0 c4) ▸
       at 15 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4) ▸ done

  b8 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b8 = at 12 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4) ▸
       at 9 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4) ▸
       at 6 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4) ▸
       at 19 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS0 c4) ▸
       at 16 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4) ▸
       at 13 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4) ▸
       at 10 4 (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4) ▸
       at 7 4 (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4) ▸ done

  b9 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  b9 = at 8 30 [] (wp1274 c4) ▸ done

-- S2-SBOX(0;2;43;1) @0213243140: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 : Ws → ⟪ (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 2 1 (CS34 ∷ []) (refl) ▸
       at 4 1 (CS34⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b1 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CCZ024 ∷ CS34⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b1 = at 5 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 4 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 9 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b2 = at 7 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 3 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 4 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 4 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 6 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸ done

  b3 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b3 = at 12 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 11 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 10 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 7 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸ done

  b4 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ024 ∷ Toff301 ∷ Toff213 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b4 = at 5 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸
       at 8 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 7 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 11 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸ done

  b5 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ Toff213 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b5 = at 8 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 6 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 3 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b6 : Chain (Bx2-4013 ∷ Toff301 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CS34 ∷ Toff213 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ K3 ∷ CS01 ∷ CX31 ∷ CCZ024 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b6 = at 5 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 2 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 1 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 7 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸ done

  b7 : Chain (Bx2-4013 ∷ K3 ∷ CS01 ∷ CX31 ∷ CCZ024 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b7 = at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 2 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸
       at 4 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b8 : Chain (Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CCZ024 ∷ CS03 ∷ K3⁻ ∷ Toff213 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff213 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b8 = at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸
       at 6 2 (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (sym (wl1421 (lit c4))) ▸ done

  b9 : Chain (Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff201 ∷ CCZ014 ∷ Toff213 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b9 = at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸ done

  b10 : Chain (Bx2-4013 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff201 ∷ CCZ014 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (CCZ014 ∷ [])
  b10 = at 5 3 (CCZ014 ∷ []) (sym (wp1275 c4)) ▸
       at 1 4 (Bx2-4013 ∷ []) (sym (lem-box-cP-at0214203143 c4)) ▸
       at 0 2 [] (lem-box2-at0214203143 c4) ▸
       at 0 3 (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) (wp1276 c4) ▸
       at 2 2 [] (wp0161 c4) ▸
       at 0 8 (CCZ014 ∷ []) (sym (wp1277 c4)) ▸ done

-- F4-K3-CS2 @0213243140: 19 steps
lem-F4-K3-CS2-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
  b0 = at 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 5 1 (CS34 ∷ []) (refl) ▸
       at 7 1 (CS34⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 1 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸ done

  b1 : Chain (CCZ234 ∷ X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1439 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 2 (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑)) ▸
       at 3 4 (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1439 (lit c4))) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸
       at 0 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1423-at0214203143 c4)) ▸
       at 1 7 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1292 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

-- F4-CS2-K3 @0213243140: 21 steps
lem-F4-CS2-K3-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (sym (wl1441 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1294 c4)) ▸
       at 1 1 (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 4 4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (sym (wl1442 (lit c4))) ▸ done

  b1 : Chain (X0 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx2-4301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 4 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 5 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 2 4 (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (sym (wl1442 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 2 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 3 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 4 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸ done

  b2 : Chain (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx2-4301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx2-4013 ∷ []) (sym (lem-box-perm-1423-at0214203143 c4)) ▸
       at 6 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-4-01-3 ∷ []) (refl) ▸
       at 0 4 (CK01 ∷ X0 ∷ []) (sym (wl1443 (lit c4))) ▸ done
