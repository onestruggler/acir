{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D044 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0433 ; wl0452 ; wl0508 ; wl0763 ; wl0765 ; wl0831 ; wl1321 ; wl1328 ; wl1329 ; wl1333 ; wl1334 ; wl1335 ; wp0090 ; wp0161 ; wp0272 ; wp0501 ; wp0687 ; wp0774 ; wp1056 ; wp1071 ; wp1143 ; wp1152 ; wp1171 ; wp1173 ; wp1174 ; wp1182 ; wp1183 ; wp1184 ; wp1185 ; wp1186 ; wp1187 ; wp1188 ; wp1189 ; wl0332 ; wl0451 ; wl0560 ; wl0760 ; wl0762 ; wl0898 ; wl1342 ; wl1343 ; wl1344 ; wl1345 ; wl1346 ; wl1347 ; wl1353 ; wl1354 ; wp0048 ; wp0301 ; wp0302 ; wp0543 ; wp0550 ; wp0686 ; wp0776 ; wp0923 ; wp1194 ; wp1195)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02142041 ; lem-box-tQ-at0314203241)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-box-cP-at0213243041 ; lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at02132031 ; lem-box-perm-2314-at0213243041)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at02142041 ; lem-box-perm-2314-at0312243041 ; lem-box-perm-3124-at02142041 ; lem-box-perm-3124-at0314203241 ; lem-box-perm-4123-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-box-1-at0213243041 ; lem-box-perm-1243-at03102132 ; lem-box-perm-1243-at0310213442 ; lem-box-perm-2341-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX30-TOFF214 ; lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX31-TOFF204)

-- Tu-box @0314203241: 83 steps
lem-Tu-box-at0314203241 : Ws → ⟪ (Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Bx2-4031 ∷ []) ⟫ʷ
lem-Tu-box-at0314203241 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ []) (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 0 2 (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) (wp1182 c4) ▸
       at 2 2 (CCZ123 ∷ CCZ134 ∷ Toff234 ∷ []) (sym (wl1333 (lit c4))) ▸
       at 4 2 (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) (wp1182 c4) ▸
       at 6 3 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl1334 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1056 c4) ▸
       at 5 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ CCZ134 ∷ []) (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (Toff204 ∷ CS34 ∷ []) (wp0501 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CS14⁻ ∷ []) (wp1183 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CS14 ∷ []) (wp1152 c4) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 6 3 (CCZ123 ∷ []) (sym (wl1335 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b2 = at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff204 ∷ Toff304 ∷ []) (sym (wp1184 c4)) ▸ done

  b3 : Chain (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b3 = at 4 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 1 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸
       at 1 1 (Bx2-4301 ∷ []) (lem-box-perm-1324-at02142041 c4) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 2 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸
       at 1 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 7 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸ done

  b4 : Chain (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b4 = at 6 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 3 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 1 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 2 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸ done

  b5 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ CCZ024 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b5 = at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸ done

  b6 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ CCZ024 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b6 = at 3 3 (Toff304 ∷ []) (wp1188 c4) ▸
       at 4 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b7 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (Bx2-4031 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b7 = at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸
       at 0 1 (Bx2-4031 ∷ []) (sym (lem-box-perm-1324-at02142041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b8 : Chain (Bx2-4031 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (Bx2-4031 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CCZ014 ∷ [])
  b8 = at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b9 : Chain (Bx2-4031 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CCZ014 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b9 = at 6 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-box-perm-3124-at02142041 c4) ▸
       at 1 1 (Bx3-2401 ∷ []) (lem-box-perm-3124-at0314203241 c4) ▸ done

  b10 : Chain (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-4021 ∷ Bx2-4031 ∷ [])
  b10 = at 0 2 (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-box-box-1-at0213243041 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-box-perm-2314-at0312243041 c4) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-box-perm-2314-at0213243041 c4) ▸ done

-- box-box-3 @03102132: 105 steps
lem-box-box-3-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-3-at03102132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-0124 ∷ Bx2-3014 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ023 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ [])
  b0 = at 0 1 (Bx3-0142 ∷ []) (lem-box-perm-1243-at03102132 c4) ▸
       at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 4 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 3 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 4 2 (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl1342 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 5 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ023 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 6 3 (Toff214 ∷ CCZ234 ∷ []) (wl1344 (lit c4)) ▸
       at 3 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ Toff214 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ [])
  b2 = at 2 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 4 2 (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1194 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸ done

  b3 : Chain (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ Toff214 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff214 ∷ CCZ234 ∷ [])
  b3 = at 4 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 3 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 4 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 10 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 9 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b4 : Chain (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff214 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff214 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 6 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 5 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 5 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 5 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 11 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸ done

  b5 : Chain (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff214 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ Bx2-3014 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 10 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 9 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 5 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 2 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸ done

  b6 : Chain (Toff301 ∷ CCZ234 ∷ Bx2-3014 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CCZ023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b6 = at 2 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 2 2 (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl1342 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 6 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸ done

  b7 : Chain (Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CCZ023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff301 ∷ Toff214 ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b7 = at 4 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 4 3 (Toff214 ∷ CCZ234 ∷ []) (wl1344 (lit c4)) ▸
       at 1 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 0 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 2 2 (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1194 c4) ▸ done

  b8 : Chain (CCZ023 ∷ Toff301 ∷ Toff214 ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff214 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b8 = at 1 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 7 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 3 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 1 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸ done

  b9 : Chain (CCZ023 ∷ Toff214 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CCZ023 ∷ CCZ014 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b9 = at 2 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b10 : Chain (CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CCZ023 ∷ CCZ014 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Toff214 ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b10 = at 3 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 3 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸ done

  b11 : Chain (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Toff214 ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3014 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b11 = at 6 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 3 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 4 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 6 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸ done

  b12 : Chain (Bx2-3014 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3014 ∷ Bx3-0142 ∷ [])
  b12 = at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

  b13 : Chain (Bx2-3014 ∷ Bx3-0142 ∷ []) (Bx2-3014 ∷ Bx3-0124 ∷ [])
  b13 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-1243-at0310213442 c4) ▸ done

-- box-box-1 @0312243041: 105 steps
lem-box-box-1-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-box-box-1-at0312243041 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-2401 ∷ Bx2-3401 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ Toff201 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-box-perm-2341-at0312243041 c4) ▸
       at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 4 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4)) ▸
       at 6 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 10 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ Toff201 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 6 3 (Toff201 ∷ CCZ123 ∷ []) (wl1354 (lit c4)) ▸
       at 3 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b2 = at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 4 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b3 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ CCZ123 ∷ [])
  b3 = at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸ done

  b4 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 4 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 5 3 (Toff304 ∷ []) (wp1188 c4) ▸
       at 6 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 5 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 11 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸ done

  b5 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ Bx2-3401 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 10 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 9 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 8 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 5 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 6 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 2 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸ done

  b6 : Chain (Toff304 ∷ CCZ123 ∷ Bx2-3401 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 2 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 1 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 2 2 (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b7 : Chain (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff304 ∷ Toff201 ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 3 (Toff201 ∷ CCZ123 ∷ []) (wl1354 (lit c4)) ▸
       at 1 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 2 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸ done

  b8 : Chain (CCZ234 ∷ Toff304 ∷ Toff201 ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 1 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 7 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 6 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 3 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 1 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸ done

  b9 : Chain (CCZ234 ∷ Toff201 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CCZ234 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 2 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CCZ234 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ Toff201 ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 3 3 (Toff304 ∷ []) (wp1188 c4) ▸
       at 4 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b11 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ Toff201 ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸ done

  b12 : Chain (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Bx3-4012 ∷ [])
  b12 = at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

  b13 : Chain (Bx2-3401 ∷ Bx3-4012 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b13 = at 1 1 (Bx3-2401 ∷ []) (lem-box-perm-4123-at0314203142 c4) ▸ done
