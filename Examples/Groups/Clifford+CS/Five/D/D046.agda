{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D046 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0263 ; wl0298 ; wl0334 ; wl0348 ; wl0452 ; wl0492 ; wl0499 ; wl0501 ; wl0508 ; wl0616 ; wl0620 ; wl0621 ; wl0765 ; wl0778 ; wl0871 ; wl1213 ; wl1256 ; wl1324 ; wl1347 ; wl1356 ; wl1380 ; wl1395 ; wp0003 ; wp0103 ; wp0108 ; wp0161 ; wp0221 ; wp0302 ; wp0341 ; wp0342 ; wp0357 ; wp0513 ; wp0559 ; wp0562 ; wp0575 ; wp0822 ; wp0948 ; wp1114 ; wp1150 ; wp1173 ; wp1174 ; wp1193 ; wp1219 ; wp1220 ; wp1221 ; wp1222 ; wp1239 ; wp1240 ; wl1409 ; wl1410 ; wl1411 ; wl1412 ; wp1263)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-K2 ; lem-F4-I-S3 ; lem-F4-K2-K2 ; lem-F4-S3-I ; lem-F4-S3-K2 ; lem-F4-S3-S3)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K2-at02132031 ; lem-F4-I-S3-at02132031 ; lem-F4-K2-K2-at02132031 ; lem-F4-S3-I-at02132031 ; lem-F4-S3-K2-at02132031 ; lem-F4-S3-S3-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at03203442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at02132130 ; lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S3 ; lem-F4-I-CS2 ; lem-F4-K2-CS2 ; lem-F4-S3-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F4-CS2-K2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-2341-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-K2-at02132031 ; lem-F4-CS2-S3-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-K2-CS2-at02132031 ; lem-F4-S3-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at02132031 ; lem-box-perm-2341-at03122130 ; lem-box-perm-4123-at03203442 ; lem-box-perm-4123-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS04-CCZ123 ; lem-comm-CSd04-CCZ123 ; lem-comm-CX04-TOFF312 ; lem-comm-CX41-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX31-TOFF204)

-- box-box-1 @03122130: 105 steps
lem-box-box-1-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-box-box-1-at03122130 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-2104 ∷ Bx2-3104 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ123 ∷ CX30 ∷ CS34 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Bx3-1042 ∷ []) (lem-box-perm-2341-at03122130 c4) ▸
       at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03203442 c4) ▸
       at 4 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 3 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp0559 c4) ▸
       at 6 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 10 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 9 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ123 ∷ CX30 ∷ CS34 ∷ Toff204 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 7 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 5 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 6 3 (Toff204 ∷ CCZ234 ∷ []) (wp1219 c4) ▸
       at 3 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸
       at 3 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ Toff204 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ [])
  b2 = at 2 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 9 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸
       at 8 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸ done

  b3 : Chain (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ Toff204 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CS04 ∷ CCZ123 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ Toff204 ∷ CCZ234 ∷ [])
  b3 = at 4 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 3 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸
       at 4 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 6 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 10 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 9 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸ done

  b4 : Chain (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CS04 ∷ CCZ123 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ Toff204 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff204 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 6 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 5 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 5 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 5 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 11 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸ done

  b5 : Chain (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff204 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ Bx2-3104 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 10 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 9 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 5 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸
       at 6 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 2 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸ done

  b6 : Chain (Toff301 ∷ CCZ234 ∷ Bx2-3104 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CCZ123 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ Toff204 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b6 = at 2 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 1 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp0559 c4) ▸
       at 4 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 8 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸ done

  b7 : Chain (Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CCZ123 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ Toff204 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff301 ∷ Toff204 ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b7 = at 4 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 3 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 4 3 (Toff204 ∷ CCZ234 ∷ []) (wp1219 c4) ▸
       at 1 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 0 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4) ▸ done

  b8 : Chain (CCZ123 ∷ Toff301 ∷ Toff204 ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff204 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b8 = at 1 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 7 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸
       at 6 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 3 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 1 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸ done

  b9 : Chain (CCZ123 ∷ Toff204 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CCZ123 ∷ CCZ014 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b9 = at 2 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 8 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 4 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸ done

  b10 : Chain (CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CCZ123 ∷ CCZ014 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ Toff204 ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b10 = at 3 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 3 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 9 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸
       at 8 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸ done

  b11 : Chain (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ Toff204 ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3104 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CCZ234 ∷ CS14 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b11 = at 6 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 3 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸
       at 4 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸
       at 2 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 6 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸ done

  b12 : Chain (Bx2-3104 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CCZ234 ∷ CS14 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3104 ∷ Bx3-1042 ∷ [])
  b12 = at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-1042 ∷ []) (sym (lem-box-tQ-at03203442 c4)) ▸ done

  b13 : Chain (Bx2-3104 ∷ Bx3-1042 ∷ []) (Bx2-3104 ∷ Bx3-2104 ∷ [])
  b13 = at 1 1 (Bx3-2104 ∷ []) (lem-box-perm-4123-at03203442 c4) ▸ done

-- box-box-1 @13243142: 105 steps
lem-box-box-1-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-box-box-1-at13243142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-3412 ∷ Bx3-0412 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-box-perm-2341-at13243142 c4) ▸
       at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 3 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 4 2 (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1213 (lit c4)) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 9 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ [])
  b1 = at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 6 3 (Toff312 ∷ CCZ023 ∷ []) (wl1395 (lit c4)) ▸
       at 3 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ [])
  b2 = at 2 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 4 2 (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4)) ▸
       at 3 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 9 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b3 : Chain (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff312 ∷ CCZ023 ∷ [])
  b3 = at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 3 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 4 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 6 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 9 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b4 : Chain (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff312 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ [])
  b4 = at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 4 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 5 3 (Toff014 ∷ []) (wp1240 c4) ▸
       at 6 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 5 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 11 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸ done

  b5 : Chain (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Bx3-0412 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b5 = at 10 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 6 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b6 : Chain (Toff014 ∷ CCZ023 ∷ Bx3-0412 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b6 = at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 2 2 (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1213 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b7 : Chain (Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff014 ∷ Toff312 ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b7 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 4 3 (Toff312 ∷ CCZ023 ∷ []) (wl1395 (lit c4)) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 2 2 (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4)) ▸ done

  b8 : Chain (CCZ034 ∷ Toff014 ∷ Toff312 ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b8 = at 1 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 7 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸
       at 6 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 1 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b9 = at 2 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸ done

  b10 : Chain (CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b10 = at 3 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 2 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 3 3 (Toff014 ∷ []) (wp1240 c4) ▸
       at 4 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 3 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 9 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b11 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx3-0412 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CCZ023 ∷ CS24 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b11 = at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 3 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 4 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸ done

  b12 : Chain (Bx3-0412 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CCZ023 ∷ CS24 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx3-0412 ∷ Bx0-4123 ∷ [])
  b12 = at 5 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done

  b13 : Chain (Bx3-0412 ∷ Bx0-4123 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  b13 = at 1 1 (Bx0-3412 ∷ []) (lem-box-perm-4123-at14213243 c4) ▸ done

-- deb-P-hi-split-a: 136 steps
lem-deb-P-hi-split-a : Ws → ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-hi-split-a c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 3 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 11 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b1 = at 10 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 9 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b2 = at 19 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 18 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 17 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 16 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 24 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 23 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 22 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b3 = at 21 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 19 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 18 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 28 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 27 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 26 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 25 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b4 = at 24 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 23 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 22 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 21 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 32 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 29 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 27 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 26 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 25 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 24 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 36 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 35 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 34 4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-K2-K2 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b6 = at 33 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 32 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 31 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 30 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 29 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 28 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 27 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 40 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 38 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 37 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 36 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 44 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 43 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 42 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 41 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 40 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 39 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b9 = at 38 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 37 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 36 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 35 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 34 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 33 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 48 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 47 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ S3 ∷ [])
  b10 = at 46 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 45 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 44 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 43 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 42 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 41 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 40 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 39 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ S3 ∷ [])
  b11 = at 38 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 37 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 36 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 52 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 51 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 50 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 49 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 48 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ S3 ∷ [])
  b12 = at 47 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 46 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 45 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 44 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 43 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 42 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 41 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 40 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ S3 ∷ [])
  b13 = at 39 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 56 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 53 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 52 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 51 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 50 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

  b14 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ S3 ∷ [])
  b14 = at 49 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 43 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ [])
  b15 = at 60 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 59 4 (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S3-I c4)) ▸
       at 58 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 57 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 56 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 55 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 54 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 53 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ [])
  b16 = at 52 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 51 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 50 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 49 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 48 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 47 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 46 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 45 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

-- deb-P-hi-split-b: 66 steps
lem-deb-P-hi-split-b : Ws → ⟪ (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-deb-P-hi-split-b c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 4 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 3 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 8 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 7 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 6 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 12 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 11 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b1 = at 10 4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-K2-K2 c4)) ▸
       at 9 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-K2-CS2 c4)) ▸
       at 16 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 15 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 14 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 13 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 12 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 20 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b2 = at 19 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 18 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 17 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 16 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 15 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 24 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 23 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 22 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ CS23 ∷ CS23 ∷ [])
  b3 = at 21 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 20 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 19 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 18 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 28 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl1410 (lit c4)) ▸
       at 27 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 26 4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-S3-S3 c4)) ▸
       at 25 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS23 ∷ CS23 ∷ [])
  b4 = at 24 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 23 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 22 4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S3-K2 c4)) ▸
       at 21 4 (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-S3-CS2 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-I-S3 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ CS23 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K2 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-I-CS2 c4)) ▸
       at 36 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-CS2-S3 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-CS2-S3 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-CS2-S3 c4)) ▸
       at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 29 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 28 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 27 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 40 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-23 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 38 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I c4)) ▸
       at 37 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-CS2-S3 c4)) ▸
       at 36 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-CS2-S3 c4)) ▸
       at 35 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (sym (lem-F4-CS2-S3 c4)) ▸
       at 34 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸
       at 33 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 32 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K2 c4)) ▸
       at 30 4 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS2-CS2 c4)) ▸ done

-- deb-P-hi-split-a @02132031: 136 steps
lem-deb-P-hi-split-a-at02132031 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-hi-split-a-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 11 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b1 = at 10 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 9 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b2 = at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 17 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 23 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b3 = at 21 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 27 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b4 = at 24 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 24 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 35 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-K2-K2-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b6 = at 33 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 31 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 40 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 44 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b9 = at 38 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 35 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 34 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 48 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 47 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b10 = at 46 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ [])
  b11 = at 38 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 37 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 36 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 52 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 51 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 50 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 49 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ [])
  b12 = at 47 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ [])
  b13 = at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 56 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 53 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 52 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 51 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 50 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

  b14 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ [])
  b14 = at 49 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 43 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  b15 = at 60 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 59 4 (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S3-I-at02132031 c4)) ▸
       at 58 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 57 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 56 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 55 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 54 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 53 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  b16 = at 52 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 51 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 50 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 49 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 48 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 47 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 46 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

-- deb-P-hi-split-b @02132031: 66 steps
lem-deb-P-hi-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-deb-P-hi-split-b-at02132031 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 4 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 3 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 8 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 7 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 6 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 12 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4) ▸
       at 11 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b1 = at 10 4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-K2-K2-at02132031 c4)) ▸
       at 9 4 (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K2-CS2-at02132031 c4)) ▸
       at 16 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 15 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 14 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 13 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 12 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 20 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b2 = at 19 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 17 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 16 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 15 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 24 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 23 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ CS01 ∷ CS01 ∷ [])
  b3 = at 21 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 20 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 19 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 18 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 28 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 27 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 26 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S3-S3-at02132031 c4)) ▸
       at 25 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS01 ∷ CS01 ∷ [])
  b4 = at 24 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 23 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 22 4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-S3-K2-at02132031 c4)) ▸
       at 21 4 (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S3-CS2-at02132031 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S3-at02132031 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ CS01 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-I-K2-at02132031 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-I-CS2-at02132031 c4)) ▸
       at 36 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 29 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 28 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 27 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 40 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-23-at02132031 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 38 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at02132031 c4)) ▸
       at 37 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 36 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 35 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S3-at02132031 c4)) ▸
       at 34 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸
       at 33 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 32 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (sym (lem-F4-CS2-K2-at02132031 c4)) ▸
       at 30 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS2-CS2-at02132031 c4)) ▸ done
