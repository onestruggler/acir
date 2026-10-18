{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D041 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0157 ; wl0159 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0214 ; wl0220 ; wl0221 ; wl0222 ; wl0256 ; wl0275 ; wl0280 ; wl0283 ; wl0284 ; wl0285 ; wl0286 ; wl0287 ; wl0305 ; wl0335 ; wl0344 ; wl0348 ; wl0443 ; wl0447 ; wl0448 ; wl0471 ; wl0489 ; wl0498 ; wl0514 ; wl0527 ; wl0640 ; wl0641 ; wl0670 ; wl0698 ; wl0761 ; wl0825 ; wl0826 ; wl0827 ; wl0850 ; wl0852 ; wl0882 ; wl1112 ; wl1192 ; wl1206 ; wl1341 ; wl1344 ; wl1348 ; wl1351 ; wl1370 ; wl1391 ; wl1398 ; wl1399 ; wl1400 ; wl1401 ; wl1402 ; wl1403 ; wl1404 ; wl1405 ; wl1406 ; wl1407 ; wl1408 ; wp0006 ; wp0007 ; wp0049 ; wp0050 ; wp0051 ; wp0053 ; wp0054 ; wp0058 ; wp0059 ; wp0061 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0127 ; wp0173 ; wp0231 ; wp0268 ; wp0272 ; wp0298 ; wp0299 ; wp0301 ; wp0384 ; wp0543 ; wp0550 ; wp0574 ; wp0593 ; wp0661 ; wp0683 ; wp0725 ; wp0823 ; wp1209 ; wp1217 ; wp1226 ; wp1228 ; wp1229 ; wp1230 ; wp1232 ; wp1249 ; wp1250 ; wp1251 ; wp1252 ; wp1253 ; wp1254 ; wp1255 ; wp1256 ; wp1257 ; wp1258)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-box-tQ-at1331)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-box-tQ-at2442 ; lem-pairs-at1331)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-pairs-at13243142 ; lem-sym-ab-at14233142)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-tQ-at032032)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-box-box-1-at03102132 ; lem-box-cP-at032032 ; lem-box-tQ-at033440 ; lem-sym-bc-at132132 ; lem-sym-bc-at1331 ; lem-tP-at032032)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-box-perm-2134-at03102132)
open import Examples.Groups.Clifford+CS.FiveV.D.D018 using (lem-box-cP-at2442 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-box-cP-at033440 ; lem-tP-at033440)
open import Examples.Groups.Clifford+CS.FiveV.D.D035 using (lem-box-box-3-at03102132)
open import Examples.Groups.Clifford+CS.FiveV.D.D036 using (lem-L-CCZ013-0 ; lem-box-box-3-at021021)
open import Examples.Groups.Clifford+CS.FiveV.D.D040 using (lem-CK-box-at033440 ; lem-L-Toff-0 ; lem-Tu-box-at0220 ; lem-Tu-box-at0314213042 ; lem-box-cP-at02102331 ; lem-box-perm-1324-at021021 ; lem-box-perm-2134-at021021 ; lem-box-perm-2134-at0220 ; lem-box-perm-2134-at032032 ; lem-box-perm-2341-at0314213042 ; lem-box-perm-3214-at03122031 ; lem-box-perm-3214-at032032 ; lem-box-perm-4123-at032032 ; lem-box-tQ-at142142 ; lem-cQ-at02102331 ; lem-cQ-at142142 ; lem-nf-toff-cczat0 ; lem-sym-ab-at142142 ; lem-sym-bc-at021021 ; lem-sym-bc-at142142)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd14-TOFF023 ; lem-comm-TOFF014-CSd23)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CZ14-TOFF023)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CZ12-TOFF304)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CSd14-TOFF203 ; lem-comm-CX03-CCZ124 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ23-TOFF014)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CS23 ; lem-comm-CCZ014-CSd23 ; lem-comm-CCZ023-CX14 ; lem-comm-CS14-TOFF203 ; lem-comm-TOFF023-CX14)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-CCZ013-CS24 ; lem-comm-CCZ013-CSd24 ; lem-comm-SWAP13-BOX⟨2·04⟩ ; lem-comm-TOFF214-CX03)
-- P-box @2442: 8 steps
lem-P-box-at2442 : Ws → ⟪ (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-P-box-at2442 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4) ▸
       at 0 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at2442 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (sym (wl0825 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at2442 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ23 ∷ []) (sym (wl0826 (lit c4))) ▸
       at 2 2 (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done


-- pairs @2442: 4 steps
lem-pairs-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-pairs-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) (sym (lem-P-box-at2442 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at2442 c4) ▸
       at 4 2 [] (wl0203 (lit c4)) ▸
       at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸ done


-- box-perm-3241 @142142: 3 steps
lem-box-perm-3241-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3241-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-1432 ∷ []) (lem-sym-ab-at142142 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-pairs-at2442 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4) ▸ done


-- sym-ab @2442: 18 steps
lem-sym-ab-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-ab-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1432 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 4 1 (Bx0-42 ∷ []) (refl) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ [])
  b1 = at 2 6 (Bx4-032 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 7 1 (Bx0-42 ∷ []) (refl) ▸
       at 10 1 (Bx0-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (Bx0-4132 ∷ [])
  b2 = at 5 6 (Bx4-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- box-perm-4213 @132132: 3 steps
lem-box-perm-4213-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4213-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-pairs-at1331 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-ab-at2442 c4) ▸ done


-- sym-ab @02102331: 18 steps
lem-sym-ab-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym-ab-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0314 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (sym (wl1341 (lit c4))) ▸
       at 4 1 (Bx2-34 ∷ []) (refl) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ [])
  b1 = at 2 6 (Bx3-214 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (sym (wl1341 (lit c4))) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸
       at 10 1 (Bx2-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (Bx2-3014 ∷ [])
  b2 = at 5 6 (Bx3-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- box-perm-3124 @021021: 2 steps
lem-box-perm-3124-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-box-perm-3124-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Bx2-0314 ∷ []) (lem-sym-bc-at021021 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym-ab-at02102331 c4) ▸ done


-- sym-ab @02132031: 18 steps
lem-sym-ab-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym-ab-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3014 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (sym (wp1232 c4)) ▸
       at 4 1 (Bx2-04 ∷ []) (refl) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ [])
  b1 = at 2 6 (Bx0-214 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (sym (wp1232 c4)) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸
       at 10 1 (Bx2-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (Bx2-0314 ∷ [])
  b2 = at 5 6 (Bx0-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- box-tQ @02102331: 13 steps
lem-box-tQ-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0314 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 0 2 (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) (wl0640 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at02102331 c4) ▸
       at 2 4 (Toff203 ∷ []) (wl0641 (lit c4)) ▸ done


-- CXbc-box @02102331: 17 steps
lem-CXbc-box-at02102331 : Ws → ⟪ (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX31 ∷ CCZ234 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ124 ∷ CX03 ∷ CS04 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02102331 c4) ▸
       at 0 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (sym (wl1398 (lit c4))) ▸
       at 3 2 (Toff203 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1249 c4) ▸
       at 2 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 9 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 8 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX31 ∷ CCZ234 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ124 ∷ CX03 ∷ CS04 ∷ CX31 ∷ []) (Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS34⁻ ∷ []) (sym (wl1399 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ234 ∷ []) (sym (wl0527 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (sym (wl1398 (lit c4))) ▸
       at 4 3 (CX31 ∷ []) (wl1400 (lit c4)) ▸
       at 0 4 (Bx2-0314 ∷ []) (sym (lem-box-tQ-at02102331 c4)) ▸ done

  b2 : Chain (Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ []) (Bx2-0314 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp1228 c4)) ▸ done


-- CXcb-box @02102331: 18 steps
lem-CXcb-box-at02102331 : Ws → ⟪ (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) (Toff203 ∷ CCZ124 ∷ CX13 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ Toff203 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ124 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02102331 c4) ▸
       at 0 2 (Toff203 ∷ CX13 ∷ Toff201 ∷ []) (wl1401 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 1 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (Toff203 ∷ CS04 ∷ []) (wp1251 c4) ▸
       at 7 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ CX13 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ Toff203 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ124 ∷ CX13 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff203 ∷ Toff201 ∷ []) (wl1391 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CX13 ∷ Toff201 ∷ []) (wl1401 (lit c4)) ▸
       at 3 3 (CX13 ∷ []) (wl1402 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b2 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ []) (Bx2-0314 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-0314 ∷ []) (sym (lem-box-tQ-at02102331 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp1226 c4)) ▸ done


-- SWbc-box @02102331: 11 steps
lem-SWbc-box-at02102331 : Ws → ⟪ (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-SWbc-box-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (CX31 ∷ Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx2-0314 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02102331 c4) ▸
       at 3 2 (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4) ▸
       at 1 3 (Bx2-0314 ∷ CCZ014 ∷ []) (lem-CXcb-box-at02102331 c4) ▸
       at 4 2 (CX31 ∷ CCZ034 ∷ []) (wp0127 c4) ▸
       at 3 2 (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4) ▸
       at 2 2 (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4) ▸ done

  b1 : Chain (CX31 ∷ Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ []) (Bx2-0314 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp1252 c4) ▸
       at 0 3 (Bx2-0314 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02102331 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done


-- nat-SWbc @02102331: 23 steps
lem-nat-SWbc-at02102331 : Ws → ⟪ (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-nat-SWbc-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ Sw13 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 4 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 5 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ Sw13 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Sw13 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 8 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 12 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Sw13 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Sw13 ∷ []) (Bx2-0134 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx0-234 ∷ []) (refl) ▸
       at 5 6 (Bx0-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- sym-bc @02102331: 2 steps
lem-sym-bc-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-bc-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at02102331 c4)) ▸
       at 0 3 (Bx2-0134 ∷ []) (lem-nat-SWbc-at02102331 c4) ▸ done


-- box-perm-2314 @02132031: 2 steps
lem-box-perm-2314-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2314-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-0314 ∷ []) (lem-sym-ab-at02132031 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-bc-at02102331 c4) ▸ done


-- tP @142142: 7 steps
lem-tP-at142142 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at142142 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at142142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done


-- VPQ @142142: 14 steps
lem-VPQ-at142142 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸ done


-- QVQ @142142: 3 steps
lem-QVQ-at142142 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at142142 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at142142 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @142142: 12 steps
lem-box-cP-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4132 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at142142 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done


-- t-cP @032032: 5 steps
lem-t-cP-at032032 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at032032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 2 (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (sym (wl1370 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸
       at 2 3 (CCZ013 ∷ Toff301 ∷ []) (sym (wl1192 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸ done


-- box2 @032032: 11 steps
lem-box2-at032032 : Ws → ⟪ (Bx3-1024 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ Bx3-1024 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 4 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) (lem-t-cP-at032032 c4) ▸
       at 5 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 5 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) []
  b1 = at 2 2 [] (wl0443 (lit c4)) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wl0443 (lit c4)) ▸ done


-- t-cP @142142: 5 steps
lem-t-cP-at142142 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-t-cP-at142142 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (sym (wp0058 c4)) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4)) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸
       at 2 3 (CCZ014 ∷ Toff014 ∷ []) (sym (wp0059 c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸ done


-- box2 @142142: 11 steps
lem-box2-at142142 : Ws → ⟪ (Bx0-4132 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4132 ∷ Bx0-4132 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 5 5 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) (lem-t-cP-at142142 c4) ▸
       at 5 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) []
  b1 = at 2 2 [] (wp0051 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wp0051 c4) ▸ done


-- box-perm-2431 @142142: 3 steps
lem-box-perm-2431-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2431-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done


-- t-cP @033440: 5 steps
lem-t-cP-at033440 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-t-cP-at033440 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ [])
  b0 = at 0 2 (CCZ123 ∷ Toff312 ∷ CZ12 ∷ []) (sym (wl1403 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4)) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸
       at 2 3 (CCZ123 ∷ Toff312 ∷ []) (sym (wl0882 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸ done


-- box2 @033440: 11 steps
lem-box2-at033440 : Ws → ⟪ (Bx3-1240 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 4 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 5 5 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ []) (lem-t-cP-at033440 c4) ▸
       at 5 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 5 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) []
  b1 = at 2 2 [] (wl0489 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0489 (lit c4)) ▸ done


-- F1-toff-ccz@0: 310 steps
lem-F1-toff-cczat0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-toff-cczat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (run b38))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 0 48 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-L-Toff-0 c4) ▸
       at 4 75 (Bx2-0134 ∷ []) (lem-L-CCZ013-0 c4) ▸
       at 5 48 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-L-Toff-0 c4) ▸
       at 4 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 6 1 (Bx2-1034 ∷ []) (lem-box-perm-2134-at021021 c4) ▸
       at 5 3 (Bx2-1034 ∷ Bx3-1024 ∷ []) (lem-Tu-box-at0220 c4) ▸
       at 5 1 (Bx2-0134 ∷ []) (lem-box-perm-2134-at0220 c4) ▸
       at 6 1 (Bx3-2014 ∷ []) (lem-box-perm-3214-at032032 c4) ▸ done

  b1 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ CX03 ∷ Toff214 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ [])
  b1 = at 5 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 5 1 (Bx3-1024 ∷ []) (lem-box-perm-3214-at03122031 c4) ▸
       at 6 1 (Bx2-0314 ∷ []) (lem-box-perm-1324-at021021 c4) ▸
       at 6 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02102331 c4) ▸
       at 10 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸
       at 9 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 10 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 11 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸ done

  b2 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ CX03 ∷ Toff214 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ K0 ∷ Toff214 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ [])
  b2 = at 12 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 13 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 14 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 15 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 9 7 (Toff034 ∷ []) (wp1253 c4) ▸
       at 8 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 8 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸
       at 7 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸ done

  b3 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ K0 ∷ Toff214 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ CCZ134 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ [])
  b3 = at 8 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 9 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 11 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 12 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 13 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 7 7 (Toff034 ∷ []) (wp1253 c4) ▸
       at 8 2 (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (sym (wl1344 (lit c4))) ▸ done

  b4 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ CCZ134 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CCZ134 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ [])
  b4 = at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 9 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 8 2 (CS34 ∷ CCZ023 ∷ []) (wp0543 c4) ▸
       at 9 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ023 ∷ []) (wp0574 c4) ▸
       at 11 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ023 ∷ []) (wl0670 (lit c4)) ▸
       at 8 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done

  b5 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CCZ134 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-1024 ∷ Toff034 ∷ [])
  b5 = at 9 2 (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4) ▸
       at 7 3 (CCZ134 ∷ []) (sym (wl1405 (lit c4))) ▸
       at 8 4 (Bx2-0314 ∷ []) (sym (lem-box-cP-at02102331 c4)) ▸
       at 8 1 (Bx2-0134 ∷ []) (sym (lem-box-perm-1324-at021021 c4)) ▸
       at 8 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 10 1 (Bx2-1034 ∷ []) (lem-box-perm-2134-at021021 c4) ▸
       at 9 3 (Bx2-1034 ∷ Bx3-1024 ∷ []) (lem-Tu-box-at0220 c4) ▸
       at 9 1 (Bx2-0134 ∷ []) (lem-box-perm-2134-at0220 c4) ▸ done

  b6 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-1024 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ Toff214 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ [])
  b6 = at 10 1 (Bx3-2014 ∷ []) (lem-box-perm-3214-at032032 c4) ▸
       at 9 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 9 1 (Bx3-1024 ∷ []) (lem-box-perm-3214-at03122031 c4) ▸
       at 10 1 (Bx2-0314 ∷ []) (lem-box-perm-1324-at021021 c4) ▸
       at 10 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02102331 c4) ▸
       at 14 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸
       at 13 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 14 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸ done

  b7 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ Toff214 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ [])
  b7 = at 15 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 17 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 18 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 19 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 13 7 (Toff034 ∷ []) (wp1253 c4) ▸
       at 12 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 12 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸ done

  b8 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ Toff214 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ [])
  b8 = at 11 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 12 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 13 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 15 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 16 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 17 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 11 7 (Toff034 ∷ []) (wp1253 c4) ▸ done

  b9 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ Toff214 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b9 = at 12 2 (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (sym (wl1344 (lit c4))) ▸
       at 10 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 13 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 12 2 (CS34 ∷ CCZ023 ∷ []) (wp0543 c4) ▸
       at 13 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ023 ∷ []) (wp0574 c4) ▸
       at 15 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 16 2 (CS13 ∷ CCZ023 ∷ []) (wl0670 (lit c4)) ▸ done

  b10 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b10 = at 12 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 13 2 (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4) ▸
       at 11 3 (CCZ134 ∷ []) (sym (wl1405 (lit c4))) ▸
       at 12 4 (Bx2-0314 ∷ []) (sym (lem-box-cP-at02102331 c4)) ▸
       at 12 1 (Bx2-0134 ∷ []) (sym (lem-box-perm-1324-at021021 c4)) ▸
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 11 1 (Bx3-4102 ∷ []) (lem-box-perm-4123-at032032 c4) ▸
       at 10 3 (Bx3-4102 ∷ Bx0-4132 ∷ []) (lem-Tu-box-at0314213042 c4) ▸ done

  b11 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx2-0134 ∷ [])
  b11 = at 10 1 (Bx3-1024 ∷ []) (lem-box-perm-2341-at0314213042 c4) ▸
       at 10 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 11 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸
       at 10 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 10 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 11 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 11 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 14 2 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (sym (wl1406 (lit c4))) ▸ done

  b12 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx2-0134 ∷ [])
  b12 = at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 14 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd24 (lit c4)) ▸
       at 16 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ013 ∷ []) (wp0299 c4) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 14 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸ done

  b13 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b13 = at 12 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 11 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 12 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 12 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 13 1 (Bx2-3014 ∷ []) (lem-box-perm-3124-at021021 c4) ▸
       at 12 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 12 1 (Bx2-0134 ∷ []) (lem-box-perm-2314-at02132031 c4) ▸
       at 13 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸ done

  b14 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b14 = at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 14 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 13 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done

  b15 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b15 = at 12 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done

  b16 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx3-0124 ∷ Bx0-3124 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b16 = at 10 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 11 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 5 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 7 1 (Bx3-4102 ∷ []) (lem-box-perm-4123-at032032 c4) ▸
       at 6 3 (Bx3-4102 ∷ Bx0-4132 ∷ []) (lem-Tu-box-at0314213042 c4) ▸
       at 6 1 (Bx3-1024 ∷ []) (lem-box-perm-2341-at0314213042 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 7 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸ done

  b17 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx3-0124 ∷ Bx0-3124 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX12 ∷ CCZ013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ134 ∷ Toff324 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b17 = at 6 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 6 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 7 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 7 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 10 2 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (sym (wl1406 (lit c4))) ▸
       at 10 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 10 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸ done

  b18 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX12 ∷ CCZ013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ134 ∷ Toff324 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx3-1024 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b18 = at 11 2 (CS24⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd24 (lit c4)) ▸
       at 12 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ013 ∷ []) (wp0299 c4) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 10 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 8 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 8 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸ done

  b19 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx3-1024 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ CCZ013 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff324 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b19 = at 8 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 11 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 10 2 (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl0498 (lit c4)) ▸
       at 9 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff324 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 11 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 12 2 (CS12⁻ ∷ Toff324 ∷ []) (sym (wl0447 (lit c4))) ▸ done

  b20 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ CCZ013 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff324 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b20 = at 13 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 14 2 (CS02 ∷ Toff324 ∷ []) (sym (wp0298 c4)) ▸
       at 10 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 8 3 (Toff312 ∷ CCZ013 ∷ []) (wl0850 (lit c4)) ▸
       at 9 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 11 1 (Bx3-4102 ∷ []) (lem-box-perm-4123-at032032 c4) ▸
       at 10 3 (Bx3-4102 ∷ Bx0-4132 ∷ []) (lem-Tu-box-at0314213042 c4) ▸ done

  b21 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b21 = at 10 1 (Bx3-1024 ∷ []) (lem-box-perm-2341-at0314213042 c4) ▸
       at 10 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 11 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸
       at 10 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 10 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 11 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 11 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 14 2 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (sym (wl1406 (lit c4))) ▸ done

  b22 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b22 = at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 14 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd24 (lit c4)) ▸
       at 16 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ013 ∷ []) (wp0299 c4) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 14 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸ done

  b23 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx3-1024 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b23 = at 12 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 11 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 12 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 12 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 13 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸
       at 12 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 12 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 13 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸ done

  b24 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx3-1024 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Bx0-4132 ∷ Bx2-0134 ∷ [])
  b24 = at 13 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 14 1 (Bx2-3014 ∷ []) (lem-box-perm-3124-at021021 c4) ▸
       at 13 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 13 1 (Bx2-0134 ∷ []) (lem-box-perm-2314-at02132031 c4) ▸
       at 14 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 14 2 [] (lem-box2-at032032 c4) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 14 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸ done

  b25 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Bx0-4132 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-4132 ∷ Bx2-0134 ∷ [])
  b25 = at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 13 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 12 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸ done

  b26 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-4132 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx0-4132 ∷ Bx2-0134 ∷ [])
  b26 = at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 10 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 11 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸ done

  b27 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx0-4132 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b27 = at 11 2 [] (lem-box2-at142142 c4) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 10 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 9 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b28 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b28 = at 9 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 8 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b29 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ Toff012 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b29 = at 7 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 7 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 7 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 10 2 (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) (sym (wl1407 (lit c4))) ▸
       at 9 2 (Toff012 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp1255 c4) ▸
       at 12 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl0514 (lit c4))) ▸
       at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b30 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ Toff012 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ Toff023 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b30 = at 12 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 13 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 14 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 15 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 16 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 11 7 (Toff312 ∷ []) (wl0514 (lit c4)) ▸
       at 8 2 (Toff012 ∷ Toff023 ∷ []) (sym (wl0275 (lit c4))) ▸ done

  b31 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ Toff023 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff012 ∷ Toff312 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b31 = at 10 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 10 2 (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) (sym (wl1407 (lit c4))) ▸ done

  b32 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff012 ∷ Toff312 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b32 = at 8 3 (CCZ124 ∷ []) (sym (wp1256 c4)) ▸
       at 7 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 9 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl0514 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 9 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 10 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 11 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 12 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸ done

  b33 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff034 ∷ Toff023 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b33 = at 13 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff312 ∷ []) (wl0514 (lit c4)) ▸
       at 9 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 12 2 (Toff034 ∷ Toff023 ∷ []) (wp0173 c4) ▸
       at 11 2 (Toff034 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1209 c4) ▸
       at 10 2 (Toff034 ∷ Toff023 ∷ []) (wp0173 c4) ▸ done

  b34 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff034 ∷ Toff023 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b34 = at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 9 3 (Toff034 ∷ CCZ014 ∷ []) (wp0268 c4) ▸ done

  b35 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Bx2-0134 ∷ [])
  b35 = at 10 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 14 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b36 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ [])
  b36 = at 13 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 12 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b37 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ Bx0-1234 ∷ Bx2-0134 ∷ [])
  b37 = at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 10 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 11 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 11 1 (Bx0-1234 ∷ []) (lem-box-perm-2431-at142142 c4) ▸
       at 6 2 (Toff312 ∷ CCZ134 ∷ Toff312 ∷ []) (wl1408 (lit c4)) ▸
       at 8 2 [] (wl0489 (lit c4)) ▸
       at 7 3 (Toff034 ∷ []) (wp1257 c4) ▸
       at 4 4 (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (sym (lem-CK-box-at033440 c4)) ▸ done

  b38 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ Bx0-1234 ∷ Bx2-0134 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b38 = at 0 4 (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (sym (lem-CK-box-at033440 c4)) ▸
       at 2 2 [] (wp1258 c4) ▸
       at 1 2 [] (lem-box2-at033440 c4) ▸
       at 0 2 [] (wp1217 c4) ▸
       at 0 0 [] (wl1112 (lit c4)) ▸
       at 0 2 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (sym (lem-nf-toff-cczat0 c4)) ▸ done

