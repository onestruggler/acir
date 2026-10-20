{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D037 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0166 ; wl0199 ; wl0238 ; wl0256 ; wl0274 ; wl0298 ; wl0305 ; wl0313 ; wl0321 ; wl0341 ; wl0348 ; wl0366 ; wl0367 ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0389 ; wl0390 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wp0003 ; wp0053 ; wp0062 ; wp0063 ; wp0064 ; wp0117 ; wp0141 ; wp0142 ; wp0161 ; wp0167 ; wp0221 ; wp0231 ; wp0259 ; wp0260 ; wp0275 ; wp0276 ; wp0277 ; wp0278 ; wl0167 ; wl0214 ; wl0263 ; wl0296 ; wl0325 ; wl0327 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0444 ; wl0445 ; wl0446 ; wl0447 ; wl0448 ; wl0449 ; wl0450 ; wl0460 ; wl0461 ; wp0007 ; wp0011 ; wp0034 ; wp0035 ; wp0036 ; wp0054 ; wp0077 ; wp0106 ; wp0107 ; wp0108 ; wp0186 ; wp0290 ; wp0291 ; wp0292 ; wp0293 ; wp0295 ; wp0296 ; wp0297 ; wp0298 ; wp0299 ; wp0300 ; wp0311 ; wl0499 ; wl0501 ; wl0503 ; wl0511 ; wl0512 ; wl0513 ; wl0514 ; wl0515 ; wl0516 ; wl0517 ; wp0061 ; wp0065 ; wp0357 ; wp0372 ; wp0373 ; wp0374 ; wp0375 ; wp0376 ; wl0204 ; wl0642 ; wl0665 ; wp0517 ; wp0524 ; wl0685 ; wl0704 ; wl0706 ; wl0720 ; wl0721 ; wl0722 ; wl0723 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0736 ; wl0737 ; wp0555 ; wp0587 ; wp0610 ; wp0613 ; wp0614 ; wp0615 ; wp0616 ; wp0617 ; wp0629 ; wp0630 ; wp0631 ; wp0632 ; wp0633 ; wp0635 ; wl0771 ; wl0772 ; wl0773 ; wl0774 ; wl0775 ; wl0776 ; wl0777 ; wl0778 ; wl0779 ; wl0780 ; wp0041 ; wp0644 ; wp0645 ; wp0646 ; wp0647 ; wp0684 ; wp0686 ; wp0697 ; wp0698 ; wp0699 ; wp0700 ; wp0701 ; wp0702 ; wl0829 ; wl0850 ; wl0869 ; wl0870 ; wl0871 ; wp0183 ; wp0185 ; wp0190 ; wp0739 ; wp0740 ; wp0741 ; wp0742 ; wp0743)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214213043 ; lem-box-tQ-at0314213042 ; lem-box-tQ-at0330 ; lem-box-tQ-at033440 ; lem-box-tQ-at043043 ; lem-box-tQ-at12233441 ; lem-box-tQ-at233442 ; lem-box-tQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at021021 ; lem-box-cP-at03102132 ; lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0110 ; lem-box-cP-at0210233441 ; lem-box-cP-at0210243143 ; lem-box-cP-at0314203142 ; lem-box-cP-at122441 ; lem-box-cP-at132132 ; lem-box-cP-at233442 ; lem-box-cP-at243243 ; lem-box-perm-2314-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-Kdu-box ; lem-Ku-box ; lem-Ku-box-at0210243143 ; lem-Ku-box-at122441 ; lem-Ku-box-at243243 ; lem-box-box-4-at0410213243 ; lem-box-perm-1324-at043043 ; lem-box-perm-1423-at233442 ; lem-box-perm-3124-at043043 ; lem-box-perm-4123-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-box-4-at0310243142 ; lem-box-perm-1324-at0314213042 ; lem-box-perm-2314-at0310243142 ; lem-box-perm-2341-at03102132 ; lem-box-perm-3124-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-CKdu-box-1 ; lem-CKdu-box-2 ; lem-CKdu-box-2-at0210243143 ; lem-CKdu-box-2-at122441 ; lem-CKdu-box-2-at243243 ; lem-CKdu-box-3 ; lem-CKdu-box-4 ; lem-CKu-box-1 ; lem-CKu-box-2 ; lem-CKu-box-2-at0210243143 ; lem-CKu-box-2-at122441 ; lem-CKu-box-2-at243243 ; lem-CKu-box-3 ; lem-CKu-box-4 ; lem-box-perm-1243 ; lem-box-perm-1243-at3443 ; lem-box-perm-1342 ; lem-box-perm-1423-at0210243143 ; lem-box-perm-1423-at243243 ; lem-box-perm-2341 ; lem-box-perm-3421-at0213203441 ; lem-box-perm-3421-at0314203142 ; lem-box-perm-4123-at033440 ; lem-box-perm-4312-at0214213043 ; lem-box-perm-4312-at0330)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX02-TOFF134 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ03-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ013-CK42 ; lem-comm-CK41-CCZ023 ; lem-comm-CK42-CCZ013 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX04-TOFF312 ; lem-comm-CX31-TOFF024 ; lem-comm-CZ02-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CK41)

-- XCKX-box-1: 4 steps
lem-XCKX-box-1 : Ws → ⟪ (X1 ∷ CK10 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-XCKX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CK10 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  b0 = at 0 3 (K0 ∷ CK10⁻ ∷ []) (sym (wl0366 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CK10⁻ ∷ []) (lem-CKdu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X1 ∷ CK10 ∷ X1 ∷ []) (wl0366 (lit c4)) ▸ done

-- XCKdX-box-1: 4 steps
lem-XCKdX-box-1 : Ws → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCKdX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK10 ∷ []) (sym (wl0367 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CK10 ∷ []) (lem-CKu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X1 ∷ CK10⁻ ∷ X1 ∷ []) (wl0367 (lit c4)) ▸ done

-- XCKX-box-2: 4 steps
lem-XCKX-box-2 : Ws → ⟪ (X2 ∷ CK20 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-XCKX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b0 = at 0 3 (K0 ∷ CK20⁻ ∷ []) (sym (wl0379 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CK20⁻ ∷ []) (lem-CKdu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X2 ∷ CK20 ∷ X2 ∷ []) (wl0379 (lit c4)) ▸ done

-- XCKdX-box-2: 4 steps
lem-XCKdX-box-2 : Ws → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCKdX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK20 ∷ []) (sym (wl0380 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CK20 ∷ []) (lem-CKu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (wl0380 (lit c4)) ▸ done

-- XCKX-box-3: 4 steps
lem-XCKX-box-3 : Ws → ⟪ (X3 ∷ CK30 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-XCKX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b0 = at 0 3 (K0 ∷ CK30⁻ ∷ []) (sym (wl0389 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CK30⁻ ∷ []) (lem-CKdu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X3 ∷ CK30 ∷ X3 ∷ []) (wl0389 (lit c4)) ▸ done

-- XCKdX-box-3: 4 steps
lem-XCKdX-box-3 : Ws → ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCKdX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK30 ∷ []) (sym (wl0390 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CK30 ∷ []) (lem-CKu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X3 ∷ CK30⁻ ∷ X3 ∷ []) (wl0390 (lit c4)) ▸ done

-- XCKX-box-4: 4 steps
lem-XCKX-box-4 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (sym (wp0259 c4)) ▸
       at 1 2 (Bx0-1234 ∷ CK40⁻ ∷ []) (lem-CKdu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (wp0259 c4) ▸ done

-- XCKdX-box-4: 4 steps
lem-XCKdX-box-4 : Ws → ⟪ (X4 ∷ CK40⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCKdX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK40 ∷ []) (sym (wp0260 c4)) ▸
       at 1 2 (Bx0-1234 ∷ CK40 ∷ []) (lem-CKu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X4 ∷ CK40⁻ ∷ X4 ∷ []) (wp0260 c4) ▸ done

-- box-box-1: 105 steps
lem-box-box-1 : Ws → ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-0234 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff134 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-box-perm-2341 c4) ▸
       at 0 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 4 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 4 2 (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0275 c4) ▸
       at 6 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 10 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 9 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff134 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 5 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 6 3 (Toff134 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 3 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ Toff134 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0313 (lit c4))) ▸
       at 4 2 (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0408 (lit c4)) ▸
       at 3 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0409 (lit c4))) ▸
       at 9 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 8 2 (Toff134 ∷ CS03 ∷ []) (wp0277 c4) ▸
       at 7 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸
       at 6 2 (Toff134 ∷ CS23⁻ ∷ []) (wl0410 (lit c4)) ▸
       at 5 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸ done

  b3 : Chain (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ Toff134 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff134 ∷ CCZ014 ∷ [])
  b3 = at 4 2 (Toff134 ∷ CS23 ∷ []) (wl0238 (lit c4)) ▸
       at 3 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff023 ∷ []) (wl0409 (lit c4)) ▸
       at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 9 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b4 : Chain (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff134 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff134 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0313 (lit c4))) ▸
       at 5 3 (Toff023 ∷ []) (wl0412 (lit c4)) ▸
       at 6 2 (Toff134 ∷ CCZ234 ∷ []) (wl0413 (lit c4)) ▸
       at 5 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0409 (lit c4))) ▸
       at 11 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸ done

  b5 : Chain (Toff023 ∷ CCZ014 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff134 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ014 ∷ Bx1-0234 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b5 = at 10 2 (Toff134 ∷ CS03 ∷ []) (wp0277 c4) ▸
       at 9 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸
       at 8 2 (Toff134 ∷ CS23⁻ ∷ []) (wl0410 (lit c4)) ▸
       at 7 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸
       at 6 2 (Toff134 ∷ CS23 ∷ []) (wl0238 (lit c4)) ▸
       at 5 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 7 (Toff023 ∷ []) (wl0409 (lit c4)) ▸
       at 2 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸ done

  b6 : Chain (Toff023 ∷ CCZ014 ∷ Bx1-0234 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff134 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 2 2 (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0275 c4) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b7 : Chain (Toff023 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff134 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff023 ∷ Toff134 ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 4 3 (Toff134 ∷ CCZ014 ∷ []) (wp0276 c4) ▸
       at 1 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-box-cP-at0110 c4) ▸
       at 0 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0313 (lit c4))) ▸
       at 2 2 (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0408 (lit c4)) ▸ done

  b8 : Chain (CCZ012 ∷ Toff023 ∷ Toff134 ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff134 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b8 = at 1 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0409 (lit c4))) ▸
       at 7 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 2 (Toff134 ∷ CS03 ∷ []) (wp0277 c4) ▸
       at 5 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸
       at 4 2 (Toff134 ∷ CS23⁻ ∷ []) (wl0410 (lit c4)) ▸
       at 3 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸
       at 2 2 (Toff134 ∷ CS23 ∷ []) (wl0238 (lit c4)) ▸
       at 1 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸ done

  b9 : Chain (CCZ012 ∷ Toff134 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CCZ012 ∷ CCZ234 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b9 = at 2 7 (Toff023 ∷ []) (wl0409 (lit c4)) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done

  b10 : Chain (CCZ012 ∷ Toff134 ∷ Toff023 ∷ CCZ123 ∷ CCZ012 ∷ CCZ234 ∷ Toff134 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Toff134 ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0313 (lit c4))) ▸
       at 3 3 (Toff023 ∷ []) (wl0412 (lit c4)) ▸
       at 4 2 (Toff134 ∷ CCZ234 ∷ []) (wl0413 (lit c4)) ▸
       at 3 1 (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0409 (lit c4))) ▸
       at 9 2 (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 8 2 (Toff134 ∷ CS03 ∷ []) (wp0277 c4) ▸
       at 7 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸ done

  b11 : Chain (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Toff134 ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx1-0234 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b11 = at 6 2 (Toff134 ∷ CS23⁻ ∷ []) (wl0410 (lit c4)) ▸
       at 5 2 (Toff134 ∷ CX02 ∷ []) (lem-comm-CX02-TOFF134 (lit c4)) ▸
       at 4 2 (Toff134 ∷ CS23 ∷ []) (wl0238 (lit c4)) ▸
       at 3 2 (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff023 ∷ []) (wl0409 (lit c4)) ▸
       at 0 4 (Bx1-0234 ∷ []) (sym (lem-box-cP-at0110 c4)) ▸
       at 2 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸ done

  b12 : Chain (Bx1-0234 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx1-0234 ∷ Bx0-2341 ∷ [])
  b12 = at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 3 2 (Toff023 ∷ CCZ234 ∷ []) (wp0278 c4) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸
       at 1 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

  b13 : Chain (Bx1-0234 ∷ Bx0-2341 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ [])
  b13 = at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-4123-at12233441 c4) ▸ done

-- box-box-2: 105 steps
lem-box-box-2 : Ws → ⟪ (Bx0-1234 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx2-0134 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff234 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-box-perm-1342 c4) ▸
       at 0 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 4 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 4 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0290 c4) ▸
       at 6 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 10 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 9 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ012 ∷ CX03 ∷ CS04 ∷ Toff234 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 5 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 6 3 (Toff234 ∷ CCZ024 ∷ []) (wp0291 c4) ▸
       at 3 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ Toff234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 4 2 (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0426 (lit c4)) ▸
       at 3 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0427 (lit c4))) ▸
       at 9 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (wp0292 c4) ▸
       at 7 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 6 2 (Toff234 ∷ CS13⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸ done

  b3 : Chain (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ Toff234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff234 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff234 ∷ CS13 ∷ []) (wl0429 (lit c4)) ▸
       at 3 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸
       at 4 7 (Toff013 ∷ []) (wl0427 (lit c4)) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸ done

  b4 : Chain (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff234 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff234 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 5 3 (Toff013 ∷ []) (wl0430 (lit c4)) ▸
       at 6 2 (Toff234 ∷ CCZ134 ∷ []) (wl0431 (lit c4)) ▸
       at 5 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0427 (lit c4))) ▸
       at 11 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸ done

  b5 : Chain (Toff013 ∷ CCZ024 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff234 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ024 ∷ Bx2-0134 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff234 ∷ CS03 ∷ []) (wp0292 c4) ▸
       at 9 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 8 2 (Toff234 ∷ CS13⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 7 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 6 2 (Toff234 ∷ CS13 ∷ []) (wl0429 (lit c4)) ▸
       at 5 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸
       at 6 7 (Toff013 ∷ []) (wl0427 (lit c4)) ▸
       at 2 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸ done

  b6 : Chain (Toff013 ∷ CCZ024 ∷ Bx2-0134 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff234 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 2 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0290 c4) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b7 : Chain (Toff013 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff234 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff013 ∷ Toff234 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 4 3 (Toff234 ∷ CCZ024 ∷ []) (wp0291 c4) ▸
       at 1 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 0 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 2 2 (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0426 (lit c4)) ▸ done

  b8 : Chain (CCZ012 ∷ Toff013 ∷ Toff234 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff234 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0427 (lit c4))) ▸
       at 7 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸
       at 6 2 (Toff234 ∷ CS03 ∷ []) (wp0292 c4) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 4 2 (Toff234 ∷ CS13⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 3 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 2 2 (Toff234 ∷ CS13 ∷ []) (wl0429 (lit c4)) ▸
       at 1 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸ done

  b9 : Chain (CCZ012 ∷ Toff234 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff013 ∷ []) (wl0427 (lit c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done

  b10 : Chain (CCZ012 ∷ Toff234 ∷ Toff013 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff234 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Toff234 ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 3 3 (Toff013 ∷ []) (wl0430 (lit c4)) ▸
       at 4 2 (Toff234 ∷ CCZ134 ∷ []) (wl0431 (lit c4)) ▸
       at 3 1 (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (sym (wl0427 (lit c4))) ▸
       at 9 2 (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑)) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (wp0292 c4) ▸
       at 7 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸ done

  b11 : Chain (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Toff234 ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx2-0134 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff234 ∷ CS13⁻ ∷ []) (wl0428 (lit c4)) ▸
       at 5 2 (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff)) ▸
       at 4 2 (Toff234 ∷ CS13 ∷ []) (wl0429 (lit c4)) ▸
       at 3 2 (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑)) ▸
       at 4 7 (Toff013 ∷ []) (wl0427 (lit c4)) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-cP-at021021 c4)) ▸
       at 2 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b12 : Chain (Bx2-0134 ∷ Toff013 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff013 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx2-0134 ∷ Bx0-1342 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (Toff013 ∷ CCZ134 ∷ []) (wp0293 c4) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸
       at 1 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

  b13 : Chain (Bx2-0134 ∷ Bx0-1342 ∷ []) (Bx2-0134 ∷ Bx0-1234 ∷ [])
  b13 = at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1423-at233442 c4) ▸ done

-- box-box-3: 105 steps
lem-box-box-3 : Ws → ⟪ (Bx0-1234 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx3-0124 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ013 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-box-perm-1243 c4) ▸
       at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 4 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 6 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 5 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ013 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 7 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 6 3 (Toff324 ∷ CCZ034 ∷ []) (wp0297 c4) ▸
       at 3 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 4 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 3 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 9 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b4 : Chain (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 5 3 (Toff012 ∷ []) (wl0449 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 11 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸ done

  b5 : Chain (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Bx3-0124 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 9 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 8 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 5 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 6 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 2 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸ done

  b6 : Chain (Toff012 ∷ CCZ034 ∷ Bx3-0124 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CCZ013 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 2 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸ done

  b7 : Chain (Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CCZ013 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff012 ∷ Toff324 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 4 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 3 (Toff324 ∷ CCZ034 ∷ []) (wp0297 c4) ▸
       at 1 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 0 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4)) ▸ done

  b8 : Chain (CCZ013 ∷ Toff012 ∷ Toff324 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff324 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 7 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 6 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 1 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸ done

  b9 : Chain (CCZ013 ∷ Toff324 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b10 : Chain (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 3 3 (Toff012 ∷ []) (wl0449 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b11 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx3-0124 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 3 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸ done

  b12 : Chain (Bx3-0124 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx3-0124 ∷ Bx0-1243 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff012 ∷ CCZ124 ∷ []) (wp0300 c4) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

  b13 : Chain (Bx3-0124 ∷ Bx0-1243 ∷ []) (Bx3-0124 ∷ Bx0-1234 ∷ [])
  b13 = at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1243-at3443 c4) ▸ done

-- F0-B: 62 steps
lem-F0-B : Ws → ⟪ (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx4-1203 ∷ []) ⟫ʷ
lem-F0-B c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) (Toff312 ∷ Toff412 ∷ CCZ034 ∷ Toff312 ∷ Toff412 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ CZ03 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ Toff412 ∷ CX34 ∷ []) (wl0511 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ03 ∷ CX34 ∷ []) (sym (wp0372 c4)) ▸
       at 4 2 (Toff312 ∷ Toff412 ∷ CX34 ∷ []) (wl0511 (lit c4)) ▸
       at 6 3 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0373 c4)) ▸
       at 3 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 5 2 (Toff412 ∷ CCZ012 ∷ []) (wp0374 c4) ▸
       at 4 2 (Toff412 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF412 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ Toff412 ∷ CCZ034 ∷ Toff312 ∷ Toff412 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ CZ03 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b1 = at 5 2 (CCZ012 ∷ CZ03 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ []) (sym (wp0375 c4)) ▸
       at 3 2 (Toff412 ∷ Toff312 ∷ []) (wl0513 (lit c4)) ▸
       at 4 0 (CCZ034 ∷ CCZ034 ∷ []) (sym (wp0007 c4)) ▸
       at 1 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl0514 (lit c4))) ▸ done

  b2 : Chain (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff312 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b2 = at 6 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 1 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 1 7 (Toff312 ∷ []) (wl0514 (lit c4)) ▸ done

  b3 : Chain (CCZ014 ∷ Toff312 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ K3 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff412 ∷ CCZ012 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b3 = at 1 2 (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) (wl0515 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp0376 c4)) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl0514 (lit c4))) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b4 : Chain (CCZ014 ∷ Toff423 ∷ K3 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff412 ∷ CCZ012 ∷ Toff423 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff312 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b4 = at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 3 7 (Toff312 ∷ []) (wl0514 (lit c4)) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 8 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 7 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 6 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b5 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff312 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx4-1203 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b5 = at 5 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 4 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 3 2 (Toff423 ∷ Toff312 ∷ Toff412 ∷ []) (wl0515 (lit c4)) ▸
       at 4 3 (Toff312 ∷ []) (wl0517 (lit c4)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 0 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸ done

  b6 : Chain (Bx4-1203 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx4-1203 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b6 = at 6 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 5 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 3 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

  b7 : Chain (Bx4-1203 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ [])
  b7 = at 1 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸
       at 0 1 (Bx4-0123 ∷ []) (lem-box-perm-3124-at043043 c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-4312-at0330 c4) ▸
       at 0 2 (Bx3-4012 ∷ Bx4-0123 ∷ []) (lem-box-box-4-at0410213243 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-box-perm-3421-at0314203142 c4) ▸
       at 1 1 (Bx4-1203 ∷ []) (lem-box-perm-2314-at0410213243 c4) ▸ done

-- XCKX-box-2 @243243: 4 steps
lem-XCKX-box-2-at243243 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at243243 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (sym (wp0259 c4)) ▸
       at 1 2 (Bx0-1423 ∷ CK40⁻ ∷ []) (lem-CKdu-box-2-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (wp0259 c4) ▸ done

-- XCKX-box-2 @122441: 4 steps
lem-XCKX-box-2-at122441 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at122441 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (sym (wp0259 c4)) ▸
       at 1 2 (Bx0-2431 ∷ CK40⁻ ∷ []) (lem-CKdu-box-2-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (wp0259 c4) ▸ done

-- F4-K1-CS0: 19 steps
lem-F4-K1-CS0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0642 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0642 (lit c4))) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0517 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- XCKX-box-2 @0210243143: 4 steps
lem-XCKX-box-2-at0210243143 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 3 (K2 ∷ CK42⁻ ∷ []) (sym (wl0665 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ CK42⁻ ∷ []) (lem-CKdu-box-2-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 1 2 (X4 ∷ CK42 ∷ X4 ∷ []) (wl0665 (lit c4)) ▸ done

-- F4-K2-CS1: 19 steps
lem-F4-K2-CS1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ013 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ013 ∷ X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0555 c4)) ▸
       at 4 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (CCZ013 ∷ CK42 ∷ []) (lem-comm-CK42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 4 (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0555 c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-cP-at233442 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1423-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0685 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

-- F4-CS0-K1: 21 steps
lem-F4-CS0-K1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0614 c4)) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (sym (wl0721 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (sym (wl0721 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done

-- F4-CS0-K2: 20 steps
lem-F4-CS0-K2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ Bx2-0413 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 4 (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ []) (wp0615 c4) ▸
       at 4 4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (sym (wl0726 (lit c4))) ▸
       at 3 4 (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ []) (wp0616 c4) ▸
       at 2 4 (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (sym (wl0726 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K2 ∷ Bx2-0413 ∷ []) (sym (lem-Ku-box-at0210243143 c4)) ▸
       at 2 2 (CK42 ∷ Bx2-0413 ∷ []) (sym (lem-CKu-box-2-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 5 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 3 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done

-- F4-CS1-K0: 20 steps
lem-F4-CS1-K0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ Bx0-1423 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 4 (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ []) (wp0629 c4) ▸
       at 4 4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (sym (wp0630 c4)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ []) (wp0631 c4) ▸
       at 2 4 (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (sym (wp0630 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K0 ∷ Bx0-1423 ∷ []) (sym (lem-Ku-box-at243243 c4)) ▸
       at 2 2 (CK40 ∷ Bx0-1423 ∷ []) (sym (lem-CKu-box-2-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 5 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 3 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (sym (wp0613 c4)) ▸ done

-- F4-CS1-K2: 21 steps
lem-F4-CS1-K2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0736 (lit c4))) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 4 4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (sym (wp0635 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-1342 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K2 ∷ CCZ013 ∷ []) (wl0737 (lit c4)) ▸
       at 4 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S)) ▸
       at 2 4 (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (sym (wp0635 c4)) ▸
       at 1 2 (K2 ∷ CCZ013 ∷ []) (wl0737 (lit c4)) ▸
       at 2 2 (CK42 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CK42 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S)) ▸
       at 4 4 (Bx0-1342 ∷ []) (sym (lem-box-cP-at233442 c4)) ▸ done

  b2 : Chain (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ Bx0-1342 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1423-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK42 ∷ X4 ∷ []) (sym (wl0728 (lit c4))) ▸ done

-- F4-CS2-K0: 20 steps
lem-F4-CS2-K0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ Bx0-2431 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 4 (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ []) (wp0644 c4) ▸
       at 4 4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (sym (wp0645 c4)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ []) (wp0646 c4) ▸
       at 2 4 (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (sym (wp0645 c4)) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 1 2 (K0 ∷ Bx0-2431 ∷ []) (sym (lem-Ku-box-at122441 c4)) ▸
       at 2 2 (CK40 ∷ Bx0-2431 ∷ []) (sym (lem-CKu-box-2-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 5 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 3 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (sym (wp0613 c4)) ▸ done

-- F0-B @14213243: 62 steps
lem-F0-B-at14213243 : Ws → ⟪ (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Bx3-4102 ∷ []) ⟫ʷ
lem-F0-B-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CZ02 ∷ CCZ014 ∷ CCZ023 ∷ CZ02 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ Toff314 ∷ CX23 ∷ []) (wl0771 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) (sym (wl0772 (lit c4))) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ CX23 ∷ []) (wl0771 (lit c4)) ▸
       at 6 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl0773 (lit c4))) ▸
       at 3 2 (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) (wp0697 c4) ▸
       at 5 2 (Toff314 ∷ CCZ014 ∷ []) (wp0698 c4) ▸
       at 4 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CZ02 ∷ CCZ014 ∷ CCZ023 ∷ CZ02 ∷ []) (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CZ02 ∷ []) (sym (wp0699 c4)) ▸
       at 6 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff214 ∷ []) (wl0775 (lit c4)) ▸
       at 4 0 (CCZ023 ∷ CCZ023 ∷ []) (sym (wl0204 (lit c4))) ▸
       at 1 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 1 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (sym (wl0776 (lit c4))) ▸ done

  b2 : Chain (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff214 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b2 = at 6 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 1 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 1 7 (Toff214 ∷ []) (wl0776 (lit c4)) ▸ done

  b3 : Chain (CCZ034 ∷ Toff214 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b3 = at 1 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (sym (wl0776 (lit c4))) ▸
       at 8 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 7 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b4 : Chain (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b4 = at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 3 7 (Toff214 ∷ []) (wl0776 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b5 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (Bx3-4102 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b5 = at 5 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 4 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 0 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 2 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b6 : Chain (Bx3-4102 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (Bx3-4102 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b6 = at 6 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 4 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX04 ∷ []) (sym (wp0684 c4)) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 4 2 [] (wp0161 c4) ▸ done

  b7 : Chain (Bx3-4102 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ [])
  b7 = at 1 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-box-perm-3124-at0314213042 c4) ▸
       at 1 1 (Bx2-3041 ∷ []) (lem-box-perm-4312-at0214213043 c4) ▸
       at 0 2 (Bx2-3041 ∷ Bx3-0412 ∷ []) (lem-box-box-4-at0310243142 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-box-perm-3421-at0213203441 c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-box-perm-2314-at0310243142 c4) ▸ done

-- box-box-1 @03102132: 105 steps
lem-box-box-1-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-1-at03102132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-0124 ∷ Bx0-3124 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ013 ∷ CX32 ∷ CS34 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-box-perm-2341-at03102132 c4) ▸
       at 0 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 4 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 4 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0183 c4) ▸
       at 6 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 10 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 9 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ013 ∷ CX32 ∷ CS34 ∷ Toff024 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 6 3 (Toff024 ∷ CCZ034 ∷ []) (wp0739 c4) ▸
       at 3 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ Toff024 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 4 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp0587 c4) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸ done

  b3 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ Toff024 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 9 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b4 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff024 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 5 3 (Toff312 ∷ []) (wl0870 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 5 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 11 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸ done

  b5 : Chain (Toff312 ∷ CCZ034 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff024 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ034 ∷ Bx0-3124 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 9 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 5 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 6 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 2 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸ done

  b6 : Chain (Toff312 ∷ CCZ034 ∷ Bx0-3124 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CCZ013 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff024 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 2 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0183 c4) ▸
       at 4 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 7 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX32 ∷ []) (sym (wl0706 (lit c4))) ▸ done

  b7 : Chain (Toff312 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ CS24 ∷ CCZ013 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff024 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff312 ∷ Toff024 ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (sym (wp0186 c4)) ▸
       at 4 3 (Toff024 ∷ CCZ034 ∷ []) (wp0739 c4) ▸
       at 1 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 0 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp0587 c4) ▸ done

  b8 : Chain (CCZ013 ∷ Toff312 ∷ Toff024 ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 7 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 6 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 3 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 2 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 1 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸ done

  b9 : Chain (CCZ013 ∷ Toff024 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ012 ∷ CCZ124 ∷ CCZ013 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ124 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b10 : Chain (CCZ013 ∷ Toff024 ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ124 ∷ Toff024 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff024 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl0850 (lit c4))) ▸
       at 3 3 (Toff312 ∷ []) (wl0870 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 3 1 (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (sym (wl0869 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (wp0190 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸ done

  b11 : Chain (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ Toff024 ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx0-3124 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff024 ∷ CS12⁻ ∷ []) (wp0741 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff312 ∷ []) (wl0869 (lit c4)) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-cP-at132132 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸ done

  b12 : Chain (Bx0-3124 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx0-3124 ∷ Bx3-1240 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

  b13 : Chain (Bx0-3124 ∷ Bx3-1240 ∷ []) (Bx0-3124 ∷ Bx3-0124 ∷ [])
  b13 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-4123-at033440 c4) ▸ done
