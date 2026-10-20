{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0156 ; wl0157 ; wl0158 ; wl0159 ; wl0160 ; wl0161 ; wl0167 ; wl0174 ; wl0175 ; wl0179 ; wl0182 ; wl0200 ; wl0205 ; wl0207 ; wl0226 ; wl0231 ; wl0256 ; wl0268 ; wl0272 ; wl0277 ; wp0004 ; wp0005 ; wp0008 ; wp0011 ; wp0014 ; wp0025 ; wp0026 ; wp0049 ; wp0056 ; wp0057 ; wp0078 ; wp0083 ; wp0084 ; wp0097 ; wp0111 ; wp0115 ; wp0116 ; wp0117 ; wp0129 ; wl0290 ; wl0291 ; wl0292 ; wl0293 ; wl0294 ; wl0295 ; wl0296 ; wl0297 ; wl0298 ; wl0299 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0313 ; wl0314 ; wl0315 ; wl0323 ; wl0329 ; wl0330 ; wl0331 ; wl0332 ; wl0333 ; wl0334 ; wl0338 ; wl0339 ; wl0340 ; wp0130 ; wp0131 ; wp0137 ; wp0138 ; wp0139 ; wp0140 ; wp0141 ; wp0142 ; wp0143 ; wp0144 ; wp0145 ; wp0146 ; wp0147 ; wp0148 ; wp0153 ; wp0154 ; wp0163 ; wp0164 ; wp0165 ; wp0166 ; wp0167 ; wp0168 ; wp0169 ; wp0170 ; wp0171 ; wp0172 ; wp0173 ; wp0174 ; wp0180 ; wp0199 ; wp0200 ; wp0201 ; wp0202 ; wp0203 ; wp0204 ; wp0205 ; wp0210 ; wp0211 ; wp0212 ; wp0214 ; wl0344 ; wl0394 ; wl0395 ; wl0396 ; wl0418 ; wl0419 ; wp0216 ; wp0217 ; wp0218 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0452 ; wl0454 ; wl0455 ; wl0456 ; wl0465 ; wl0466 ; wl0467 ; wl0473 ; wl0474 ; wl0476 ; wl0477 ; wl0479 ; wl0487 ; wl0493 ; wl0494 ; wp0290 ; wp0292 ; wp0294 ; wp0302 ; wp0304 ; wp0315 ; wp0335 ; wp0341 ; wp0342 ; wp0343 ; wp0353 ; wp0354 ; wl0507 ; wl0508 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wp0360 ; wp0361 ; wp0362 ; wp0363 ; wp0364 ; wp0365 ; wp0366 ; wp0367 ; wp0368 ; wp0369 ; wp0377 ; wp0378 ; wp0379 ; wp0380 ; wl0610 ; wl0622 ; wl0623 ; wl0624 ; wl0625 ; wl0640 ; wl0641 ; wp0516 ; wl0704 ; wp0560 ; wp0565 ; wp0598 ; wl0749 ; wl0750 ; wl0781 ; wl0782 ; wp0661 ; wl0842 ; wl0843 ; wl0844 ; wl0845 ; wl0846 ; wl0847 ; wp0732 ; wp0733 ; wl0915 ; wl0916 ; wl0924 ; wl0925 ; wl0926 ; wl0927 ; wl0928 ; wl0932 ; wl0933 ; wl0934 ; wl0938 ; wl0939 ; wl0940 ; wl0941 ; wl0942 ; wl0943)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0213243140 ; lem-box-tQ-at0220 ; lem-box-tQ-at032032 ; lem-box-tQ-at04203243 ; lem-box-tQ-at13243142 ; lem-box-tQ-at13243241 ; lem-box-tQ-at14233142 ; lem-box-tQ-at14233241 ; lem-cQ ; lem-cQ-at0110 ; lem-cQ-at0210233441 ; lem-cQ-at0210243143 ; lem-cQ-at0213203441 ; lem-cQ-at0214203143 ; lem-cQ-at0214213043 ; lem-cQ-at022330 ; lem-cQ-at0310243142 ; lem-cQ-at0312213440 ; lem-cQ-at0312243140 ; lem-cQ-at0314203142 ; lem-cQ-at0314213042 ; lem-cQ-at0330 ; lem-cQ-at033440 ; lem-cQ-at043043 ; lem-cQ-at1221 ; lem-cQ-at12213443 ; lem-cQ-at122331 ; lem-cQ-at12233441 ; lem-cQ-at12243143 ; lem-cQ-at122441 ; lem-cQ-at132132 ; lem-cQ-at13213442 ; lem-cQ-at1331 ; lem-cQ-at133441 ; lem-cQ-at14213243 ; lem-cQ-at143143 ; lem-cQ-at1441 ; lem-cQ-at2332 ; lem-cQ-at233442 ; lem-cQ-at243243 ; lem-cQ-at2442 ; lem-cQ-at3443 ; lem-tP-at021021 ; lem-tP-at0210213443 ; lem-tP-at0220 ; lem-tP-at03102132 ; lem-tP-at032032 ; lem-tP-at0410213243 ; lem-tP-at04203243 ; lem-tP-at13243142 ; lem-tP-at13243241 ; lem-tP-at14233142 ; lem-tP-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd12-TOFF034 ; lem-comm-CZ04-CCZ123 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ23-CCZ014 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF034-CSd12 ; lem-comm-TOFF301-CSd24 ; lem-comm-TOFF401-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-TOFF401 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-TOFF301 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-SWAP03-BOX⟨2·14⟩)

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

-- box-tQ @2442: 13 steps
lem-box-tQ-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1432 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (wp0056 c4) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at2442 c4) ▸
       at 2 4 (Toff014 ∷ []) (wp0057 c4) ▸ done

-- box-tQ @12233441: 13 steps
lem-box-tQ-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (wl0308 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at12233441 c4) ▸
       at 2 4 (Toff023 ∷ []) (wl0309 (lit c4)) ▸ done

-- tP @0110: 7 steps
lem-tP-at0110 : Ws → ⟪ (Toff102 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ []) ⟫ʷ
lem-tP-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Toff134 ∷ []) (Toff134 ∷ Toff102 ∷ [])
  b0 = at 0 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (sym (wl0394 (lit c4))) ▸
       at 3 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (sym (wl0395 (lit c4))) ▸
       at 2 2 [] (wl0396 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-cQ-at0110 c4) ▸
       at 2 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0396 (lit c4))) ▸
       at 0 3 (Toff134 ∷ []) (wl0395 (lit c4)) ▸
       at 1 3 (Toff102 ∷ []) (wl0394 (lit c4)) ▸ done

-- box-tQ @133441: 13 steps
lem-box-tQ-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at133441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3241 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0217 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp0217 c4)) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (wl0308 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at133441 c4) ▸
       at 2 4 (Toff023 ∷ []) (wl0309 (lit c4)) ▸ done

-- P-box @13243241: 8 steps
lem-P-box-at13243241 : Ws → ⟪ (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-P-box-at13243241 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243241 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243241 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (sym (wl0338 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243241 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (sym (wl0339 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done

-- VPQ @13243241: 14 steps
lem-VPQ-at13243241 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸ done

-- box-tQ @233442: 13 steps
lem-box-tQ-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (wl0290 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at233442 c4) ▸
       at 2 4 (Toff013 ∷ []) (wl0291 (lit c4)) ▸ done

-- VPQ @021021: 14 steps
lem-VPQ-at021021 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at021021 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸ done

-- P-box @13243142: 8 steps
lem-P-box-at13243142 : Ws → ⟪ (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-P-box-at13243142 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at13243142 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243142 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (sym (wl0338 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at13243142 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (sym (wl0339 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done

-- VPQ @13243142: 14 steps
lem-VPQ-at13243142 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸ done

-- VPQ @03102132: 14 steps
lem-VPQ-at03102132 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 3 2 (CS24⁻ ∷ S3⁻ ∷ []) (sym (wl0439 (lit c4))) ▸
       at 2 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S3 ∷ []) (sym (wl0440 (lit c4))) ▸
       at 0 2 (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑)) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑)) ▸
       at 0 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸
       at 2 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸ done

-- tP @3443: 7 steps
lem-tP-at3443 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at3443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at3443 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff034 ∷ []) (wp0004 c4) ▸
       at 1 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸ done

-- VPQ @0410213243: 14 steps
lem-VPQ-at0410213243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (sym (wp0304 c4)) ▸
       at 4 2 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (sym (wl0455 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S4⁻ ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS23⁻ ∷ Toff401 ∷ []) (lem-comm-TOFF401-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S4 ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S))) ▸
       at 0 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑)) ▸
       at 2 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 3 2 (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑)) ▸
       at 0 4 (Toff423 ∷ CCZ234 ∷ []) (wl0455 (lit c4)) ▸
       at 2 4 (Toff401 ∷ CCZ014 ∷ []) (wp0304 c4) ▸ done

-- box-tQ @043043: 13 steps
lem-box-tQ-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1203 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at043043 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done

-- tP @043043: 7 steps
lem-tP-at043043 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at043043 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at043043 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done

-- box-tQ @0330: 13 steps
lem-box-tQ-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1204 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0473 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0330 c4) ▸
       at 2 4 (Toff312 ∷ []) (wl0474 (lit c4)) ▸ done

-- VPQ @04203243: 14 steps
lem-VPQ-at04203243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (sym (wp0304 c4)) ▸
       at 4 2 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (sym (wl0455 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S4⁻ ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS23⁻ ∷ Toff401 ∷ []) (lem-comm-TOFF401-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S4 ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S))) ▸
       at 0 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑)) ▸
       at 2 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 3 2 (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑)) ▸
       at 0 4 (Toff423 ∷ CCZ234 ∷ []) (wl0455 (lit c4)) ▸
       at 2 4 (Toff401 ∷ CCZ014 ∷ []) (wp0304 c4) ▸ done

-- tP @0330: 7 steps
lem-tP-at0330 : Ws → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at0330 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0330 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff304 ∷ []) (wp0343 c4) ▸
       at 1 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸ done

-- box-tQ @0310243142: 13 steps
lem-box-tQ-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0412 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243142 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done

-- tP @0314203142: 7 steps
lem-tP-at0314203142 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203142 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸
       at 1 3 (Toff304 ∷ []) (wp0343 c4) ▸ done

-- tP @0310243142: 7 steps
lem-tP-at0310243142 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243142 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸
       at 1 3 (Toff304 ∷ []) (wp0343 c4) ▸ done

-- CXbc-box @04203243: 17 steps
lem-CXbc-box-at04203243 : Ws → ⟪ (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX02 ∷ CCZ034 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CCZ234 ∷ CX10 ∷ CS13 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ CX02 ∷ []) (wp0360 c4) ▸
       at 1 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (sym (wp0361 c4)) ▸
       at 3 2 (Toff401 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0362 c4) ▸
       at 2 2 (Toff401 ∷ CX02 ∷ []) (wp0360 c4) ▸
       at 5 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX02 ∷ CCZ034 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CCZ234 ∷ CX10 ∷ CS13 ∷ CX02 ∷ []) (Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS03⁻ ∷ []) (sym (wp0363 c4)) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 3 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (sym (wp0361 c4)) ▸
       at 4 3 (CX02 ∷ []) (wp0364 c4) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done

  b2 : Chain (Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ []) (Bx4-1023 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wl0479 (lit c4))) ▸ done

-- CXcb-box @04203243: 18 steps
lem-CXcb-box-at04203243 : Ws → ⟪ (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) (Toff401 ∷ CCZ234 ∷ CX20 ∷ Toff412 ∷ CS23 ∷ CX12 ∷ Toff401 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ234 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ CX20 ∷ Toff412 ∷ []) (wp0365 c4) ▸
       at 2 2 (CCZ234 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl0507 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS13 ∷ []) (wp0367 c4) ▸
       at 7 2 (Toff401 ∷ CX12 ∷ []) (wp0368 c4) ▸
       at 6 2 (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ CX20 ∷ Toff412 ∷ CS23 ∷ CX12 ∷ Toff401 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ234 ∷ CX20 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ [])
  b1 = at 5 2 (Toff401 ∷ CX12 ∷ []) (wp0368 c4) ▸
       at 4 2 (Toff401 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF401 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff401 ∷ Toff412 ∷ []) (sym (wp0335 c4)) ▸
       at 2 2 (Toff401 ∷ CX20 ∷ Toff412 ∷ []) (wp0365 c4) ▸
       at 3 3 (CX20 ∷ []) (wp0369 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ []) (Bx4-1023 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0476 (lit c4))) ▸ done

-- CXbc-box @032032: 17 steps
lem-CXbc-box-at032032 : Ws → ⟪ (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX02 ∷ CCZ034 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ CX02 ∷ []) (wl0521 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (sym (wp0361 c4)) ▸
       at 3 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp0377 c4) ▸
       at 2 2 (Toff301 ∷ CX02 ∷ []) (wl0521 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX02 ∷ CCZ034 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX02 ∷ []) (Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 3 2 (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (sym (wp0361 c4)) ▸
       at 4 3 (CX02 ∷ []) (wp0364 c4) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done

  b2 : Chain (Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-1024 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0378 c4)) ▸ done

-- CXcb-box @032032: 18 steps
lem-CXcb-box-at032032 : Ws → ⟪ (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) (Toff301 ∷ CCZ234 ∷ CX20 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ Toff301 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ234 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ CX20 ∷ Toff312 ∷ []) (wl0522 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl0523 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS14 ∷ []) (wp0379 c4) ▸
       at 7 2 (Toff301 ∷ CX12 ∷ []) (wl0524 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ CX20 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ Toff301 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ234 ∷ CX20 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 5 2 (Toff301 ∷ CX12 ∷ []) (wl0524 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff312 ∷ []) (sym (wl0525 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CX20 ∷ Toff312 ∷ []) (wl0522 (lit c4)) ▸
       at 3 3 (CX20 ∷ []) (wl0526 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ124 ∷ []) (wl0527 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-1024 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸ done

-- box-tQ @0214203143: 13 steps
lem-box-tQ-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4013 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0025 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0214203143 c4) ▸
       at 2 4 (Toff204 ∷ []) (wp0026 c4) ▸ done

-- box-tQ @0214213043: 13 steps
lem-box-tQ-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4103 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 0 2 (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) (wl0622 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at0214213043 c4) ▸
       at 2 4 (Toff214 ∷ []) (wl0623 (lit c4)) ▸ done

-- tP @0214213043: 7 steps
lem-tP-at0214213043 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at0214213043 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at0214213043 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸ done

-- box-tQ @0210233441: 13 steps
lem-box-tQ-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0341 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 0 2 (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) (wl0640 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0210233441 c4) ▸
       at 2 4 (Toff203 ∷ []) (wl0641 (lit c4)) ▸ done

-- tP @0210233441: 7 steps
lem-tP-at0210233441 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0210233441 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0210233441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸
       at 1 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸ done

-- tP @12233441: 7 steps
lem-tP-at12233441 : Ws → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at12233441 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at12233441 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff014 ∷ []) (wp0049 c4) ▸
       at 1 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸ done

-- box-tQ @14213243: 13 steps
lem-box-tQ-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (wp0056 c4) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at14213243 c4) ▸
       at 2 4 (Toff014 ∷ []) (wp0057 c4) ▸ done

-- box-tQ @143143: 13 steps
lem-box-tQ-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0180 c4)) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (wp0083 c4) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at143143 c4) ▸
       at 2 4 (Toff024 ∷ []) (wp0084 c4) ▸ done

-- tP @143143: 7 steps
lem-tP-at143143 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at143143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at143143 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done

-- tP @233442: 7 steps
lem-tP-at233442 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at233442 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at233442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff024 ∷ []) (wp0078 c4) ▸
       at 1 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸ done

-- VPQ @0210213443: 14 steps
lem-VPQ-at0210213443 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0210213443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸ done

-- P-box @14233241: 8 steps
lem-P-box-at14233241 : Ws → ⟪ (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-P-box-at14233241 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233241 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (sym (wl0338 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233241 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (sym (wl0339 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0340 (lit c4))) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done

-- VPQ @14233241: 14 steps
lem-VPQ-at14233241 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸ done

-- box-tQ @12213443: 13 steps
lem-box-tQ-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2143 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0160 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at12213443 c4) ▸
       at 2 4 (Toff012 ∷ []) (wl0161 (lit c4)) ▸ done

-- tP @12213443: 7 steps
lem-tP-at12213443 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at12213443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at12213443 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff034 ∷ []) (wp0004 c4) ▸
       at 1 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸ done

-- box-tQ @0314213042: 13 steps
lem-box-tQ-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213042 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done

-- tP @0213203441: 7 steps
lem-tP-at0213203441 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0213203441 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0213203441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸
       at 1 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸ done

-- box-tQ @0314203142: 13 steps
lem-box-tQ-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203142 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done

-- tP @0314213042: 7 steps
lem-tP-at0314213042 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213042 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done

-- P-box @032032: 8 steps
lem-P-box-at032032 : Ws → ⟪ (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-P-box-at032032 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at032032 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (sym (wl0842 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at032032 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ24 ∷ []) (sym (wl0843 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0844 (lit c4))) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done

-- VPQ @032032: 14 steps
lem-VPQ-at032032 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 3 2 (CS24⁻ ∷ S3⁻ ∷ []) (sym (wl0439 (lit c4))) ▸
       at 2 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S3 ∷ []) (sym (wl0440 (lit c4))) ▸
       at 0 2 (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑)) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑)) ▸
       at 0 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸
       at 2 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸ done

-- box-tQ @0312243140: 13 steps
lem-box-tQ-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2410 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0845 (lit c4))) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243140 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done

-- box-tQ @033440: 13 steps
lem-box-tQ-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0473 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at033440 c4) ▸
       at 2 4 (Toff312 ∷ []) (wl0474 (lit c4)) ▸ done

-- box-tQ @0312213440: 13 steps
lem-box-tQ-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0312213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2140 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0473 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0312213440 c4) ▸
       at 2 4 (Toff312 ∷ []) (wl0474 (lit c4)) ▸ done

-- tP @0312243140: 7 steps
lem-tP-at0312243140 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at0312243140 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243140 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸
       at 1 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸ done

-- box-tQ @022330: 13 steps
lem-box-tQ-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at022330 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done

-- nat-SWbc @022330: 23 steps
lem-nat-SWbc-at022330 : Ws → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-nat-SWbc-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ Sw03 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw03 ∷ []) (wl0925 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸
       at 4 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 5 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ Sw03 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ Sw03 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Sw03 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 7 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 8 2 (Toff201 ∷ Sw03 ∷ []) (wl0925 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸
       at 12 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Sw03 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Sw03 ∷ []) (Bx2-1034 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 15 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx1-234 ∷ []) (refl) ▸
       at 5 6 (Bx1-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done

-- P-box @0220: 8 steps
lem-P-box-at0220 : Ws → ⟪ (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-P-box-at0220 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0220 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (sym (wl0932 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0220 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ34 ∷ []) (sym (wl0933 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0934 (lit c4))) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done

-- VPQ @0220: 14 steps
lem-VPQ-at0220 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸ done

-- CXbc-box @0213243140: 17 steps
lem-CXbc-box-at0213243140 : Ws → ⟪ (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX41 ∷ CCZ024 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CCZ012 ∷ CX34 ∷ CS03 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ CX41 ∷ []) (wl0938 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (sym (wp0138 c4)) ▸
       at 3 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0290 c4) ▸
       at 2 2 (Toff234 ∷ CX41 ∷ []) (wl0938 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 9 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX41 ∷ CCZ024 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CCZ012 ∷ CX34 ∷ CS03 ∷ CX41 ∷ []) (Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸
       at 4 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 3 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (sym (wp0138 c4)) ▸
       at 4 3 (CX41 ∷ []) (wp0143 c4) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done

  b2 : Chain (Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-3410 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done

-- CXcb-box @0213243140: 18 steps
lem-CXcb-box-at0213243140 : Ws → ⟪ (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) (Toff234 ∷ CCZ012 ∷ CX14 ∷ Toff213 ∷ CS01 ∷ CX31 ∷ Toff234 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ012 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ CX14 ∷ Toff213 ∷ []) (wl0939 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX14 ∷ []) (sym (wp0145 c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (wp0292 c4) ▸
       at 7 2 (Toff234 ∷ CX31 ∷ []) (wl0941 (lit c4)) ▸
       at 6 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ CX14 ∷ Toff213 ∷ CS01 ∷ CX31 ∷ Toff234 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ012 ∷ CX14 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff234 ∷ CX31 ∷ []) (wl0941 (lit c4)) ▸
       at 4 2 (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 2 2 (Toff234 ∷ CX14 ∷ Toff213 ∷ []) (wl0939 (lit c4)) ▸
       at 3 3 (CX14 ∷ []) (wl0943 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX14 ∷ []) (sym (wp0145 c4)) ▸ done

  b2 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-3410 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done
