{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0158 ; wl0159 ; wl0162 ; wl0163 ; wl0164 ; wl0166 ; wl0172 ; wl0173 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0201 ; wl0202 ; wl0207 ; wl0222 ; wl0227 ; wl0228 ; wl0230 ; wl0245 ; wl0246 ; wl0250 ; wl0251 ; wl0252 ; wl0253 ; wl0254 ; wl0255 ; wl0256 ; wl0257 ; wl0271 ; wl0272 ; wl0273 ; wl0274 ; wl0275 ; wl0276 ; wl0277 ; wl0279 ; wl0281 ; wp0001 ; wp0002 ; wp0003 ; wp0005 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0027 ; wp0028 ; wp0047 ; wp0048 ; wp0050 ; wp0053 ; wp0058 ; wp0059 ; wp0067 ; wp0076 ; wp0077 ; wp0079 ; wp0081 ; wp0085 ; wp0086 ; wp0087 ; wp0090 ; wp0092 ; wp0096 ; wp0097 ; wp0100 ; wp0101 ; wp0102 ; wp0103 ; wp0104 ; wp0105 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0110 ; wp0112 ; wp0113 ; wp0114 ; wp0120 ; wp0121 ; wp0122 ; wp0123 ; wp0124 ; wp0125 ; wp0126 ; wp0127 ; wp0128 ; wp0129 ; wl0293 ; wl0295 ; wl0297 ; wl0299 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0305 ; wl0310 ; wl0312 ; wl0314 ; wl0315 ; wl0316 ; wl0317 ; wl0318 ; wl0319 ; wl0320 ; wl0321 ; wl0324 ; wl0325 ; wl0326 ; wl0327 ; wl0335 ; wl0336 ; wl0337 ; wl0341 ; wp0132 ; wp0133 ; wp0134 ; wp0142 ; wp0158 ; wp0159 ; wp0160 ; wp0161 ; wp0167 ; wp0173 ; wp0181 ; wp0182 ; wp0183 ; wp0184 ; wp0185 ; wp0186 ; wp0187 ; wp0188 ; wp0189 ; wp0190 ; wp0191 ; wp0192 ; wp0193 ; wl0347 ; wl0348 ; wl0349 ; wl0350 ; wl0351 ; wl0352 ; wl0353 ; wl0354 ; wl0355 ; wl0356 ; wl0357 ; wl0358 ; wl0359 ; wl0360 ; wl0361 ; wl0368 ; wl0369 ; wl0370 ; wl0371 ; wl0372 ; wl0373 ; wl0374 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0401 ; wl0404 ; wl0420 ; wl0422 ; wp0221 ; wp0222 ; wp0223 ; wp0224 ; wp0225 ; wp0226 ; wp0227 ; wp0228 ; wp0229 ; wp0263 ; wp0264 ; wp0265 ; wp0266 ; wp0267 ; wp0268 ; wp0269 ; wp0270 ; wp0271 ; wp0272 ; wp0281 ; wp0282 ; wp0283 ; wl0441 ; wl0442 ; wl0444 ; wl0456 ; wl0457 ; wl0468 ; wl0469 ; wl0475 ; wl0476 ; wl0477 ; wl0478 ; wl0479 ; wl0481 ; wl0482 ; wl0483 ; wl0488 ; wl0490 ; wl0492 ; wl0495 ; wp0284 ; wp0285 ; wp0286 ; wp0287 ; wp0296 ; wp0301 ; wp0308 ; wp0312 ; wp0313 ; wp0314 ; wp0316 ; wp0320 ; wp0330 ; wp0331 ; wp0332 ; wp0333 ; wp0334 ; wp0335 ; wp0336 ; wp0341 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wl0499 ; wl0504 ; wl0505 ; wl0506 ; wl0509 ; wl0510 ; wl0525 ; wl0532 ; wl0533 ; wl0534 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0560 ; wl0561 ; wl0562 ; wp0378 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0388 ; wp0422 ; wp0423 ; wp0424 ; wp0425 ; wp0426 ; wp0427 ; wp0431 ; wp0432 ; wp0433 ; wp0434 ; wp0435 ; wp0436 ; wl0582 ; wl0612 ; wl0613 ; wl0614 ; wl0615 ; wl0616 ; wl0617 ; wl0618 ; wl0626 ; wl0627 ; wl0628 ; wp0449 ; wp0450 ; wp0451 ; wp0452 ; wp0453 ; wp0454 ; wp0455 ; wp0480 ; wp0481 ; wp0487 ; wp0488 ; wp0497 ; wp0498 ; wp0499 ; wp0500 ; wp0501 ; wp0502 ; wp0503 ; wp0504 ; wp0505)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-CXbc-box-at032032 ; lem-CXbc-box-at04203243 ; lem-CXbc-box-at13243142 ; lem-CXbc-box-at13243241 ; lem-CXbc-box-at14233142 ; lem-CXcb-box-at032032 ; lem-CXcb-box-at04203243 ; lem-CXcb-box-at13243142 ; lem-CXcb-box-at13243241 ; lem-CXcb-box-at14233142 ; lem-VPQ-at021021 ; lem-VPQ-at03102132 ; lem-VPQ-at0410213243 ; lem-VPQ-at04203243 ; lem-VPQ-at13243142 ; lem-VPQ-at13243241 ; lem-VPQ-at14233142 ; lem-box-tQ ; lem-box-tQ-at0210243143 ; lem-box-tQ-at0214203143 ; lem-box-tQ-at0214213043 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0330 ; lem-box-tQ-at043043 ; lem-box-tQ-at1221 ; lem-box-tQ-at122331 ; lem-box-tQ-at12243143 ; lem-box-tQ-at122441 ; lem-box-tQ-at132132 ; lem-box-tQ-at13213442 ; lem-box-tQ-at1331 ; lem-box-tQ-at133441 ; lem-box-tQ-at2332 ; lem-box-tQ-at243243 ; lem-box-tQ-at3443 ; lem-tP ; lem-tP-at0110 ; lem-tP-at0210243143 ; lem-tP-at0214213043 ; lem-tP-at0310243142 ; lem-tP-at0314203142 ; lem-tP-at0330 ; lem-tP-at043043 ; lem-tP-at1221 ; lem-tP-at122331 ; lem-tP-at122441 ; lem-tP-at132132 ; lem-tP-at13213442 ; lem-tP-at1331 ; lem-tP-at2332 ; lem-tP-at243243 ; lem-tP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CS12-CCZ034 ; lem-comm-CS13-TOFF024 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd02-TOFF134 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd12-TOFF034 ; lem-comm-CSd12-TOFF403 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX12-CCZ034 ; lem-comm-CX21-CCZ034 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034 ; lem-comm-CZ14-TOFF023 ; lem-comm-CZ24-TOFF013 ; lem-comm-TOFF013-CSd24 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF024-CSd13 ; lem-comm-TOFF204-CSd13 ; lem-comm-TOFF312-CSd04 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS04-CCZ123 ; lem-comm-CS04-TOFF312 ; lem-comm-CS13-TOFF204 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX40-CCZ123 ; lem-comm-CZ03-TOFF214 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ12-TOFF403 ; lem-comm-TOFF304-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CSd14)

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

-- QVQ @14233142: 3 steps
lem-QVQ-at14233142 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at14233142 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

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

-- VPQ @1331: 14 steps
lem-VPQ-at1331 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (sym (wl0202 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸ done

-- Su-box: 17 steps
lem-Su-box : Ws → ⟪ (S0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0 ∷ Bx0-1234 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (wl0347 (lit c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ S0 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0 ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ S0 ∷ []) (sym (wp0222 c4)) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl0164 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (wl0349 (lit c4)) ▸
       at 2 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (wl0347 (lit c4)) ▸
       at 3 6 (S0 ∷ []) (wl0350 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ S0 ∷ []) (sym (wp0222 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0 ∷ []) (Bx0-1234 ∷ S0 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- Sdu-box: 17 steps
lem-Sdu-box : Ws → ⟪ (S0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ
lem-Sdu-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0⁻ ∷ Bx0-1234 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl0351 (lit c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0⁻ ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ S0⁻ ∷ []) (sym (wp0223 c4)) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl0164 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (wl0352 (lit c4)) ▸
       at 2 2 (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl0351 (lit c4)) ▸
       at 3 6 (S0⁻ ∷ []) (wl0353 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ S0⁻ ∷ []) (sym (wp0223 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0⁻ ∷ []) (Bx0-1234 ∷ S0⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CSu-box-1: 17 steps
lem-CSu-box-1 : Ws → ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ
lem-CSu-box-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) (wl0354 (lit c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01 ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl0164 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (wl0349 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) (wl0354 (lit c4)) ▸
       at 3 6 (CS01 ∷ []) (wl0355 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01 ∷ []) (Bx0-1234 ∷ CS01 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CSdu-box-1: 17 steps
lem-CSdu-box-1 : Ws → ⟪ (CS01⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSdu-box-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01⁻ ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl0356 (lit c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01⁻ ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl0164 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (wl0352 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl0356 (lit c4)) ▸
       at 3 6 (CS01⁻ ∷ []) (wl0357 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01⁻ ∷ []) (Bx0-1234 ∷ CS01⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CZu-box-1: 9 steps
lem-CZu-box-1 : Ws → ⟪ (CZ01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZu-box-1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ01 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) (wl0358 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CZ01 ∷ []) (sym (wp0224 c4)) ▸
       at 3 2 (Toff012 ∷ CZ12 ∷ []) (wl0359 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) (wl0358 (lit c4)) ▸
       at 3 3 (CZ01 ∷ []) (wl0360 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CZ01 ∷ []) (sym (wp0224 c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ01 ∷ []) (Bx0-1234 ∷ CZ01 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CXu-box-1: 15 steps
lem-CXu-box-1 : Ws → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CXu-box-1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX10 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ CX10 ∷ CS34 ∷ Toff012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CX10 ∷ []) (wl0361 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (sym (wp0225 c4)) ▸
       at 3 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CS14 ∷ []) (wp0102 c4) ▸
       at 6 2 (Toff012 ∷ CX13 ∷ []) (wl0251 (lit c4)) ▸
       at 5 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 4 2 (Toff012 ∷ CX13 ∷ []) (wl0251 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX10 ∷ CS34 ∷ Toff012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  b1 = at 3 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 2 2 (Toff012 ∷ CX10 ∷ []) (wl0361 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 3 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (sym (wp0225 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp0226 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CSu-box-2: 17 steps
lem-CSu-box-2 : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wl0368 (lit c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02 ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl0164 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (wl0349 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wl0368 (lit c4)) ▸
       at 3 6 (CS02 ∷ []) (wl0369 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CSdu-box-2: 17 steps
lem-CSdu-box-2 : Ws → ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl0370 (lit c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02⁻ ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl0164 (lit c4)) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (wl0352 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl0370 (lit c4)) ▸
       at 3 6 (CS02⁻ ∷ []) (wl0371 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS02⁻ ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CZu-box-2: 9 steps
lem-CZu-box-2 : Ws → ⟪ (CZ02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ []) ⟫ʷ
lem-CZu-box-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ02 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ02 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) (wl0372 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CZ02 ∷ []) (sym (wp0227 c4)) ▸
       at 3 2 (Toff012 ∷ CZ12 ∷ []) (wl0359 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) (wl0372 (lit c4)) ▸
       at 3 3 (CZ02 ∷ []) (wl0373 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CZ02 ∷ []) (sym (wp0227 c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CZ02 ∷ []) (Bx0-1234 ∷ CZ02 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- CXu-box-2: 15 steps
lem-CXu-box-2 : Ws → ⟪ (CX20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX20 ∷ []) ⟫ʷ
lem-CXu-box-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX20 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ CX20 ∷ CS34 ∷ Toff012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CX20 ∷ []) (wl0374 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (sym (wp0228 c4)) ▸
       at 3 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CS24 ∷ []) (wp0128 c4) ▸
       at 6 2 (Toff012 ∷ CX23 ∷ []) (wl0255 (lit c4)) ▸
       at 5 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 4 2 (Toff012 ∷ CX23 ∷ []) (wl0255 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX20 ∷ CS34 ∷ Toff012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ []) (Bx0-1234 ∷ CX20 ∷ [])
  b1 = at 3 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 2 2 (Toff012 ∷ CX20 ∷ []) (wl0374 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (sym (wp0228 c4)) ▸
       at 4 3 (CX20 ∷ []) (wp0229 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

-- VPQ @0110: 14 steps
lem-VPQ-at0110 : Ws → ⟪ (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (CS34⁻ ∷ CS02⁻ ∷ S1 ∷ Toff134 ∷ Toff102 ∷ S1⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) (sym (wl0397 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) (sym (wl0398 (lit c4))) ▸
       at 3 2 (CS34⁻ ∷ S1⁻ ∷ []) (c₂ ((S • S • S) ↑) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S1 ∷ []) (c₂ (S ↑) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS • CS • CS)) ▸
       at 4 2 [] (wl0399 (lit c4)) ▸
       at 3 2 (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS02⁻ ∷ S1 ∷ Toff134 ∷ Toff102 ∷ S1⁻ ∷ []) (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S1⁻ ∷ S1 ∷ []) (sym (wl0399 (lit c4))) ▸
       at 1 2 (S1 ∷ CS02⁻ ∷ []) (wl0400 (lit c4)) ▸
       at 2 2 (Toff134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF134 (lit c4)) ▸
       at 3 2 (S1⁻ ∷ CS02⁻ ∷ []) (wl0401 (lit c4)) ▸
       at 0 4 (Toff134 ∷ CCZ134 ∷ []) (wl0398 (lit c4)) ▸
       at 2 4 (Toff102 ∷ CCZ012 ∷ []) (wl0397 (lit c4)) ▸ done

-- CXbc-box @133441: 17 steps
lem-CXbc-box-at133441 : Ws → ⟪ (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX24 ∷ CCZ012 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at133441 c4) ▸
       at 0 2 (Toff023 ∷ CX24 ∷ []) (wp0263 c4) ▸
       at 1 2 (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (sym (wp0264 c4)) ▸
       at 3 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl0404 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CX24 ∷ []) (wp0263 c4) ▸
       at 5 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX24 ∷ CCZ012 ∷ CS12 ∷ CX32 ∷ CS12⁻ ∷ CCZ014 ∷ CX32 ∷ CS13 ∷ CX24 ∷ []) (Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0314 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 3 2 (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (sym (wp0264 c4)) ▸
       at 4 3 (CX24 ∷ []) (wp0266 c4) ▸
       at 0 4 (Bx0-3241 ∷ []) (sym (lem-box-tQ-at133441 c4)) ▸ done

  b2 : Chain (Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0315 (lit c4))) ▸ done

-- CXcb-box @133441: 18 steps
lem-CXcb-box-at133441 : Ws → ⟪ (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) (Toff023 ∷ CCZ014 ∷ CX42 ∷ Toff034 ∷ CS14 ∷ CX34 ∷ Toff023 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ014 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at133441 c4) ▸
       at 0 2 (Toff023 ∷ CX42 ∷ Toff034 ∷ []) (wp0267 c4) ▸
       at 2 2 (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) (sym (wp0268 c4)) ▸
       at 1 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸
       at 4 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0310 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CX34 ∷ []) (wp0270 c4) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX42 ∷ Toff034 ∷ CS14 ∷ CX34 ∷ Toff023 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ CCZ014 ∷ CX42 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX34 ∷ []) (wp0270 c4) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Toff034 ∷ []) (sym (wp0173 c4)) ▸
       at 2 2 (Toff023 ∷ CX42 ∷ Toff034 ∷ []) (wp0267 c4) ▸
       at 3 3 (CX42 ∷ []) (wp0271 c4) ▸
       at 4 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 3 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-3241 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-3241 ∷ []) (sym (lem-box-tQ-at133441 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0312 (lit c4))) ▸ done

-- QVQ @13243241: 3 steps
lem-QVQ-at13243241 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243241 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at13243241 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @021021: 3 steps
lem-QVQ-at021021 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at021021 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at021021 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- CXbc-box @13213442: 17 steps
lem-CXbc-box-at13213442 : Ws → ⟪ (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX14 ∷ CCZ012 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 0 2 (Toff013 ∷ CX14 ∷ []) (wp0281 c4) ▸
       at 1 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (sym (wp0282 c4)) ▸
       at 3 2 (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl0422 (lit c4)) ▸
       at 2 2 (Toff013 ∷ CX14 ∷ []) (wp0281 c4) ▸
       at 5 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX14 ∷ CCZ012 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX14 ∷ []) (Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4) ▸
       at 3 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (sym (wp0282 c4)) ▸
       at 4 3 (CX14 ∷ []) (wp0283 c4) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done

  b2 : Chain (Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0299 (lit c4))) ▸ done

-- CXcb-box @13213442: 18 steps
lem-CXcb-box-at13213442 : Ws → ⟪ (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) (Toff013 ∷ CCZ024 ∷ CX41 ∷ Toff034 ∷ CS24 ∷ CX34 ∷ Toff013 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ024 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 0 2 (Toff013 ∷ CX41 ∷ Toff034 ∷ []) (wp0284 c4) ▸
       at 2 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 1 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CX34 ∷ []) (wp0286 c4) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX41 ∷ Toff034 ∷ CS24 ∷ CX34 ∷ Toff013 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ024 ∷ CX41 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX34 ∷ []) (wp0286 c4) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 2 2 (Toff013 ∷ CX41 ∷ Toff034 ∷ []) (wp0284 c4) ▸
       at 3 3 (CX41 ∷ []) (wp0287 c4) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-3142 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0295 (lit c4))) ▸ done

-- QVQ @13243142: 3 steps
lem-QVQ-at13243142 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at13243142 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @03102132: 3 steps
lem-QVQ-at03102132 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at03102132 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- P-box @3443: 8 steps
lem-P-box-at3443 : Ws → ⟪ (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-P-box-at3443 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at3443 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (sym (wp0112 c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at3443 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (sym (wp0113 c4)) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0114 c4)) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

-- VPQ @3443: 14 steps
lem-VPQ-at3443 : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (sym (wl0158 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (sym (wp0005 c4)) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (wp0005 c4) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (wl0158 (lit c4)) ▸ done

-- QVQ @0410213243: 3 steps
lem-QVQ-at0410213243 : Ws → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0457 (lit c4))) ▸
       at 1 4 (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0410213243 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- VPQ @043043: 14 steps
lem-VPQ-at043043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸ done

-- CXbc-box @043043: 17 steps
lem-CXbc-box-at043043 : Ws → ⟪ (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX20 ∷ CCZ234 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 0 2 (Toff412 ∷ CX20 ∷ []) (wp0330 c4) ▸
       at 1 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (sym (wp0228 c4)) ▸
       at 3 2 (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0475 (lit c4)) ▸
       at 2 2 (Toff412 ∷ CX20 ∷ []) (wp0330 c4) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX20 ∷ CCZ234 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX20 ∷ []) (Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (sym (wp0228 c4)) ▸
       at 4 3 (CX20 ∷ []) (wp0229 c4) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done

  b2 : Chain (Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ []) (Bx4-1203 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0476 (lit c4))) ▸ done

-- CXcb-box @043043: 18 steps
lem-CXcb-box-at043043 : Ws → ⟪ (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) (Toff412 ∷ CCZ034 ∷ CX02 ∷ Toff401 ∷ CS03 ∷ CX10 ∷ Toff412 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ CCZ034 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 0 2 (Toff412 ∷ CX02 ∷ Toff401 ∷ []) (wp0331 c4) ▸
       at 2 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (sym (wp0332 c4)) ▸
       at 1 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸
       at 4 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 8 2 (Toff412 ∷ CS13 ∷ []) (wl0478 (lit c4)) ▸
       at 7 2 (Toff412 ∷ CX10 ∷ []) (wp0334 c4) ▸
       at 6 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ CX02 ∷ Toff401 ∷ CS03 ∷ CX10 ∷ Toff412 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ CCZ034 ∷ CX02 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ [])
  b1 = at 5 2 (Toff412 ∷ CX10 ∷ []) (wp0334 c4) ▸
       at 4 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸
       at 3 2 (Toff412 ∷ Toff401 ∷ []) (wp0335 c4) ▸
       at 2 2 (Toff412 ∷ CX02 ∷ Toff401 ∷ []) (wp0331 c4) ▸
       at 3 3 (CX02 ∷ []) (wp0336 c4) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ []) (Bx4-1203 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wl0479 (lit c4))) ▸ done

-- QVQ @04203243: 3 steps
lem-QVQ-at04203243 : Ws → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at04203243 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0457 (lit c4))) ▸
       at 1 4 (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at04203243 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- P-box @0330: 8 steps
lem-P-box-at0330 : Ws → ⟪ (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-P-box-at0330 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at0330 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (sym (wp0344 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at0330 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ04 ∷ []) (sym (wp0345 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0346 c4)) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done

-- VPQ @0330: 14 steps
lem-VPQ-at0330 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 3 2 (CS04⁻ ∷ S3⁻ ∷ []) (sym (wp0348 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S3 ∷ []) (sym (wp0349 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS12⁻ ∷ []) (sym (wp0350 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S)) ▸
       at 2 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S)) ▸
       at 0 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸
       at 2 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸ done

-- VPQ @0314203142: 14 steps
lem-VPQ-at0314203142 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (wp0349 c4) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸ done

-- P-box @0310243142: 8 steps
lem-P-box-at0310243142 : Ws → ⟪ (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-P-box-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243142 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (sym (wl0504 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243142 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ12 ∷ []) (sym (wl0505 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0506 (lit c4))) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done

-- VPQ @0310243142: 14 steps
lem-VPQ-at0310243142 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (wp0349 c4) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸ done

-- SWbc-box @04203243: 11 steps
lem-SWbc-box-at04203243 : Ws → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-SWbc-box-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (CX02 ∷ Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 4 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 2 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04203243 c4) ▸
       at 3 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl0483 (lit c4)) ▸
       at 1 3 (Bx4-1023 ∷ CCZ123 ∷ []) (lem-CXcb-box-at04203243 c4) ▸
       at 4 2 (CX02 ∷ CCZ013 ∷ []) (wl0444 (lit c4)) ▸
       at 3 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl0481 (lit c4)) ▸
       at 2 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl0481 (lit c4)) ▸ done

  b1 : Chain (CX02 ∷ Bx4-1023 ∷ CX02 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (Bx4-1023 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wl0510 (lit c4)) ▸
       at 0 3 (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04203243 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done

-- SWbc-box @032032: 11 steps
lem-SWbc-box-at032032 : Ws → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-SWbc-box-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (CX02 ∷ Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 4 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 2 3 (Bx3-1024 ∷ CCZ014 ∷ []) (lem-CXbc-box-at032032 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 1 3 (Bx3-1024 ∷ CCZ124 ∷ []) (lem-CXcb-box-at032032 c4) ▸
       at 4 2 (CX02 ∷ CCZ014 ∷ []) (wp0308 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 2 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸ done

  b1 : Chain (CX02 ∷ Bx3-1024 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (Bx3-1024 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0383 c4) ▸
       at 0 3 (Bx3-1024 ∷ CCZ014 ∷ []) (lem-CXbc-box-at032032 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- t-cP @043043: 5 steps
lem-t-cP-at043043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-t-cP-at043043 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) (sym (wl0532 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸
       at 2 3 (CCZ124 ∷ Toff412 ∷ []) (sym (wl0533 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸ done

-- CXbc-box @0330: 17 steps
lem-CXbc-box-at0330 : Ws → ⟪ (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX20 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (sym (wp0228 c4)) ▸
       at 3 2 (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0535 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4)) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX20 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CX20 ∷ []) (Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (sym (wp0228 c4)) ▸
       at 4 3 (CX20 ∷ []) (wp0229 c4) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done

  b2 : Chain (Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-1204 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸ done

-- CXcb-box @0330: 18 steps
lem-CXcb-box-at0330 : Ws → ⟪ (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) (Toff312 ∷ CCZ034 ∷ CX02 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ Toff312 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ034 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4) ▸
       at 0 2 (Toff312 ∷ CX02 ∷ Toff301 ∷ []) (wl0536 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp0388 c4)) ▸
       at 1 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX02 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ Toff312 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ034 ∷ CX02 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX02 ∷ Toff301 ∷ []) (wl0536 (lit c4)) ▸
       at 3 3 (CX02 ∷ []) (wl0538 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 3 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-1204 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0378 c4)) ▸ done

-- CSdu-box-2 @243243: 17 steps
lem-CSdu-box-2-at243243 : Ws → ⟪ (CS04⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx0-1423 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp0422 c4) ▸
       at 3 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 7 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 6 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 2 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 4 2 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (wp0059 c4) ▸
       at 3 2 (Toff014 ∷ CS14⁻ ∷ []) (wp0423 c4) ▸
       at 2 2 (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp0422 c4) ▸
       at 3 6 (CS04⁻ ∷ []) (wp0424 c4) ▸
       at 3 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04⁻ ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

-- Su-box @243243: 17 steps
lem-Su-box-at243243 : Ws → ⟪ (S0 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0 ∷ Bx0-1423 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) (wp0425 c4) ▸
       at 3 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 7 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 6 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ S0 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ S0 ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ S0 ∷ []) (sym (wl0561 (lit c4))) ▸
       at 4 2 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (wp0059 c4) ▸
       at 3 2 (Toff014 ∷ CS14 ∷ []) (wp0426 c4) ▸
       at 2 2 (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) (wp0425 c4) ▸
       at 3 6 (S0 ∷ []) (wp0427 c4) ▸
       at 3 2 (CCZ023 ∷ S0 ∷ []) (sym (wl0561 (lit c4))) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ S0 ∷ []) (Bx0-1423 ∷ S0 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

-- CSdu-box-2 @122441: 17 steps
lem-CSdu-box-2-at122441 : Ws → ⟪ (CS04⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx0-2431 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp0431 c4) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 2 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸
       at 4 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp0086 c4) ▸
       at 3 2 (Toff024 ∷ CS24⁻ ∷ []) (wp0432 c4) ▸
       at 2 2 (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp0431 c4) ▸
       at 3 6 (CS04⁻ ∷ []) (wp0433 c4) ▸
       at 3 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04⁻ ∷ []) (Bx0-2431 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

-- Su-box @122441: 17 steps
lem-Su-box-at122441 : Ws → ⟪ (S0 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0 ∷ Bx0-2431 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) (wp0434 c4) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ S0 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ S0 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 2 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ S0 ∷ []) (sym (wl0562 (lit c4))) ▸
       at 4 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp0086 c4) ▸
       at 3 2 (Toff024 ∷ CS24 ∷ []) (wp0435 c4) ▸
       at 2 2 (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) (wp0434 c4) ▸
       at 3 6 (S0 ∷ []) (wp0436 c4) ▸
       at 3 2 (CCZ013 ∷ S0 ∷ []) (sym (wl0562 (lit c4))) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ S0 ∷ []) (Bx0-2431 ∷ S0 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

-- CSdu-box-2 @0210243143: 17 steps
lem-CSdu-box-2-at0210243143 : Ws → ⟪ (CS24⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24⁻ ∷ Bx2-0413 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp0449 c4) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24⁻ ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 2 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4) ▸
       at 3 2 (Toff204 ∷ CS04⁻ ∷ []) (wp0451 c4) ▸
       at 2 2 (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp0449 c4) ▸
       at 3 6 (CS24⁻ ∷ []) (wp0452 c4) ▸
       at 3 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24⁻ ∷ []) (Bx2-0413 ∷ CS24⁻ ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done

-- Su-box @0210243143: 17 steps
lem-Su-box-at0210243143 : Ws → ⟪ (S2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S2 ∷ []) ⟫ʷ
lem-Su-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S2 ∷ Bx2-0413 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) (wp0453 c4) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ S2 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ S2 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 2 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ S2 ∷ []) (sym (wl0582 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4) ▸
       at 3 2 (Toff204 ∷ CS04 ∷ []) (wp0454 c4) ▸
       at 2 2 (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) (wp0453 c4) ▸
       at 3 6 (S2 ∷ []) (wp0455 c4) ▸
       at 3 2 (CCZ123 ∷ S2 ∷ []) (sym (wl0582 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ S2 ∷ []) (Bx2-0413 ∷ S2 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done

-- CSu-box-2 @243243: 17 steps
lem-CSu-box-2-at243243 : Ws → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-2-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) (wp0480 c4) ▸
       at 3 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 7 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 6 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04 ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 4 2 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (wp0059 c4) ▸
       at 3 2 (Toff014 ∷ CS14 ∷ []) (wp0426 c4) ▸
       at 2 2 (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) (wp0480 c4) ▸
       at 3 6 (CS04 ∷ []) (wp0481 c4) ▸
       at 3 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

-- CSu-box-2 @122441: 17 steps
lem-CSu-box-2-at122441 : Ws → ⟪ (CS04 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-2-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) (wp0487 c4) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 2 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 4 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp0086 c4) ▸
       at 3 2 (Toff024 ∷ CS24 ∷ []) (wp0435 c4) ▸
       at 2 2 (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) (wp0487 c4) ▸
       at 3 6 (CS04 ∷ []) (wp0488 c4) ▸
       at 3 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04 ∷ []) (Bx0-2431 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

-- CXbc-box @0214203143: 17 steps
lem-CXbc-box-at0214203143 : Ws → ⟪ (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX01 ∷ CCZ023 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CCZ123 ∷ CX40 ∷ CS34 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ CX01 ∷ []) (wp0497 c4) ▸
       at 1 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (sym (wl0612 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp0498 c4) ▸
       at 2 2 (Toff204 ∷ CX01 ∷ []) (wp0497 c4) ▸
       at 5 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 9 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX01 ∷ CCZ023 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CCZ123 ∷ CX40 ∷ CS34 ∷ CX01 ∷ []) (Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS03⁻ ∷ []) (sym (wl0495 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ023 ∷ []) (wl0613 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (sym (wl0612 (lit c4))) ▸
       at 4 3 (CX01 ∷ []) (wl0614 (lit c4)) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp0499 c4)) ▸ done

-- CXcb-box @0214203143: 18 steps
lem-CXcb-box-at0214203143 : Ws → ⟪ (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) (Toff204 ∷ CCZ123 ∷ CX10 ∷ Toff214 ∷ CS13 ∷ CX41 ∷ Toff204 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ123 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ CX10 ∷ Toff214 ∷ []) (wp0500 c4) ▸
       at 2 2 (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (sym (wl0615 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS34 ∷ []) (wp0501 c4) ▸
       at 7 2 (Toff204 ∷ CX41 ∷ []) (wp0502 c4) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX10 ∷ Toff214 ∷ CS13 ∷ CX41 ∷ Toff204 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ123 ∷ CX10 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX41 ∷ []) (wp0502 c4) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff214 ∷ []) (sym (wp0503 c4)) ▸
       at 2 2 (Toff204 ∷ CX10 ∷ Toff214 ∷ []) (wp0500 c4) ▸
       at 3 3 (CX10 ∷ []) (wp0504 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-4013 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0505 c4)) ▸ done

-- P-box @0214213043: 8 steps
lem-P-box-at0214213043 : Ws → ⟪ (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-P-box-at0214213043 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ Toff203 ∷ []) (sym (lem-tP-at0214213043 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) (sym (wl0626 (lit c4))) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (sym (lem-tP-at0214213043 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ03 ∷ []) (sym (wl0627 (lit c4))) ▸
       at 2 2 (Toff214 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF214 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0628 (lit c4))) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸ done
