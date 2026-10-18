{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0004 ; wl0181 ; wl0207 ; wl0230 ; wl0256 ; wl0263 ; wl0334 ; wl0341 ; wl0348 ; wl0382 ; wl0414 ; wl0415 ; wl0433 ; wl0436 ; wl0441 ; wl0444 ; wl0452 ; wl0460 ; wl0461 ; wl0470 ; wl0471 ; wl0476 ; wl0477 ; wl0479 ; wl0480 ; wl0481 ; wl0483 ; wl0485 ; wl0486 ; wl0487 ; wl0488 ; wl0489 ; wl0493 ; wl0494 ; wl0496 ; wl0497 ; wl0498 ; wl0499 ; wl0500 ; wl0501 ; wl0502 ; wl0503 ; wl0504 ; wl0505 ; wl0506 ; wl0507 ; wl0508 ; wl0509 ; wl0510 ; wl0511 ; wl0512 ; wl0513 ; wl0514 ; wl0515 ; wl0516 ; wl0517 ; wl0518 ; wl0519 ; wl0520 ; wl0521 ; wl0522 ; wl0523 ; wl0524 ; wl0525 ; wl0526 ; wl0527 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0532 ; wl0533 ; wl0534 ; wl0535 ; wl0536 ; wl0537 ; wl0538 ; wl0539 ; wl0540 ; wl0541 ; wl0542 ; wl0543 ; wl0544 ; wl0545 ; wl0546 ; wl0547 ; wl0548 ; wl0549 ; wl0550 ; wl0551 ; wl0552 ; wl0553 ; wl0554 ; wl0555 ; wl0556 ; wl0557 ; wl0558 ; wl0559 ; wl0560 ; wl0561 ; wl0562 ; wl0563 ; wl0564 ; wl0565 ; wl0566 ; wl0567 ; wl0568 ; wl0569 ; wl0570 ; wl0571 ; wp0003 ; wp0007 ; wp0047 ; wp0048 ; wp0053 ; wp0054 ; wp0059 ; wp0061 ; wp0065 ; wp0076 ; wp0077 ; wp0086 ; wp0106 ; wp0107 ; wp0108 ; wp0124 ; wp0129 ; wp0161 ; wp0186 ; wp0221 ; wp0228 ; wp0229 ; wp0257 ; wp0279 ; wp0280 ; wp0294 ; wp0296 ; wp0301 ; wp0302 ; wp0305 ; wp0308 ; wp0311 ; wp0320 ; wp0321 ; wp0322 ; wp0332 ; wp0333 ; wp0335 ; wp0337 ; wp0339 ; wp0341 ; wp0342 ; wp0343 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0355 ; wp0356 ; wp0357 ; wp0358 ; wp0359 ; wp0360 ; wp0361 ; wp0362 ; wp0363 ; wp0364 ; wp0365 ; wp0366 ; wp0367 ; wp0368 ; wp0369 ; wp0370 ; wp0371 ; wp0372 ; wp0373 ; wp0374 ; wp0375 ; wp0376 ; wp0377 ; wp0378 ; wp0379 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0384 ; wp0385 ; wp0386 ; wp0387 ; wp0388 ; wp0389 ; wp0390 ; wp0391 ; wp0392 ; wp0393 ; wp0394 ; wp0395 ; wp0396 ; wp0397 ; wp0398 ; wp0399 ; wp0400 ; wp0401 ; wp0402 ; wp0403 ; wp0404 ; wp0405 ; wp0406 ; wp0407 ; wp0408 ; wp0409 ; wp0410 ; wp0411 ; wp0412 ; wp0413 ; wp0414 ; wp0415 ; wp0416 ; wp0417 ; wp0418 ; wp0419 ; wp0420 ; wp0421 ; wp0422 ; wp0423 ; wp0424 ; wp0425 ; wp0426 ; wp0427 ; wp0428 ; wp0429 ; wp0430 ; wp0431 ; wp0432 ; wp0433 ; wp0434 ; wp0435 ; wp0436 ; wp0437 ; wp0438 ; wp0439 ; wp0440 ; wp0441 ; wp0442 ; wp0443)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-tQ-at122441 ; lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-CSdu-box-3-at043043 ; lem-F0-R ; lem-QVQ-at0314203142 ; lem-box-cP-at03102132 ; lem-box-cP-at04203243 ; lem-box-cP-at043043 ; lem-box-perm-1324-at043043 ; lem-box-perm-3124-at043043 ; lem-box-perm-4312-at0330 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0330 ; lem-box-tQ-at0410213243 ; lem-box-tQ-at043043 ; lem-cQ-at0310243142 ; lem-cQ-at04203243 ; lem-tP-at0314203142 ; lem-tP-at043043)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd04-TOFF213 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CS23-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS03-CCZ124 ; lem-comm-CS04-TOFF213 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-CCZ034 ; lem-comm-CS14-CCZ023 ; lem-comm-CS23-TOFF401 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd14-CCZ023 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-CCZ013 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX40-TOFF312 ; lem-comm-CZ03-TOFF412 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ12-TOFF403 ; lem-comm-SWAP02-BOX⟨3·14⟩ ; lem-comm-SWAP02-BOX⟨4·13⟩ ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF312-CS04)
-- box-cP @0314203142: 12 steps
lem-box-cP-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0314203142 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done


-- box-box-4 @0410213243: 103 steps
lem-box-box-4-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-box-box-4-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx4-0123 ∷ Bx3-4012 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ [])
  b0 = at 0 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 3 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 4 2 (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0496 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 8 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff401 ∷ CCZ013 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 6 3 (Toff312 ∷ CCZ234 ∷ []) (wl0497 (lit c4)) ▸
       at 3 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (sym (wp0332 c4)) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff401 ∷ CCZ013 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ K4 ∷ Toff312 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ [])
  b2 = at 4 2 (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl0498 (lit c4)) ▸
       at 3 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (sym (wp0358 c4)) ▸
       at 9 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸ done

  b3 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ K4 ∷ Toff312 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ [])
  b3 = at 3 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 4 7 (Toff401 ∷ []) (wp0358 c4) ▸
       at 6 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 8 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 7 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b4 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff312 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ [])
  b4 = at 5 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (sym (wp0332 c4)) ▸
       at 6 3 (CCZ012 ∷ []) (sym (wl0502 (lit c4))) ▸
       at 6 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 5 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (sym (wp0358 c4)) ▸
       at 11 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 10 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸ done

  b5 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ Toff312 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b5 = at 9 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 5 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 6 7 (Toff401 ∷ []) (wp0358 c4) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸ done

  b6 : Chain (Toff401 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b6 = at 1 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 2 2 (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0496 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b7 : Chain (Toff401 ∷ CCZ034 ∷ Toff312 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ234 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b7 = at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 4 3 (Toff312 ∷ CCZ234 ∷ []) (wl0497 (lit c4)) ▸
       at 1 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (sym (wp0332 c4)) ▸
       at 2 2 (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl0498 (lit c4)) ▸
       at 1 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (sym (wp0358 c4)) ▸ done

  b8 : Chain (CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ Toff312 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b8 = at 7 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 6 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 1 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 2 7 (Toff401 ∷ []) (wp0358 c4) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ012 ∷ CCZ013 ∷ CCZ034 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ034 ∷ CCZ012 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b9 = at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸ done

  b10 : Chain (CCZ034 ∷ Toff312 ∷ Toff401 ∷ CCZ034 ∷ CCZ012 ∷ CCZ013 ∷ Toff312 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ Toff312 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b10 = at 2 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (sym (wp0332 c4)) ▸
       at 4 3 (CCZ012 ∷ []) (sym (wl0502 (lit c4))) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 3 1 (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (sym (wp0358 c4)) ▸
       at 9 2 (Toff312 ∷ K4⁻ ∷ []) (sym (c₄ (Toffᵗ ↑) (K • iI))) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸ done

  b11 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K4 ∷ CS01 ∷ CX40 ∷ Toff312 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (Bx3-4012 ∷ Toff401 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ [])
  b11 = at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 3 2 (Toff312 ∷ K4 ∷ []) (sym (c₄ (Toffᵗ ↑) (K))) ▸
       at 4 7 (Toff401 ∷ []) (wp0358 c4) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 6 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b12 : Chain (Bx3-4012 ∷ Toff401 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ Toff401 ∷ CCZ012 ∷ CCZ234 ∷ []) (Bx3-4012 ∷ Bx4-0123 ∷ [])
  b12 = at 4 2 (CCZ234 ∷ CS12⁻ ∷ []) (sym (wl0414 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 3 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (Toff401 ∷ CCZ012 ∷ []) (wp0359 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 1 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸ done


-- sym-ab @0314203142: 18 steps
lem-sym-ab-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-ab-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4012 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (sym (wl0493 (lit c4))) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ [])
  b1 = at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl0494 (lit c4))) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (sym (wl0493 (lit c4))) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (Bx3-0412 ∷ [])
  b2 = at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


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


-- QVQ @0310243142: 3 steps
lem-QVQ-at0310243142 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0310243142 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @0310243142: 12 steps
lem-box-cP-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243142 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done


-- pairs @0310243142: 4 steps
lem-pairs-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-pairs-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) (sym (lem-P-box-at0310243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done


-- box-perm-3421 @0314203142: 2 steps
lem-box-perm-3421-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-3421-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸ done


-- sym-ab @0410213243: 18 steps
lem-sym-ab-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-ab-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (sym (wl0486 (lit c4))) ▸
       at 4 1 (Bx4-13 ∷ []) (refl) ▸
       at 7 1 (Bx4-13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ [])
  b1 = at 2 6 (Bx1-423 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (sym (wl0486 (lit c4))) ▸
       at 7 1 (Bx4-13 ∷ []) (refl) ▸
       at 10 1 (Bx4-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (Bx4-1023 ∷ [])
  b2 = at 5 6 (Bx1-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- box-tQ @04203243: 13 steps
lem-box-tQ-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 0 2 (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) (wp0355 c4) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at04203243 c4) ▸
       at 2 4 (Toff401 ∷ []) (wp0356 c4) ▸ done


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


-- nat-SWbc @04203243: 23 steps
lem-nat-SWbc-at04203243 : Ws → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-nat-SWbc-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ Sw02 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 1 2 (Toff412 ∷ Sw02 ∷ []) (wp0370 c4) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 3 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸
       at 4 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 5 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ Sw02 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ Sw02 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Sw02 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 7 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 8 2 (Toff412 ∷ Sw02 ∷ []) (wp0370 c4) ▸
       at 9 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 11 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸
       at 12 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Sw02 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Sw02 ∷ []) (Bx4-1203 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸
       at 14 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 15 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-403 ∷ []) (refl) ▸
       at 5 6 (Bx1-403 ∷ []) (refl) ▸
       at 0 6 (Bx4-1203 ∷ []) (refl) ▸ done


-- sym-bc @04203243: 2 steps
lem-sym-bc-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-sym-bc-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at04203243 c4)) ▸
       at 0 3 (Bx4-1203 ∷ []) (lem-nat-SWbc-at04203243 c4) ▸ done


-- box-perm-2314 @0410213243: 2 steps
lem-box-perm-2314-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-2314-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-ab-at0410213243 c4) ▸
       at 0 1 (Bx4-1203 ∷ []) (lem-sym-bc-at04203243 c4) ▸ done


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


-- sym-ab @03102132: 18 steps
lem-sym-ab-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-ab-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 4 1 (Bx3-14 ∷ []) (refl) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ [])
  b1 = at 2 6 (Bx1-324 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸
       at 10 1 (Bx3-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (Bx3-1024 ∷ [])
  b2 = at 5 6 (Bx1-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- cQ @032032: 7 steps
lem-cQ-at032032 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at032032 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS03⁻ ∷ []) (sym (wp0363 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸ done


-- box-tQ @032032: 13 steps
lem-box-tQ-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0519 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at032032 c4) ▸
       at 2 4 (Toff301 ∷ []) (wl0520 (lit c4)) ▸ done


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


-- nat-SWbc @032032: 23 steps
lem-nat-SWbc-at032032 : Ws → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-nat-SWbc-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ Sw02 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw02 ∷ []) (wl0529 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 3 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸
       at 4 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 5 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ Sw02 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ Sw02 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Sw02 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 7 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 8 2 (Toff312 ∷ Sw02 ∷ []) (wl0529 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 11 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸
       at 12 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Sw02 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Sw02 ∷ []) (Bx3-1204 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 15 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-304 ∷ []) (refl) ▸
       at 5 6 (Bx1-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- sym-bc @032032: 2 steps
lem-sym-bc-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-bc-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at032032 c4)) ▸
       at 0 3 (Bx3-1204 ∷ []) (lem-nat-SWbc-at032032 c4) ▸ done


-- box-perm-2314 @03102132: 2 steps
lem-box-perm-2314-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-2314-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸ done


-- CSu-box-3 @043043: 17 steps
lem-CSu-box-3-at043043 : Ws → ⟪ (CS04 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-3-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CS04 ∷ CS03 ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 0 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 1 2 (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) (wp0385 c4) ▸
       at 4 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 8 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 7 2 (CCZ124 ∷ CX40 ∷ []) (sym (wp0321 c4)) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX40 ∷ []) (sym (wp0321 c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff403 ∷ CS04 ∷ CS03 ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04 ∷ [])
  b1 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 3 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 5 2 (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0322 c4) ▸
       at 4 2 (Toff403 ∷ CS03 ∷ []) (wp0386 c4) ▸
       at 3 2 (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ []) (wp0385 c4) ▸
       at 4 6 (CS04 ∷ []) (wp0387 c4) ▸ done

  b2 : Chain (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04 ∷ []) (Bx4-1203 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done


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


-- box2 @043043: 11 steps
lem-box2-at043043 : Ws → ⟪ (Bx4-1203 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1203 ∷ Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) (lem-t-cP-at043043 c4) ▸
       at 5 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 5 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 4 2 [] (wl0470 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) []
  b1 = at 2 2 [] (wl0470 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0470 (lit c4)) ▸ done


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


-- SWbc-box @0330: 11 steps
lem-SWbc-box-at0330 : Ws → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-SWbc-box-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (CX20 ∷ Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 3 (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 1 3 (Bx3-1204 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0330 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ []) (wp0389 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 2 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸ done

  b1 : Chain (CX20 ∷ Bx3-1204 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0390 c4) ▸
       at 0 3 (Bx3-1204 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0330 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @0330: 23 steps
lem-nat-SWbc-at0330 : Ws → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-nat-SWbc-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ Sw02 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw02 ∷ []) (wl0539 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸
       at 4 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 5 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ Sw02 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ Sw02 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Sw02 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 7 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 8 2 (Toff301 ∷ Sw02 ∷ []) (wl0539 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸
       at 12 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Sw02 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Sw02 ∷ []) (Bx3-1024 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 15 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-324 ∷ []) (refl) ▸
       at 5 6 (Bx1-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- sym-bc @0330: 2 steps
lem-sym-bc-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym-bc-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at0330 c4)) ▸
       at 0 3 (Bx3-1024 ∷ []) (lem-nat-SWbc-at0330 c4) ▸ done


-- sym-ab @032032: 18 steps
lem-sym-ab-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym-ab-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 4 1 (Bx3-04 ∷ []) (refl) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ [])
  b1 = at 2 6 (Bx0-324 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸
       at 10 1 (Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (Bx3-0124 ∷ [])
  b2 = at 5 6 (Bx0-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- box-perm-3124 @0330: 2 steps
lem-box-perm-3124-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-3124-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


-- CXuA-S: 44 steps
lem-CXuA-S : Ws → ⟪ (CX34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX34 ∷ []) ⟫ʷ
lem-CXuA-S c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX34 ∷ Sb3-0-12-4 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ Bx4-1203 ∷ CS04⁻ ∷ CX34 ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-box-perm-2314-at03102132 c4) ▸
       at 2 0 (CX34 ∷ CX34 ∷ []) (sym (wl0541 (lit c4))) ▸
       at 0 3 (Bx3-1204 ∷ Bx4-1203 ∷ []) (lem-F0-B c4) ▸
       at 2 5 (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) (lem-F0-R c4) ▸
       at 5 2 (Bx4-1203 ∷ CS04⁻ ∷ []) (lem-CSdu-box-3-at043043 c4) ▸ done

  b1 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ Bx4-1203 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04⁻ ∷ CX34 ∷ [])
  b1 = at 5 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp0376 c4)) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 9 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b2 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ Bx4-1203 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b2 = at 6 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 5 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 6 3 (CCZ014 ∷ Toff412 ∷ []) (sym (wp0391 c4)) ▸
       at 7 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 4 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 3 2 (Bx4-1203 ∷ CS04 ∷ []) (lem-CSu-box-3-at043043 c4) ▸ done

  b3 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ Bx4-1203 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b3 = at 3 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp0376 c4)) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b4 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b4 = at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 4 3 (CCZ014 ∷ Toff412 ∷ []) (sym (wp0391 c4)) ▸
       at 5 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 2 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 1 2 [] (lem-box2-at043043 c4) ▸ done

  b5 : Chain (Bx3-1204 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Sb3-0-12-4 ∷ CX34 ∷ [])
  b5 = at 0 1 (Bx3-0124 ∷ []) (lem-box-perm-3124-at0330 c4) ▸
       at 2 1 (Sb3-0-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-12-4 ∷ []) (refl) ▸ done


-- CXu-box-4 @03102132: 15 steps
lem-CXu-box-4-at03102132 : Ws → ⟪ (CX43 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CX43 ∷ []) ⟫ʷ
lem-CXu-box-4-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX43 ∷ Bx3-0124 ∷ []) (CCZ013 ∷ CX43 ∷ Toff324 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 0 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 6 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS14⁻ ∷ []) (wl0542 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS14 ∷ []) (wl0543 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ CX43 ∷ Toff324 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ013 ∷ Toff324 ∷ []) (Bx3-0124 ∷ CX43 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 1 2 (Toff324 ∷ CX43 ∷ []) (wl0544 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 2 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 3 3 (CX43 ∷ []) (wp0395 c4) ▸
       at 3 2 (Toff324 ∷ CX43 ∷ []) (wl0544 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸ done


-- CXAu-S: 12 steps
lem-CXAu-S : Ws → ⟪ (CX43 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX43 ∷ []) ⟫ʷ
lem-CXAu-S c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX43 ∷ Sb3-0-12-4 ∷ []) (Bx3-0124 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CX43 ∷ CS04⁻ ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (Bx3-0124 ∷ CX43 ∷ []) (lem-CXu-box-4-at03102132 c4) ▸
       at 1 2 (Toff412 ∷ CX43 ∷ Toff312 ∷ []) (wl0545 (lit c4)) ▸
       at 3 2 (CS04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CS04 (lit c4)) ▸
       at 2 2 (CS04 ∷ CX43 ∷ []) (sym (wp0396 c4)) ▸
       at 3 3 (Toff412 ∷ CX43 ∷ []) (wl0546 (lit c4)) ▸ done

  b1 : Chain (Bx3-0124 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CX43 ∷ CS04⁻ ∷ []) (Sb3-0-12-4 ∷ CX43 ∷ [])
  b1 = at 4 2 (CS04⁻ ∷ CX43 ∷ []) (sym (wp0397 c4)) ▸
       at 2 1 (Sb3-0-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-12-4 ∷ []) (refl) ▸ done


-- SW-S: 5 steps
lem-SW-S : Ws → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-SW-S c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ Sw34 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 2 (Sb3-0-12-4 ∷ CX34 ∷ []) (lem-CXuA-S c4) ▸
       at 1 2 (Sb3-0-12-4 ∷ CX43 ∷ []) (lem-CXAu-S c4) ▸
       at 0 2 (Sb3-0-12-4 ∷ CX34 ∷ []) (lem-CXuA-S c4) ▸
       at 1 3 (Sw34 ∷ []) (wl0547 (lit c4)) ▸ done


-- nat-S: 31 steps
lem-nat-S : Ws → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-nat-S c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (wp0399 c4) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 5 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b1 = at 8 1 (CZ04 ∷ []) (refl) ▸
       at 2 7 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (sym (wp0400 c4)) ▸
       at 4 1 (Bx4-03 ∷ []) (refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 2 6 (Bx0-423 ∷ []) (refl) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (wp0399 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 6 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Sw34 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Toff312 ∷ CS03 ∷ Sw34 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ [])
  b2 = at 8 1 (CZ04 ∷ []) (refl) ▸
       at 11 1 (CZ04 ∷ []) (refl) ▸
       at 5 7 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (sym (wp0400 c4)) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 10 1 (Bx4-03 ∷ []) (refl) ▸
       at 5 6 (Bx0-423 ∷ []) (refl) ▸
       at 6 2 (Toff312 ∷ Sw34 ∷ []) (wl0548 (lit c4)) ▸
       at 7 2 (CS03 ∷ Sw34 ∷ []) (sym (wp0401 c4)) ▸ done

  b3 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Toff312 ∷ CS03 ∷ Sw34 ∷ Toff412 ∷ CS04⁻ ∷ Sw34 ∷ []) (Sb4-0-12-3 ∷ [])
  b3 = at 8 2 (Toff312 ∷ Sw34 ∷ []) (wl0548 (lit c4)) ▸
       at 9 2 (CS03⁻ ∷ Sw34 ∷ []) (sym (wp0402 c4)) ▸
       at 10 2 [] (wl0004 (lit c4)) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸
       at 2 1 (Sb4-0-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-0-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-0-12-3 ∷ []) (refl) ▸ done


-- F0: 3 steps
lem-F0 : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-F0 c4 = run b0
  where
  b0 : Chain (Sb3-0-12-4 ∷ []) (Sb4-0-12-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 (lit c4))) ▸
       at 1 2 (Sb3-0-12-4 ∷ Sw34 ∷ []) (lem-SW-S c4) ▸
       at 0 3 (Sb4-0-12-3 ∷ []) (lem-nat-S c4) ▸ done


-- F4-I-I: 1 steps
lem-F4-I-I : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-I c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0549 (lit c4))) ▸ done


-- F4-I-S0: 1 steps
lem-F4-I-S0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0403 c4)) ▸ done


-- F4-I-S1: 1 steps
lem-F4-I-S1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0550 (lit c4))) ▸ done


-- F4-I-S2: 1 steps
lem-F4-I-S2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0551 (lit c4))) ▸ done


-- F4-I-S3: 1 steps
lem-F4-I-S3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0552 (lit c4))) ▸ done


-- F4-I-K0: 1 steps
lem-F4-I-K0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0404 c4)) ▸ done


-- F4-I-K1: 1 steps
lem-F4-I-K1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0553 (lit c4))) ▸ done


-- F4-I-K2: 1 steps
lem-F4-I-K2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0554 (lit c4))) ▸ done


-- F4-I-K3: 1 steps
lem-F4-I-K3 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0555 (lit c4))) ▸ done


-- F4-I-CS0: 15 steps
lem-F4-I-CS0 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 1 4 (Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0556 (lit c4))) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 3 4 (Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0556 (lit c4))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0406 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ []) (wl0557 (lit c4)) ▸
       at 1 2 (X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0557 (lit c4))) ▸ done


-- F4-I-CS1: 15 steps
lem-F4-I-CS1 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 1 4 (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0407 c4)) ▸
       at 3 4 (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0408 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0558 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ []) (wl0557 (lit c4)) ▸
       at 1 2 (X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0557 (lit c4))) ▸ done


-- F4-I-CS2: 15 steps
lem-F4-I-CS2 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-F4-I-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 1 4 (Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0409 c4)) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0405 c4)) ▸
       at 3 4 (Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wp0409 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0559 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ []) (wl0557 (lit c4)) ▸
       at 1 2 (X4 ∷ S4 ∷ X4 ∷ []) (sym (wl0557 (lit c4))) ▸ done


-- F4-S0-I: 1 steps
lem-F4-S0-I : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0410 c4)) ▸ done


-- F4-S0-S0: 1 steps
lem-F4-S0-S0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0411 c4)) ▸ done


-- F4-S0-S1: 1 steps
lem-F4-S0-S1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0412 c4)) ▸ done


-- F4-S0-S2: 1 steps
lem-F4-S0-S2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0413 c4)) ▸ done


-- F4-S0-S3: 1 steps
lem-F4-S0-S3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0414 c4)) ▸ done


-- F4-S0-K0: 1 steps
lem-F4-S0-K0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0415 c4)) ▸ done


-- F4-S0-K1: 1 steps
lem-F4-S0-K1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0416 c4)) ▸ done


-- F4-S0-K2: 1 steps
lem-F4-S0-K2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0417 c4)) ▸ done


-- F4-S0-K3: 1 steps
lem-F4-S0-K3 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0418 c4)) ▸ done


-- F4-S0-CS0: 18 steps
lem-F4-S0-CS0 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0419 c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ S0 ∷ CS04⁻ ∷ [])
  b1 = at 2 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 2 3 (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (sym (wp0420 c4)) ▸
       at 4 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (Toff213 ∷ S0 ∷ []) (c₁ (S) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 6 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ []) (wp0421 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ S0 ∷ CS04⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


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


-- XCSX-box-2 @243243: 4 steps
lem-XCSX-box-2-at243243 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at243243 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ S0 ∷ []) (lem-Su-box-at243243 c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


-- F4-S0-CS1: 13 steps
lem-F4-S0-CS1 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at243243 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0429 c4)) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0428 c4)) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0430 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


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


-- XCSX-box-2 @122441: 4 steps
lem-XCSX-box-2-at122441 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at122441 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ S0 ∷ []) (lem-Su-box-at122441 c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


-- F4-S0-CS2: 13 steps
lem-F4-S0-CS2 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at122441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0438 c4)) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0437 c4)) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0439 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


-- F4-S1-I: 1 steps
lem-F4-S1-I : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0563 (lit c4))) ▸ done


-- F4-S1-S0: 1 steps
lem-F4-S1-S0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0440 c4)) ▸ done


-- F4-S1-S1: 1 steps
lem-F4-S1-S1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0564 (lit c4))) ▸ done


-- F4-S1-S2: 1 steps
lem-F4-S1-S2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0565 (lit c4))) ▸ done


-- F4-S1-S3: 1 steps
lem-F4-S1-S3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0566 (lit c4))) ▸ done


-- F4-S1-K0: 1 steps
lem-F4-S1-K0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0441 c4)) ▸ done


-- F4-S1-K1: 1 steps
lem-F4-S1-K1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0567 (lit c4))) ▸ done


-- F4-S1-K2: 1 steps
lem-F4-S1-K2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0568 (lit c4))) ▸ done


-- F4-S1-K3: 1 steps
lem-F4-S1-K3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0569 (lit c4))) ▸ done


-- F4-S1-CS0: 15 steps
lem-F4-S1-CS0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0442 c4)) ▸
       at 1 4 (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0570 (lit c4))) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0442 c4)) ▸
       at 3 4 (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0570 (lit c4))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0443 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ []) (sym (wl0571 (lit c4))) ▸
       at 1 2 (X4 ∷ CS14 ∷ X4 ∷ []) (wl0571 (lit c4)) ▸ done

