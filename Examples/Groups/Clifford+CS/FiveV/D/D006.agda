{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0004 ; wl0006 ; wl0018 ; wl0157 ; wl0159 ; wl0171 ; wl0172 ; wl0173 ; wl0175 ; wl0179 ; wl0182 ; wl0199 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0233 ; wl0263 ; wl0321 ; wl0327 ; wl0334 ; wl0444 ; wl0482 ; wl0490 ; wl0492 ; wl0495 ; wl0560 ; wl0571 ; wl0572 ; wl0573 ; wl0574 ; wl0575 ; wl0576 ; wl0577 ; wl0578 ; wl0579 ; wl0580 ; wl0581 ; wl0582 ; wl0583 ; wl0584 ; wl0585 ; wl0586 ; wl0587 ; wl0588 ; wl0589 ; wl0590 ; wl0591 ; wl0592 ; wl0593 ; wl0594 ; wl0595 ; wl0596 ; wl0597 ; wl0598 ; wl0599 ; wl0600 ; wl0601 ; wl0602 ; wl0603 ; wl0604 ; wl0605 ; wl0606 ; wl0607 ; wl0608 ; wl0609 ; wl0610 ; wl0611 ; wl0612 ; wl0613 ; wl0614 ; wl0615 ; wl0616 ; wl0617 ; wl0618 ; wl0619 ; wl0620 ; wl0621 ; wl0622 ; wl0623 ; wl0624 ; wl0625 ; wl0626 ; wl0627 ; wl0628 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636 ; wl0637 ; wl0638 ; wl0639 ; wl0640 ; wl0641 ; wl0642 ; wl0643 ; wl0644 ; wl0645 ; wl0646 ; wl0647 ; wl0648 ; wl0649 ; wl0650 ; wl0651 ; wl0652 ; wl0653 ; wl0654 ; wl0655 ; wl0656 ; wl0657 ; wl0658 ; wl0659 ; wl0660 ; wl0661 ; wl0662 ; wl0663 ; wl0664 ; wl0665 ; wl0666 ; wl0667 ; wl0668 ; wl0669 ; wl0670 ; wl0671 ; wl0672 ; wl0673 ; wl0674 ; wl0675 ; wl0676 ; wl0677 ; wl0678 ; wl0679 ; wl0680 ; wl0681 ; wp0007 ; wp0025 ; wp0026 ; wp0028 ; wp0048 ; wp0049 ; wp0050 ; wp0051 ; wp0056 ; wp0057 ; wp0059 ; wp0072 ; wp0077 ; wp0086 ; wp0161 ; wp0216 ; wp0218 ; wp0221 ; wp0256 ; wp0259 ; wp0296 ; wp0299 ; wp0301 ; wp0320 ; wp0392 ; wp0394 ; wp0395 ; wp0426 ; wp0435 ; wp0442 ; wp0444 ; wp0445 ; wp0446 ; wp0447 ; wp0448 ; wp0449 ; wp0450 ; wp0451 ; wp0452 ; wp0453 ; wp0454 ; wp0455 ; wp0456 ; wp0457 ; wp0458 ; wp0459 ; wp0460 ; wp0461 ; wp0462 ; wp0463 ; wp0464 ; wp0465 ; wp0466 ; wp0467 ; wp0468 ; wp0469 ; wp0470 ; wp0471 ; wp0472 ; wp0473 ; wp0474 ; wp0475 ; wp0476 ; wp0477 ; wp0478 ; wp0479 ; wp0480 ; wp0481 ; wp0482 ; wp0483 ; wp0484 ; wp0485 ; wp0486 ; wp0487 ; wp0488 ; wp0489 ; wp0490 ; wp0491 ; wp0492 ; wp0493 ; wp0494 ; wp0495 ; wp0496 ; wp0497 ; wp0498 ; wp0499 ; wp0500 ; wp0501 ; wp0502 ; wp0503 ; wp0504 ; wp0505 ; wp0506 ; wp0507 ; wp0508 ; wp0509 ; wp0510 ; wp0511 ; wp0512 ; wp0513 ; wp0514 ; wp0515 ; wp0516 ; wp0517 ; wp0518 ; wp0519 ; wp0520 ; wp0521 ; wp0522 ; wp0523 ; wp0524 ; wp0525 ; wp0526 ; wp0527 ; wp0528 ; wp0529 ; wp0530 ; wp0531 ; wp0532 ; wp0533 ; wp0534 ; wp0535 ; wp0536 ; wp0537 ; wp0538 ; wp0539 ; wp0540 ; wp0541 ; wp0542 ; wp0543 ; wp0544 ; wp0545 ; wp0546 ; wp0547 ; wp0548 ; wp0549 ; wp0550 ; wp0551 ; wp0552 ; wp0553 ; wp0554)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-tQ-at0210243143 ; lem-box-tQ-at122441 ; lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-cQ-at12233441)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd14-TOFF023 ; lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CSd13-TOFF024 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX24-CCZ013 ; lem-comm-CZ14-CCZ023 ; lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS13-TOFF024 ; lem-comm-CS14-CCZ023 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd14-CCZ023 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CK40-TOFF213 ; lem-comm-CK41-CCZ023 ; lem-comm-CK41-TOFF023 ; lem-comm-CS04-CCZ123 ; lem-comm-CS13-TOFF204 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CX03-CCZ124 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ03-TOFF214 ; lem-comm-TOFF203-CSd14 ; lem-comm-TOFF214-CSd03)
-- F4-S1-CS1: 18 steps
lem-F4-S1-CS1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0444 c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ S1 ∷ CS14⁻ ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ []) (sym (wl0571 (lit c4))) ▸
       at 2 3 (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (sym (wp0445 c4)) ▸
       at 4 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (Toff023 ∷ S1 ∷ []) (wl0572 (lit c4)) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 6 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ []) (wl0573 (lit c4)) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ S1 ∷ CS14⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 2 (X4 ∷ CS14 ∷ X4 ∷ []) (wl0571 (lit c4)) ▸ done


-- F4-S1-CS2: 15 steps
lem-F4-S1-CS2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0442 c4)) ▸
       at 1 4 (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0446 c4)) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0442 c4)) ▸
       at 3 4 (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0446 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0574 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ []) (sym (wl0571 (lit c4))) ▸
       at 1 2 (X4 ∷ CS14 ∷ X4 ∷ []) (wl0571 (lit c4)) ▸ done


-- F4-S2-I: 1 steps
lem-F4-S2-I : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0575 (lit c4))) ▸ done


-- F4-S2-S0: 1 steps
lem-F4-S2-S0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0447 c4)) ▸ done


-- F4-S2-S1: 1 steps
lem-F4-S2-S1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0576 (lit c4))) ▸ done


-- F4-S2-S2: 1 steps
lem-F4-S2-S2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0577 (lit c4))) ▸ done


-- F4-S2-S3: 1 steps
lem-F4-S2-S3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0578 (lit c4))) ▸ done


-- F4-S2-K0: 1 steps
lem-F4-S2-K0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0448 c4)) ▸ done


-- F4-S2-K1: 1 steps
lem-F4-S2-K1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0579 (lit c4))) ▸ done


-- F4-S2-K2: 1 steps
lem-F4-S2-K2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0580 (lit c4))) ▸ done


-- F4-S2-K3: 1 steps
lem-F4-S2-K3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0581 (lit c4))) ▸ done


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


-- XCSX-box-2 @0210243143: 4 steps
lem-XCSX-box-2-at0210243143 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ S2 ∷ []) (lem-Su-box-at0210243143 c4) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done


-- F4-S2-CS0: 13 steps
lem-F4-S2-CS0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-XCSX-box-2-at0210243143 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0456 c4)) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0584 (lit c4))) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0457 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done


-- F4-S2-CS1: 15 steps
lem-F4-S2-CS1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 1 4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0459 c4)) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0458 c4)) ▸
       at 3 4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0459 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0585 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done


-- F4-S2-CS2: 18 steps
lem-F4-S2-CS2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0460 c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ S2 ∷ CS24⁻ ∷ [])
  b1 = at 2 3 (S2 ∷ CS24⁻ ∷ []) (sym (wl0583 (lit c4))) ▸
       at 2 3 (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) (sym (wp0461 c4)) ▸
       at 4 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (Toff013 ∷ S2 ∷ []) (wl0586 (lit c4)) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 6 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ []) (wl0587 (lit c4)) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ S2 ∷ CS24⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (wl0583 (lit c4)) ▸ done


-- F4-S3-I: 1 steps
lem-F4-S3-I : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0588 (lit c4))) ▸ done


-- F4-S3-S0: 1 steps
lem-F4-S3-S0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0462 c4)) ▸ done


-- F4-S3-S1: 1 steps
lem-F4-S3-S1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0589 (lit c4))) ▸ done


-- F4-S3-S2: 1 steps
lem-F4-S3-S2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0590 (lit c4))) ▸ done


-- F4-S3-S3: 1 steps
lem-F4-S3-S3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0591 (lit c4))) ▸ done


-- F4-S3-K0: 1 steps
lem-F4-S3-K0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0463 c4)) ▸ done


-- F4-S3-K1: 1 steps
lem-F4-S3-K1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0592 (lit c4))) ▸ done


-- F4-S3-K2: 1 steps
lem-F4-S3-K2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0593 (lit c4))) ▸ done


-- F4-S3-K3: 1 steps
lem-F4-S3-K3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0594 (lit c4))) ▸ done


-- F4-S3-CS0: 15 steps
lem-F4-S3-CS0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0464 c4)) ▸
       at 1 4 (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0595 (lit c4))) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0464 c4)) ▸
       at 3 4 (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0595 (lit c4))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0465 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ []) (sym (wl0596 (lit c4))) ▸
       at 1 2 (X4 ∷ CS34 ∷ X4 ∷ []) (wl0596 (lit c4)) ▸ done


-- F4-S3-CS1: 15 steps
lem-F4-S3-CS1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0466 c4)) ▸
       at 1 4 (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0467 c4)) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0466 c4)) ▸
       at 3 4 (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0467 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0597 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ []) (sym (wl0596 (lit c4))) ▸
       at 1 2 (X4 ∷ CS34 ∷ X4 ∷ []) (wl0596 (lit c4)) ▸ done


-- F4-S3-CS2: 15 steps
lem-F4-S3-CS2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0464 c4)) ▸
       at 1 4 (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0468 c4)) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0464 c4)) ▸
       at 3 4 (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0468 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0598 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ []) (sym (wl0596 (lit c4))) ▸
       at 1 2 (X4 ∷ CS34 ∷ X4 ∷ []) (wl0596 (lit c4)) ▸ done


-- F4-K0-I: 1 steps
lem-F4-K0-I : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0469 c4)) ▸ done


-- F4-K0-S0: 1 steps
lem-F4-K0-S0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0470 c4)) ▸ done


-- F4-K0-S1: 1 steps
lem-F4-K0-S1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0471 c4)) ▸ done


-- F4-K0-S2: 1 steps
lem-F4-K0-S2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0472 c4)) ▸ done


-- F4-K0-S3: 1 steps
lem-F4-K0-S3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0473 c4)) ▸ done


-- F4-K0-K0: 1 steps
lem-F4-K0-K0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0474 c4)) ▸ done


-- F4-K0-K1: 1 steps
lem-F4-K0-K1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0475 c4)) ▸ done


-- F4-K0-K2: 1 steps
lem-F4-K0-K2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0476 c4)) ▸ done


-- F4-K0-K3: 1 steps
lem-F4-K0-K3 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0477 c4)) ▸ done


-- F4-K0-CS0: 17 steps
lem-F4-K0-CS0 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0478 c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 2 (Toff213 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0478 c4)) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 2 (Toff213 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF213 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0479 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


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


-- Ku-box @243243: 6 steps
lem-Ku-box-at243243 : Ws → ⟪ (K0 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box-at243243 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ K0 ∷ []) (sym (wp0482 c4)) ▸
       at 1 2 (Toff023 ∷ K0 ∷ []) (wl0599 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ K0 ∷ []) (sym (wp0482 c4)) ▸
       at 3 2 (Toff023 ∷ K0 ∷ []) (wl0599 (lit c4)) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- Kdu-box @243243: 6 steps
lem-Kdu-box-at243243 : Ws → ⟪ (K0⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at243243 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ K0⁻ ∷ []) (sym (wp0483 c4)) ▸
       at 1 2 (Toff023 ∷ K0⁻ ∷ []) (wl0600 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ K0⁻ ∷ []) (sym (wp0483 c4)) ▸
       at 3 2 (Toff023 ∷ K0⁻ ∷ []) (wl0600 (lit c4)) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- CKdu-box-2 @243243: 7 steps
lem-CKdu-box-2-at243243 : Ws → ⟪ (CK40⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at243243 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0256 c4) ▸
       at 4 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 3 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 2 (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (sym (wp0256 c4)) ▸ done


-- XCKX-box-2 @243243: 4 steps
lem-XCKX-box-2-at243243 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at243243 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (sym (wp0259 c4)) ▸
       at 1 2 (Bx0-1423 ∷ CK40⁻ ∷ []) (lem-CKdu-box-2-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (wp0259 c4) ▸ done


-- F4-K0-CS1: 11 steps
lem-F4-K0-CS1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at243243 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0484 c4)) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0485 c4)) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0484 c4)) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0486 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


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


-- Ku-box @122441: 6 steps
lem-Ku-box-at122441 : Ws → ⟪ (K0 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box-at122441 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ K0 ∷ []) (sym (wp0489 c4)) ▸
       at 1 2 (Toff013 ∷ K0 ∷ []) (wl0601 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ K0 ∷ []) (sym (wp0489 c4)) ▸
       at 3 2 (Toff013 ∷ K0 ∷ []) (wl0601 (lit c4)) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- Kdu-box @122441: 6 steps
lem-Kdu-box-at122441 : Ws → ⟪ (K0⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at122441 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ K0⁻ ∷ []) (sym (wp0490 c4)) ▸
       at 1 2 (Toff013 ∷ K0⁻ ∷ []) (wl0602 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ K0⁻ ∷ []) (sym (wp0490 c4)) ▸
       at 3 2 (Toff013 ∷ K0⁻ ∷ []) (wl0602 (lit c4)) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- CKdu-box-2 @122441: 7 steps
lem-CKdu-box-2-at122441 : Ws → ⟪ (CK40⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at122441 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0256 c4) ▸
       at 4 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 3 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 2 (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (sym (wp0256 c4)) ▸ done


-- XCKX-box-2 @122441: 4 steps
lem-XCKX-box-2-at122441 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at122441 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (sym (wp0259 c4)) ▸
       at 1 2 (Bx0-2431 ∷ CK40⁻ ∷ []) (lem-CKdu-box-2-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (wp0259 c4) ▸ done


-- F4-K0-CS2: 11 steps
lem-F4-K0-CS2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at122441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0491 c4)) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0492 c4)) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0491 c4)) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0493 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-K1-I: 1 steps
lem-F4-K1-I : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0603 (lit c4))) ▸ done


-- F4-K1-S0: 1 steps
lem-F4-K1-S0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0494 c4)) ▸ done


-- F4-K1-S1: 1 steps
lem-F4-K1-S1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0604 (lit c4))) ▸ done


-- F4-K1-S2: 1 steps
lem-F4-K1-S2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0605 (lit c4))) ▸ done


-- F4-K1-S3: 1 steps
lem-F4-K1-S3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0606 (lit c4))) ▸ done


-- F4-K1-K0: 1 steps
lem-F4-K1-K0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0495 c4)) ▸ done


-- F4-K1-K1: 1 steps
lem-F4-K1-K1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0607 (lit c4))) ▸ done


-- F4-K1-K2: 1 steps
lem-F4-K1-K2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0608 (lit c4))) ▸ done


-- F4-K1-K3: 1 steps
lem-F4-K1-K3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0609 (lit c4))) ▸ done


-- sym-ab @0210243143: 18 steps
lem-sym-ab-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-ab-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (wl0610 (lit c4)) ▸
       at 4 1 (Bx2-43 ∷ []) (refl) ▸
       at 7 1 (Bx2-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ [])
  b1 = at 2 6 (Bx4-213 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl0182 (lit c4)) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (wl0610 (lit c4)) ▸
       at 7 1 (Bx2-43 ∷ []) (refl) ▸
       at 10 1 (Bx2-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (Bx2-4013 ∷ [])
  b2 = at 5 6 (Bx4-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- cQ @0214203143: 7 steps
lem-cQ-at0214203143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0214203143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 4 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS02⁻ ∷ []) (sym (wl0611 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸ done


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


-- SWbc-box @0214203143: 11 steps
lem-SWbc-box-at0214203143 : Ws → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-SWbc-box-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (CX01 ∷ Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 1 3 (Bx2-4013 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0214203143 c4) ▸
       at 4 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 2 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (Bx2-4013 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0508 c4) ▸
       at 0 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done


-- nat-SWbc @0214203143: 23 steps
lem-nat-SWbc-at0214203143 : Ws → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ Sw01 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (wp0510 c4) ▸
       at 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸
       at 4 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ Sw01 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Sw01 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Sw01 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 7 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff214 ∷ Sw01 ∷ []) (wp0510 c4) ▸
       at 9 2 (CCZ124 ∷ Sw01 ∷ []) (sym (wp0509 c4)) ▸
       at 11 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 11 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸
       at 12 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Sw01 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Sw01 ∷ []) (Bx2-4103 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw01 ∷ []) (wp0512 c4) ▸
       at 14 2 (CCZ024 ∷ Sw01 ∷ []) (sym (wp0511 c4)) ▸
       at 15 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx4-203 ∷ []) (refl) ▸
       at 5 6 (Bx4-203 ∷ []) (refl) ▸
       at 0 6 (Bx2-4103 ∷ []) (refl) ▸ done


-- sym-bc @0214203143: 2 steps
lem-sym-bc-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym-bc-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0214203143 c4)) ▸
       at 0 3 (Bx2-4103 ∷ []) (lem-nat-SWbc-at0214203143 c4) ▸ done


-- cQ @0214213043: 7 steps
lem-cQ-at0214213043 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0214213043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸ done


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


-- VPQ @0214213043: 14 steps
lem-VPQ-at0214213043 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (sym (wl0631 (lit c4))) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (sym (wl0632 (lit c4))) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0514 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4)) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸ done


-- QVQ @0214213043: 3 steps
lem-QVQ-at0214213043 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at0214213043 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (sym (wl0635 (lit c4))) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0214213043 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @0214213043: 12 steps
lem-box-cP-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at0214213043 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at0214213043 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4) ▸
       at 2 2 [] (wl0636 (lit c4)) ▸ done


-- cQ @0210233441: 7 steps
lem-cQ-at0210233441 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0210233441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0637 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS23⁻ ∷ []) (sym (wl0638 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0637 (lit c4))) ▸ done


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


-- pairs @0214213043: 4 steps
lem-pairs-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-pairs-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) (sym (lem-P-box-at0214213043 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4) ▸
       at 4 2 [] (wl0635 (lit c4)) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done


-- box-perm-1423 @0210243143: 3 steps
lem-box-perm-1423-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1423-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4) ▸ done


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


-- VPQ @0210233441: 14 steps
lem-VPQ-at0210233441 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done


-- QVQ @0210233441: 3 steps
lem-QVQ-at0210233441 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at0210233441 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0210233441 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @0210233441: 12 steps
lem-box-cP-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at0210233441 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at0210233441 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done


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


-- F4-K1-CS1: 17 steps
lem-F4-K1-CS1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0518 c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0518 c4)) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0643 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- CXbc-box @122441: 17 steps
lem-CXbc-box-at122441 : Ws → ⟪ (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX43 ∷ CCZ014 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CX43 ∷ []) (wp0519 c4) ▸
       at 1 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 3 2 (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0520 c4) ▸
       at 2 2 (Toff024 ∷ CX43 ∷ []) (wp0519 c4) ▸
       at 5 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX43 ∷ CCZ014 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX43 ∷ []) (Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS14⁻ ∷ []) (sym (wp0521 c4)) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 2 (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (sym (wp0392 c4)) ▸
       at 4 3 (CX43 ∷ []) (wp0395 c4) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

  b2 : Chain (Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done


-- CXcb-box @122441: 18 steps
lem-CXcb-box-at122441 : Ws → ⟪ (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) (Toff024 ∷ CCZ013 ∷ CX34 ∷ Toff023 ∷ CS13 ∷ CX23 ∷ Toff024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ013 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (wp0522 c4) ▸
       at 2 2 (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) (sym (wl0647 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS12 ∷ []) (wp0524 c4) ▸
       at 7 2 (Toff024 ∷ CX23 ∷ []) (wp0525 c4) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX34 ∷ Toff023 ∷ CS13 ∷ CX23 ∷ Toff024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ013 ∷ CX34 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX23 ∷ []) (wp0525 c4) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 2 2 (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (wp0522 c4) ▸
       at 3 3 (CX34 ∷ []) (wp0526 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done


-- SWbc-box @122441: 11 steps
lem-SWbc-box-at122441 : Ws → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-SWbc-box-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (CX43 ∷ Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 1 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-CXcb-box-at122441 c4) ▸
       at 4 2 (CX43 ∷ CCZ124 ∷ []) (wl0651 (lit c4)) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 2 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸ done

  b1 : Chain (CX43 ∷ Bx0-2431 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (Bx0-2431 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0653 (lit c4)) ▸
       at 0 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-CXbc-box-at122441 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @122441: 23 steps
lem-nat-SWbc-at122441 : Ws → ⟪ (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-nat-SWbc-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ Sw34 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 4 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ Sw34 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Sw34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 7 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 9 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 12 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Sw34 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Sw34 ∷ []) (Bx0-2341 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 14 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 15 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx2-041 ∷ []) (refl) ▸
       at 5 6 (Bx2-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- sym-bc @122441: 2 steps
lem-sym-bc-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-bc-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-2431 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at122441 c4)) ▸
       at 0 3 (Bx0-2341 ∷ []) (lem-nat-SWbc-at122441 c4) ▸ done


-- box-perm-1324 @122441: 1 steps
lem-box-perm-1324-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-1324-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4) ▸ done


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


-- VPQ @12233441: 14 steps
lem-VPQ-at12233441 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (sym (wl0202 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸ done


-- QVQ @12233441: 3 steps
lem-QVQ-at12233441 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at12233441 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at12233441 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done


-- box-cP @12233441: 12 steps
lem-box-cP-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at12233441 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at12233441 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4) ▸
       at 2 2 [] (wl0203 (lit c4)) ▸ done


-- F4-K1-CS2: 19 steps
lem-F4-K1-CS2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 3 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0531 c4)) ▸
       at 4 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0531 c4)) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0654 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-K2-I: 1 steps
lem-F4-K2-I : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0655 (lit c4))) ▸ done


-- F4-K2-S0: 1 steps
lem-F4-K2-S0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0532 c4)) ▸ done


-- F4-K2-S1: 1 steps
lem-F4-K2-S1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0656 (lit c4))) ▸ done


-- F4-K2-S2: 1 steps
lem-F4-K2-S2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0657 (lit c4))) ▸ done


-- F4-K2-S3: 1 steps
lem-F4-K2-S3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0658 (lit c4))) ▸ done


-- F4-K2-K0: 1 steps
lem-F4-K2-K0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0533 c4)) ▸ done


-- F4-K2-K1: 1 steps
lem-F4-K2-K1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0659 (lit c4))) ▸ done


-- F4-K2-K2: 1 steps
lem-F4-K2-K2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0660 (lit c4))) ▸ done


-- F4-K2-K3: 1 steps
lem-F4-K2-K3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0661 (lit c4))) ▸ done


-- CSu-box-2 @0210243143: 17 steps
lem-CSu-box-2-at0210243143 : Ws → ⟪ (CS24 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-2-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24 ∷ Bx2-0413 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (wp0534 c4) ▸
       at 3 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 7 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ123 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ Toff204 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 2 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4) ▸
       at 3 2 (Toff204 ∷ CS04 ∷ []) (wp0454 c4) ▸
       at 2 2 (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (wp0534 c4) ▸
       at 3 6 (CS24 ∷ []) (wp0535 c4) ▸
       at 3 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CS24 ∷ []) (Bx2-0413 ∷ CS24 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- Ku-box @0210243143: 6 steps
lem-Ku-box-at0210243143 : Ws → ⟪ (K2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K2 ∷ []) ⟫ʷ
lem-Ku-box-at0210243143 c4 = run b0
  where
  b0 : Chain (K2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ K2 ∷ []) (sym (wp0536 c4)) ▸
       at 1 2 (Toff213 ∷ K2 ∷ []) (wl0662 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ K2 ∷ []) (sym (wp0536 c4)) ▸
       at 3 2 (Toff213 ∷ K2 ∷ []) (wl0662 (lit c4)) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- Kdu-box @0210243143: 6 steps
lem-Kdu-box-at0210243143 : Ws → ⟪ (K2⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K2⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at0210243143 c4 = run b0
  where
  b0 : Chain (K2⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ K2⁻ ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ K2⁻ ∷ []) (sym (wp0537 c4)) ▸
       at 1 2 (Toff213 ∷ K2⁻ ∷ []) (wl0663 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ K2⁻ ∷ []) (sym (wp0537 c4)) ▸
       at 3 2 (Toff213 ∷ K2⁻ ∷ []) (wl0663 (lit c4)) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- CKdu-box-2 @0210243143: 7 steps
lem-CKdu-box-2-at0210243143 : Ws → ⟪ (CK42⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (CK42⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42⁻ ∷ [])
  b0 = at 0 1 (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0664 (lit c4)) ▸
       at 4 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 3 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 2 (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 5 (CK42⁻ ∷ []) (sym (wl0664 (lit c4))) ▸ done


-- XCKX-box-2 @0210243143: 4 steps
lem-XCKX-box-2-at0210243143 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 3 (K2 ∷ CK42⁻ ∷ []) (sym (wl0665 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ CK42⁻ ∷ []) (lem-CKdu-box-2-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 1 2 (X4 ∷ CK42 ∷ X4 ∷ []) (wl0665 (lit c4)) ▸ done


-- F4-K2-CS0: 11 steps
lem-F4-K2-CS0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-XCKX-box-2-at0210243143 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0666 (lit c4))) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0538 c4)) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0666 (lit c4))) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0539 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- cQ @14213243: 7 steps
lem-cQ-at14213243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 4 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS01⁻ ∷ []) (sym (wl0667 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸ done


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


-- CXbc-box @14213243: 17 steps
lem-CXbc-box-at14213243 : Ws → ⟪ (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX12 ∷ CCZ013 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ CX12 ∷ []) (wp0541 c4) ▸
       at 1 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 3 2 (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0542 c4) ▸
       at 2 2 (Toff014 ∷ CX12 ∷ []) (wp0541 c4) ▸
       at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX12 ∷ CCZ013 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX12 ∷ []) (Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS13⁻ ∷ []) (sym (wl0669 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl0672 (lit c4)) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done

  b2 : Chain (Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0673 (lit c4))) ▸ done


-- CXcb-box @14213243: 18 steps
lem-CXcb-box-at14213243 : Ws → ⟪ (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) (Toff014 ∷ CCZ023 ∷ CX21 ∷ Toff024 ∷ CS23 ∷ CX42 ∷ Toff014 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ CCZ023 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (wp0544 c4) ▸
       at 2 2 (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (sym (wp0545 c4)) ▸
       at 1 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 7 2 (Toff014 ∷ CX42 ∷ []) (wp0547 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX21 ∷ Toff024 ∷ CS23 ∷ CX42 ∷ Toff014 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ CCZ023 ∷ CX21 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX42 ∷ []) (wp0547 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff024 ∷ []) (sym (wp0548 c4)) ▸
       at 2 2 (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (wp0544 c4) ▸
       at 3 3 (CX21 ∷ []) (wp0549 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-4123 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0676 (lit c4))) ▸ done


-- SWbc-box @14213243: 11 steps
lem-SWbc-box-at14213243 : Ws → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-SWbc-box-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (CX12 ∷ Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 1 3 (Bx0-4123 ∷ CCZ234 ∷ []) (lem-CXcb-box-at14213243 c4) ▸
       at 4 2 (CX12 ∷ CCZ134 ∷ []) (wl0679 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (Bx0-4123 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl0681 (lit c4)) ▸
       at 0 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @14213243: 23 steps
lem-nat-SWbc-at14213243 : Ws → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-nat-SWbc-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (wp0552 c4) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸
       at 4 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Sw12 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 7 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff024 ∷ Sw12 ∷ []) (wp0552 c4) ▸
       at 9 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 11 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸
       at 12 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Sw12 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Sw12 ∷ []) (Bx0-4213 ∷ [])
  b2 = at 13 2 (Toff401 ∷ Sw12 ∷ []) (wp0554 c4) ▸
       at 14 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 15 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx4-013 ∷ []) (refl) ▸
       at 5 6 (Bx4-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done

