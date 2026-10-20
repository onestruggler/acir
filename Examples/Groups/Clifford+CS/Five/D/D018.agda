{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D018 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0162 ; wl0165 ; wl0166 ; wl0167 ; wl0168 ; wl0169 ; wl0170 ; wl0181 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0204 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0210 ; wl0229 ; wl0230 ; wl0232 ; wl0233 ; wl0234 ; wl0256 ; wl0268 ; wp0003 ; wp0006 ; wp0007 ; wp0009 ; wp0010 ; wp0011 ; wp0012 ; wp0019 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0024 ; wp0051 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0080 ; wp0081 ; wp0082 ; wp0108 ; wp0116 ; wp0117 ; wp0129 ; wl0298 ; wl0328 ; wl0334 ; wl0341 ; wp0146 ; wp0171 ; wp0186 ; wp0202 ; wp0205 ; wl0345 ; wl0346 ; wl0348 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0414 ; wl0415 ; wp0219 ; wp0220 ; wp0221 ; wp0230 ; wp0231 ; wp0232 ; wp0233 ; wp0234 ; wp0235 ; wp0236 ; wp0237 ; wp0238 ; wp0239 ; wp0240 ; wp0241 ; wp0242 ; wp0243 ; wp0244 ; wp0245 ; wp0246 ; wp0247 ; wp0248 ; wp0249 ; wp0250 ; wp0251 ; wp0252 ; wp0253 ; wp0254 ; wp0257 ; wp0279 ; wl0470 ; wl0471 ; wl0489 ; wp0318 ; wp0319 ; wp0320 ; wp0321 ; wp0322 ; wp0323 ; wp0324 ; wp0332 ; wp0351 ; wl0496 ; wl0497 ; wl0498 ; wl0499 ; wl0500 ; wl0501 ; wl0502 ; wl0503 ; wl0545 ; wl0546 ; wl0556 ; wl0557 ; wl0558 ; wl0559 ; wl0570 ; wl0571 ; wp0357 ; wp0358 ; wp0359 ; wp0384 ; wp0385 ; wp0386 ; wp0387 ; wp0396 ; wp0397 ; wp0405 ; wp0406 ; wp0407 ; wp0408 ; wp0409 ; wp0419 ; wp0420 ; wp0421 ; wp0442 ; wp0443 ; wl0572 ; wl0573 ; wl0574 ; wl0583 ; wl0585 ; wl0586 ; wl0587 ; wl0595 ; wl0596 ; wl0597 ; wl0598 ; wl0599 ; wl0600 ; wl0601 ; wl0602 ; wl0635 ; wl0643 ; wl0662 ; wl0663 ; wp0444 ; wp0445 ; wp0446 ; wp0458 ; wp0459 ; wp0460 ; wp0461 ; wp0464 ; wp0465 ; wp0466 ; wp0467 ; wp0468 ; wp0478 ; wp0479 ; wp0482 ; wp0483 ; wp0489 ; wp0490 ; wp0518 ; wp0536 ; wp0537 ; wl0686 ; wl0709 ; wl0710 ; wl0711 ; wl0712 ; wl0713 ; wl0714 ; wl0716 ; wl0717 ; wl0718 ; wl0719 ; wl0720 ; wl0723 ; wl0732 ; wl0733 ; wl0734 ; wl0735 ; wp0556 ; wp0599 ; wp0600 ; wp0601 ; wp0602 ; wp0603 ; wp0604 ; wp0605 ; wp0608 ; wp0609 ; wp0610 ; wp0611 ; wp0612 ; wp0613 ; wp0619 ; wp0620 ; wp0621 ; wp0625 ; wp0626 ; wp0627 ; wp0628 ; wp0634 ; wp0637 ; wp0638 ; wl0739 ; wl0740 ; wp0642 ; wp0643)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab ; lem-sym-ab-at032032 ; lem-sym-ab-at04203243 ; lem-sym-ab-at1221 ; lem-sym-ab-at122331 ; lem-sym-ab-at12233441 ; lem-sym-ab-at122441 ; lem-sym-ab-at2332 ; lem-sym-ab-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0410213243 ; lem-box-tQ-at13243142 ; lem-box-tQ-at13243241 ; lem-box-tQ-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ ; lem-box-tQ-at0210233441 ; lem-box-tQ-at0210243143 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0330 ; lem-box-tQ-at043043 ; lem-box-tQ-at12243143 ; lem-box-tQ-at122441 ; lem-box-tQ-at1441 ; lem-box-tQ-at233442 ; lem-box-tQ-at243243 ; lem-box-tQ-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-P-box ; lem-P-box-at0214213043 ; lem-P-box-at0310243142 ; lem-P-box-at0330 ; lem-P-box-at1221 ; lem-P-box-at122331 ; lem-P-box-at132132 ; lem-P-box-at13213442 ; lem-P-box-at1331 ; lem-P-box-at2332 ; lem-P-box-at3443 ; lem-t-cP ; lem-t-cP-at0210243143 ; lem-t-cP-at043043 ; lem-t-cP-at122441 ; lem-t-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-P-box-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-CXu-box-4-at03102132 ; lem-box-cP ; lem-box-cP-at0210243143 ; lem-box-cP-at0214213043 ; lem-box-cP-at0310243142 ; lem-box-cP-at0314203142 ; lem-box-cP-at0330 ; lem-box-cP-at043043 ; lem-box-cP-at1221 ; lem-box-cP-at122331 ; lem-box-cP-at122441 ; lem-box-cP-at132132 ; lem-box-cP-at13213442 ; lem-box-cP-at1331 ; lem-box-cP-at143143 ; lem-box-cP-at2332 ; lem-box-cP-at243243 ; lem-box-cP-at3443 ; lem-pairs-at13243142 ; lem-pairs-at13243241 ; lem-pairs-at14233241 ; lem-sym-bc ; lem-sym-bc-at0210243143 ; lem-sym-bc-at0330 ; lem-sym-bc-at043043 ; lem-sym-bc-at1221 ; lem-sym-bc-at122441 ; lem-sym-bc-at13213442 ; lem-sym-bc-at133441 ; lem-sym-bc-at1441 ; lem-sym-bc-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CS14-TOFF023 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX12-TOFF034 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CK40-TOFF213 ; lem-comm-CK41-TOFF023 ; lem-comm-CK42-TOFF013 ; lem-comm-CS04-TOFF213 ; lem-comm-CX40-TOFF312 ; lem-comm-TOFF213-CK40 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF312-CS04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CK41 ; lem-comm-TOFF023-CSd14)

-- box2: 11 steps
lem-box2 : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 4 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 5 5 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ []) (lem-t-cP c4) ▸
       at 5 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸
       at 5 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 3 2 [] (wp0007 c4) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) []
  b1 = at 2 2 [] (wl0162 (lit c4)) ▸
       at 1 2 [] (wp0007 c4) ▸
       at 0 2 [] (wl0162 (lit c4)) ▸ done

-- Xb-box: 18 steps
lem-Xb-box : Ws → ⟪ (X2 ∷ Bx0-1234 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-Xb-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ Bx0-1234 ∷ X2 ∷ []) (CCZ012 ∷ Toff034 ∷ X2 ∷ CZ01 ∷ CS34 ∷ CX13 ∷ CCZ012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ X2 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CZ01 ∷ CCZ134 ∷ []) (wp0009 c4) ▸
       at 1 2 (Toff034 ∷ X2 ∷ []) (sym (wp0010 c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ X2 ∷ CZ01 ∷ CS34 ∷ CX13 ∷ CCZ012 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ X2 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ X2 ∷ CCZ134 ∷ X2 ∷ [])
  b1 = at 5 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0168 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (sym (wl0165 (lit c4))) ▸
       at 3 3 (X2 ∷ []) (wl0169 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 3 2 (Toff034 ∷ X2 ∷ []) (sym (wp0010 c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ X2 ∷ CCZ134 ∷ X2 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0170 (lit c4))) ▸ done

-- Xb-box @0210243143: 18 steps
lem-Xb-box-at0210243143 : Ws → ⟪ (X4 ∷ Bx2-0413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-0413 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CCZ024 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CCZ024 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0024 c4)) ▸ done

-- box2 @0210243143: 11 steps
lem-box2-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at0210243143 c4) ▸
       at 5 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) []
  b1 = at 2 2 [] (wp0019 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0019 c4) ▸ done

-- Xb-box @243243: 18 steps
lem-Xb-box-at243243 : Ws → ⟪ (X4 ∷ Bx0-1423 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CCZ014 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done

-- box2 @243243: 11 steps
lem-box2-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1423 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 5 5 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) (lem-t-cP-at243243 c4) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) []
  b1 = at 2 2 [] (wp0051 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wp0051 c4) ▸ done

-- Xb-box @122441: 18 steps
lem-Xb-box-at122441 : Ws → ⟪ (X4 ∷ Bx0-2431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX23 ∷ CCZ024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ Toff013 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX23 ∷ CCZ024 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ Toff013 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done

-- box2 @122441: 11 steps
lem-box2-at122441 : Ws → ⟪ (Bx0-2431 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at122441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2431 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 0 (Toff024 ∷ Toff024 ∷ []) (sym (wp0080 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ []) (lem-t-cP-at122441 c4) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 3 2 [] (wl0230 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) []
  b1 = at 2 2 [] (wp0080 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸
       at 0 2 [] (wp0080 c4) ▸ done

-- pairs: 4 steps
lem-pairs : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-pairs c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) (sym (lem-P-box c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done

-- box-perm-1324: 1 steps
lem-box-perm-1324 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-box-perm-1324 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸ done

-- box-perm-2314: 2 steps
lem-box-perm-2314 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-box-perm-2314 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸ done

-- pairs @1221: 4 steps
lem-pairs-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-pairs-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) (sym (lem-P-box-at1221 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-3421 ∷ []) (sym (lem-box-tQ-at13243241 c4)) ▸ done

-- box-perm-3124: 2 steps
lem-box-perm-3124 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3124 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸ done

-- pairs @2332: 4 steps
lem-pairs-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-pairs-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) (sym (lem-P-box-at2332 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at2332 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸ done

-- box-perm-3214: 3 steps
lem-box-perm-3214 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-box-perm-3214 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸ done

-- pairs @122331: 4 steps
lem-pairs-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-pairs-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) (sym (lem-P-box-at122331 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at122331 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

-- pairs @132132: 4 steps
lem-pairs-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-pairs-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) (sym (lem-P-box-at132132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

-- pairs @13213442: 4 steps
lem-pairs-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-pairs-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) (sym (lem-P-box-at13213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done

-- pairs @1331: 4 steps
lem-pairs-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-pairs-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) (sym (lem-P-box-at1331 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at1331 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done

-- Ku-box: 6 steps
lem-Ku-box : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (CCZ012 ∷ K0 ∷ []) (sym (wl0345 (lit c4))) ▸
       at 1 2 (Toff034 ∷ K0 ∷ []) (wp0219 c4) ▸
       at 2 2 (CCZ012 ∷ K0 ∷ []) (sym (wl0345 (lit c4))) ▸
       at 3 2 (Toff034 ∷ K0 ∷ []) (wp0219 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- Kdu-box: 6 steps
lem-Kdu-box : Ws → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (CCZ012 ∷ K0⁻ ∷ []) (sym (wl0346 (lit c4))) ▸
       at 1 2 (Toff034 ∷ K0⁻ ∷ []) (wp0220 c4) ▸
       at 2 2 (CCZ012 ∷ K0⁻ ∷ []) (sym (wl0346 (lit c4))) ▸
       at 3 2 (Toff034 ∷ K0⁻ ∷ []) (wp0220 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CSu-box-3: 17 steps
lem-CSu-box-3 : Ws → ⟪ (CS03 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS03 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 1 2 (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) (wp0230 c4) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS03 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03 ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 2 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (wp0232 c4) ▸
       at 4 2 (Toff034 ∷ CS34 ∷ []) (wp0233 c4) ▸
       at 3 2 (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ []) (wp0230 c4) ▸
       at 4 6 (CS03 ∷ []) (wp0234 c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03 ∷ []) (Bx0-1234 ∷ CS03 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CSdu-box-3: 17 steps
lem-CSdu-box-3 : Ws → ⟪ (CS03⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS03⁻ ∷ []) (sym (wl0328 (lit c4))) ▸
       at 1 2 (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (wp0235 c4) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (sym (wl0328 (lit c4))) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (wp0232 c4) ▸
       at 4 2 (Toff034 ∷ CS34⁻ ∷ []) (wp0236 c4) ▸
       at 3 2 (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (wp0235 c4) ▸
       at 4 6 (CS03⁻ ∷ []) (wp0237 c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS03⁻ ∷ []) (Bx0-1234 ∷ CS03⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CZu-box-3: 9 steps
lem-CZu-box-3 : Ws → ⟪ (CZ03 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ03 ∷ []) ⟫ʷ
lem-CZu-box-3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ03 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CZ03 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 1 2 (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) (wp0238 c4) ▸
       at 3 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 2 2 (CCZ012 ∷ CZ03 ∷ []) (sym (wl0382 (lit c4))) ▸
       at 4 2 (Toff034 ∷ CZ34 ∷ []) (wp0239 c4) ▸
       at 3 2 (Toff034 ∷ CZ03 ∷ CZ34 ∷ []) (wp0238 c4) ▸
       at 4 3 (CZ03 ∷ []) (wp0240 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ03 ∷ []) (Bx0-1234 ∷ CZ03 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CXu-box-3: 15 steps
lem-CXu-box-3 : Ws → ⟪ (CX30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX30 ∷ []) ⟫ʷ
lem-CXu-box-3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ CX30 ∷ Toff034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 5 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS23⁻ ∷ []) (wp0241 c4) ▸
       at 3 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 2 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸ done

  b1 : Chain (CCZ012 ∷ CX30 ∷ Toff034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ012 ∷ Toff034 ∷ []) (Bx0-1234 ∷ CX30 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 1 2 (Toff034 ∷ CX30 ∷ []) (wp0242 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 3 3 (CX30 ∷ []) (wl0384 (lit c4)) ▸
       at 3 2 (Toff034 ∷ CX30 ∷ []) (wp0242 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CSu-box-4: 17 steps
lem-CSu-box-4 : Ws → ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-4 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS04 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 1 2 (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) (wp0243 c4) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS04 ∷ CS34 ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04 ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 2 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (wp0232 c4) ▸
       at 4 2 (Toff034 ∷ CS34 ∷ []) (wp0233 c4) ▸
       at 3 2 (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ []) (wp0243 c4) ▸
       at 4 6 (CS04 ∷ []) (wp0244 c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04 ∷ []) (Bx0-1234 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CSdu-box-4: 17 steps
lem-CSdu-box-4 : Ws → ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-4 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 1 2 (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (wp0245 c4) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 7 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CS34 ∷ CCZ012 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ [])
  b1 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 2 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 5 2 (Toff034 ∷ CZ34 ∷ CCZ034 ∷ []) (wp0232 c4) ▸
       at 4 2 (Toff034 ∷ CS34⁻ ∷ []) (wp0236 c4) ▸
       at 3 2 (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ []) (wp0245 c4) ▸
       at 4 6 (CS04⁻ ∷ []) (wp0246 c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS04⁻ ∷ []) (Bx0-1234 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CZu-box-4: 9 steps
lem-CZu-box-4 : Ws → ⟪ (CZ04 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ04 ∷ []) ⟫ʷ
lem-CZu-box-4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ04 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CZ04 ∷ []) (sym (wp0247 c4)) ▸
       at 1 2 (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) (wp0248 c4) ▸
       at 3 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 2 2 (CCZ012 ∷ CZ04 ∷ []) (sym (wp0247 c4)) ▸
       at 4 2 (Toff034 ∷ CZ34 ∷ []) (wp0239 c4) ▸
       at 3 2 (Toff034 ∷ CZ04 ∷ CZ34 ∷ []) (wp0248 c4) ▸
       at 4 3 (CZ04 ∷ []) (wp0249 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CZ04 ∷ []) (Bx0-1234 ∷ CZ04 ∷ [])
  b1 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- CXu-box-4: 15 steps
lem-CXu-box-4 : Ws → ⟪ (CX40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX40 ∷ []) ⟫ʷ
lem-CXu-box-4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ CX40 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (sym (wp0250 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸
       at 5 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS24⁻ ∷ []) (wp0252 c4) ▸
       at 3 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 2 2 (Toff034 ∷ CS24 ∷ []) (wp0202 c4) ▸ done

  b1 : Chain (CCZ012 ∷ CX40 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ012 ∷ Toff034 ∷ []) (Bx0-1234 ∷ CX40 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 1 2 (Toff034 ∷ CX40 ∷ []) (wp0253 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ124 ∷ []) (sym (wp0205 c4)) ▸
       at 2 2 (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (sym (wp0250 c4)) ▸
       at 3 3 (CX40 ∷ []) (wp0254 c4) ▸
       at 3 2 (Toff034 ∷ CX40 ∷ []) (wp0253 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done

-- box-perm-4123 @12233441: 4 steps
lem-box-perm-4123-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4123-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3241 ∷ []) (lem-sym-ab-at12233441 c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-sym-bc-at133441 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-pairs-at13243241 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done

-- box-perm-1423 @233442: 3 steps
lem-box-perm-1423-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1423-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3142 ∷ []) (lem-sym-ab-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-bc-at13213442 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done

-- pairs @3443: 4 steps
lem-pairs-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-pairs-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) (sym (lem-P-box-at3443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done

-- CSdu-box-3 @043043: 17 steps
lem-CSdu-box-3-at043043 : Ws → ⟪ (CS04⁻ ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 0 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 1 2 (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) (wp0319 c4) ▸
       at 4 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 8 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 7 2 (CCZ124 ∷ CX40 ∷ []) (sym (wp0321 c4)) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX40 ∷ []) (sym (wp0321 c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ [])
  b1 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸
       at 3 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 5 2 (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0322 c4) ▸
       at 4 2 (Toff403 ∷ CS03⁻ ∷ []) (wp0323 c4) ▸
       at 3 2 (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) (wp0319 c4) ▸
       at 4 6 (CS04⁻ ∷ []) (wp0324 c4) ▸ done

  b2 : Chain (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ []) (Bx4-1203 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done

-- box-perm-1324 @043043: 1 steps
lem-box-perm-1324-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-1324-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-bc-at043043 c4) ▸ done

-- box-perm-3124 @043043: 2 steps
lem-box-perm-3124-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-box-perm-3124-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-bc-at043043 c4) ▸
       at 0 1 (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4) ▸ done

-- pairs @0330: 4 steps
lem-pairs-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-pairs-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) (sym (lem-P-box-at0330 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at0330 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done

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

-- pairs @0310243142: 4 steps
lem-pairs-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-pairs-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) (sym (lem-P-box-at0310243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸ done

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

-- box-perm-3124 @0330: 2 steps
lem-box-perm-3124-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-3124-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done

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

-- pairs @0214213043: 4 steps
lem-pairs-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-pairs-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) (sym (lem-P-box-at0214213043 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4) ▸
       at 4 2 [] (wl0635 (lit c4)) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done

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

-- box-perm-1324 @122441: 1 steps
lem-box-perm-1324-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-1324-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4) ▸ done

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

-- pairs @143143: 4 steps
lem-pairs-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-pairs-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) (sym (lem-P-box-at143143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at143143 c4) ▸
       at 4 2 [] (wl0229 (lit c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

-- F4-K2-CS2: 17 steps
lem-F4-K2-CS2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0556 c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0556 c4)) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 2 (Toff013 ∷ CK42 ∷ []) (lem-comm-CK42-TOFF013 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0686 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

-- box-perm-1324 @0210243143: 1 steps
lem-box-perm-1324-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸ done

-- box-perm-1324 @243243: 1 steps
lem-box-perm-1324-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1324-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym-bc-at243243 c4) ▸ done

-- box-perm-1423 @122441: 3 steps
lem-box-perm-1423-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1423-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-bc-at1441 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-pairs-at14233241 c4) ▸ done

-- F4-CS0-I: 19 steps
lem-F4-CS0-I : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ ι1 ∷ S4⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0599 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 4 3 (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (wp0600 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ ι1 ∷ S4⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 4 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 3 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 3 (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (wp0600 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done

-- F4-CS0-S0: 17 steps
lem-F4-CS0-S0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S0 ∷ CS04⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (sym (wp0602 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0421 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (S0 ∷ Toff213 ∷ []) (sym (c₁ (S) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S0 ∷ CS04⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 3 3 (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp0420 c4) ▸
       at 2 2 (S0 ∷ Toff213 ∷ []) (sym (c₁ (S) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp0420 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 0 3 (CS04 ∷ X4 ∷ []) (sym (wp0603 c4)) ▸ done

-- F4-CS0-S1: 15 steps
lem-F4-CS0-S1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0604 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 3 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (sym (wl0712 (lit c4))) ▸
       at 3 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (sym (wl0712 (lit c4))) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS14 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸ done

-- F4-CS0-S3: 15 steps
lem-F4-CS0-S3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0608 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (sym (wl0718 (lit c4))) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done

-- F4-CS0-K0: 19 steps
lem-F4-CS0-K0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0611 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (wp0612 c4) ▸
       at 2 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 1 4 (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (wp0612 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (sym (wp0613 c4)) ▸ done

-- F4-CS1-I: 17 steps
lem-F4-CS1-I : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wp0619 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ ι ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp0620 c4) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp0621 c4) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff023 ∷ []) (wp0620 c4) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ014 ∷ []) (wp0621 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done

-- F4-CS1-S1: 17 steps
lem-F4-CS1-S1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S1 ∷ CS14⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0573 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (S1 ∷ Toff023 ∷ []) (sym (wl0572 (lit c4))) ▸
       at 5 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S1 ∷ CS14⁻ ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ S1 ∷ CS14⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 3 3 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp0445 c4) ▸
       at 2 2 (S1 ∷ Toff023 ∷ []) (sym (wl0572 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4)) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp0445 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S1 ∷ CS14⁻ ∷ Sb0-1-42-3 ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 0 3 (CS14 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸ done

-- F4-CS1-S2: 15 steps
lem-F4-CS1-S2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0732 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (sym (wp0625 c4)) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp0626 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S2 ∷ CS24⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (sym (wp0625 c4)) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ014 ∷ []) (wp0626 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done

-- F4-CS1-S3: 15 steps
lem-F4-CS1-S3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ S3 ∷ CS34⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0733 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (sym (wp0627 c4)) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) (wp0628 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ S3 ∷ CS34⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (sym (wp0627 c4)) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ014 ∷ []) (wp0628 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done

-- F4-CS1-K1: 19 steps
lem-F4-CS1-K1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0734 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 3 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp0634 c4) ▸
       at 2 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 1 4 (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ []) (wp0634 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done

-- F4-CS2-I: 17 steps
lem-F4-CS2-I : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ ι ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (wl0709 (lit c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 6 (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wp0637 c4) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ ι ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 4 3 (ι ∷ S4⁻ ∷ Toff013 ∷ []) (wp0638 c4) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 2 3 (ι ∷ S4⁻ ∷ Toff013 ∷ []) (wp0638 c4) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (wp0601 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 0 3 (S4 ∷ X4 ∷ []) (sym (wl0710 (lit c4))) ▸ done

-- F4-CS2-S1: 15 steps
lem-F4-CS2-S1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (sym (wl0711 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0739 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 3 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (sym (wp0642 c4)) ▸
       at 3 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (sym (wp0642 c4)) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (wp0605 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS14 ∷ X4 ∷ []) (sym (wl0713 (lit c4))) ▸ done

-- F4-CS2-S2: 17 steps
lem-F4-CS2-S2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S2 ∷ CS24⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (sym (wl0714 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0587 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (S2 ∷ Toff013 ∷ []) (sym (wl0586 (lit c4))) ▸
       at 5 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S2 ∷ CS24⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 3 3 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp0461 c4) ▸
       at 2 2 (S2 ∷ Toff013 ∷ []) (sym (wl0586 (lit c4))) ▸
       at 3 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp0461 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S2 ∷ CS24⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 0 3 (CS24 ∷ X4 ∷ []) (sym (wl0716 (lit c4))) ▸ done

-- F4-CS2-S3: 15 steps
lem-F4-CS2-S3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ024 ∷ Toff013 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (sym (wl0717 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0740 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (sym (wp0643 c4)) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff013 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (sym (wp0643 c4)) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (wp0609 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (sym (wl0719 (lit c4))) ▸ done
