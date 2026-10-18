{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0156 ; wl0157 ; wl0158 ; wl0159 ; wl0162 ; wl0166 ; wl0167 ; wl0181 ; wl0184 ; wl0207 ; wl0214 ; wl0246 ; wl0256 ; wl0263 ; wl0269 ; wl0293 ; wl0295 ; wl0296 ; wl0298 ; wl0301 ; wl0303 ; wl0305 ; wl0306 ; wl0321 ; wl0325 ; wl0327 ; wl0338 ; wl0339 ; wl0340 ; wl0341 ; wl0381 ; wl0423 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0432 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0446 ; wl0447 ; wl0448 ; wl0449 ; wl0450 ; wl0451 ; wl0452 ; wl0453 ; wl0454 ; wl0455 ; wl0456 ; wl0457 ; wl0458 ; wl0459 ; wl0460 ; wl0461 ; wl0462 ; wl0463 ; wl0464 ; wl0465 ; wl0466 ; wl0467 ; wl0468 ; wl0469 ; wl0470 ; wl0471 ; wl0472 ; wl0473 ; wl0474 ; wl0475 ; wl0476 ; wl0477 ; wl0478 ; wl0479 ; wl0480 ; wl0481 ; wl0482 ; wl0483 ; wl0484 ; wl0485 ; wl0486 ; wl0487 ; wl0488 ; wl0489 ; wl0490 ; wl0491 ; wl0492 ; wl0493 ; wl0494 ; wl0495 ; wp0004 ; wp0005 ; wp0006 ; wp0007 ; wp0008 ; wp0011 ; wp0034 ; wp0035 ; wp0036 ; wp0053 ; wp0054 ; wp0066 ; wp0077 ; wp0090 ; wp0096 ; wp0097 ; wp0106 ; wp0107 ; wp0108 ; wp0112 ; wp0113 ; wp0114 ; wp0117 ; wp0124 ; wp0129 ; wp0136 ; wp0142 ; wp0149 ; wp0151 ; wp0157 ; wp0186 ; wp0210 ; wp0228 ; wp0229 ; wp0231 ; wp0280 ; wp0284 ; wp0285 ; wp0286 ; wp0287 ; wp0288 ; wp0289 ; wp0290 ; wp0291 ; wp0292 ; wp0293 ; wp0294 ; wp0295 ; wp0296 ; wp0297 ; wp0298 ; wp0299 ; wp0300 ; wp0301 ; wp0302 ; wp0303 ; wp0304 ; wp0305 ; wp0306 ; wp0307 ; wp0308 ; wp0309 ; wp0310 ; wp0311 ; wp0312 ; wp0313 ; wp0314 ; wp0315 ; wp0316 ; wp0317 ; wp0318 ; wp0319 ; wp0320 ; wp0321 ; wp0322 ; wp0323 ; wp0324 ; wp0325 ; wp0326 ; wp0327 ; wp0328 ; wp0329 ; wp0330 ; wp0331 ; wp0332 ; wp0333 ; wp0334 ; wp0335 ; wp0336 ; wp0337 ; wp0338 ; wp0339 ; wp0340 ; wp0341 ; wp0342 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0352 ; wp0353 ; wp0354 ; wp0355 ; wp0356)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-tQ ; lem-box-tQ-at13243142 ; lem-cQ-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-perm-1243 ; lem-box-perm-1342 ; lem-box-tQ-at13213442 ; lem-box-tQ-at14233142 ; lem-box-tQ-at3443 ; lem-cQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CXbc-box-at13213442 ; lem-box-cP-at021021 ; lem-box-tQ-at233442 ; lem-sym-ab-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ04-CCZ123 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-SWAP14-BOX⟨0·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS03-CCZ124 ; lem-comm-CS03-TOFF412 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd12-TOFF403 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX40-CCZ123 ; lem-comm-CZ04-TOFF312 ; lem-comm-SWAP02-BOX⟨4·13⟩ ; lem-comm-TOFF034-CSd12 ; lem-comm-TOFF301-CSd24 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF312-CSd04 ; lem-comm-TOFF401-CSd23 ; lem-comm-TOFF412-CSd03)
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


-- SWbc-box @13213442: 11 steps
lem-SWbc-box-at13213442 : Ws → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-SWbc-box-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (CX14 ∷ Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 1 3 (Bx0-3142 ∷ CCZ234 ∷ []) (lem-CXcb-box-at13213442 c4) ▸
       at 4 2 (CX14 ∷ CCZ123 ∷ []) (wl0424 (lit c4)) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 2 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸ done

  b1 : Chain (CX14 ∷ Bx0-3142 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (Bx0-3142 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0425 (lit c4)) ▸
       at 0 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-CXbc-box-at13213442 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @13213442: 23 steps
lem-nat-SWbc-at13213442 : Ws → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-nat-SWbc-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ Sw14 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 1 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 3 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 4 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 5 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ Sw14 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Sw14 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 7 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 9 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 12 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Sw14 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Sw14 ∷ []) (Bx0-3412 ∷ [])
  b2 = at 13 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 14 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 15 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-012 ∷ []) (refl) ▸
       at 5 6 (Bx3-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- sym-bc @13213442: 2 steps
lem-sym-bc-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-bc-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at13213442 c4)) ▸
       at 0 3 (Bx0-3412 ∷ []) (lem-nat-SWbc-at13213442 c4) ▸ done


-- tP @13243142: 7 steps
lem-tP-at13243142 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done


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


-- QVQ @13243142: 3 steps
lem-QVQ-at13243142 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at13243142 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @13243142: 12 steps
lem-box-cP-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243142 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243142 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done


-- pairs @13243142: 4 steps
lem-pairs-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-pairs-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (sym (lem-P-box-at13243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243142 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- box-perm-1423 @233442: 3 steps
lem-box-perm-1423-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1423-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3142 ∷ []) (lem-sym-ab-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-bc-at13213442 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done


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


-- cQ @03102132: 7 steps
lem-cQ-at03102132 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸ done


-- tP @03102132: 7 steps
lem-tP-at03102132 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03102132 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸
       at 1 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸ done


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


-- QVQ @03102132: 3 steps
lem-QVQ-at03102132 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at03102132 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @03102132: 12 steps
lem-box-cP-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at03102132 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸
       at 2 2 [] (wl0443 (lit c4)) ▸ done


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


-- QVQ @3443: 3 steps
lem-QVQ-at3443 : Ws → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at3443 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at3443 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @3443: 12 steps
lem-box-cP-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at3443 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at3443 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4) ▸
       at 2 2 [] (wl0162 (lit c4)) ▸ done


-- pairs @3443: 4 steps
lem-pairs-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-pairs-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) (sym (lem-P-box-at3443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done


-- sym-ab @14233142: 18 steps
lem-sym-ab-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym-ab-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (wl0269 (lit c4)) ▸
       at 4 1 (Bx0-32 ∷ []) (refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ [])
  b1 = at 2 6 (Bx3-012 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (wl0269 (lit c4)) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸
       at 10 1 (Bx0-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (Bx0-3412 ∷ [])
  b2 = at 5 6 (Bx3-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- box-perm-1243 @3443: 3 steps
lem-box-perm-1243-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1243-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-pairs-at3443 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done


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


-- cQ @0410213243: 7 steps
lem-cQ-at0410213243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 4 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done


-- tP @0410213243: 7 steps
lem-tP-at0410213243 : Ws → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 3 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at0410213243 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸
       at 1 3 (Toff401 ∷ []) (wp0303 c4) ▸ done


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


-- QVQ @0410213243: 3 steps
lem-QVQ-at0410213243 : Ws → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0457 (lit c4))) ▸
       at 1 4 (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0410213243 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @0410213243: 12 steps
lem-box-cP-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 2 4 (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at0410213243 c4) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4) ▸
       at 2 2 [] (wp0306 c4) ▸ done


-- box-box-4: 103 steps
lem-box-box-4 : Ws → ⟪ (Bx0-1234 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-4 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0123 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CCZ014 ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ [])
  b0 = at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 3 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp0307 c4) ▸
       at 6 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 5 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 8 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CCZ014 ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 6 3 (Toff423 ∷ CCZ034 ∷ []) (wp0309 c4) ▸
       at 3 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ K0 ∷ Toff423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ [])
  b2 = at 4 2 (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0459 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ K0 ∷ Toff423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ [])
  b3 = at 3 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b4 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff423 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ [])
  b4 = at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 6 3 (CCZ123 ∷ []) (sym (wl0462 (lit c4))) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 11 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 10 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸ done

  b5 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff423 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b5 = at 9 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 5 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 6 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 2 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸ done

  b6 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b6 = at 1 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp0307 c4) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 3 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 6 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX02 ∷ []) (sym (wp0308 c4)) ▸ done

  b7 : Chain (Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Toff423 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 4 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 4 3 (Toff423 ∷ CCZ034 ∷ []) (wp0309 c4) ▸
       at 1 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 0 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 2 2 (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0459 (lit c4)) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸ done

  b8 : Chain (CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Toff423 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b8 = at 7 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 6 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 3 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 2 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 1 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 2 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸ done

  b9 : Chain (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b9 = at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b10 : Chain (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ Toff423 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b10 = at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 4 3 (CCZ123 ∷ []) (sym (wl0462 (lit c4))) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸ done

  b11 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ Toff423 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Bx4-0123 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b11 = at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 3 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b12 : Chain (Bx4-0123 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Bx4-0123 ∷ Bx0-1234 ∷ [])
  b12 = at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff012 ∷ CCZ123 ∷ []) (wl0464 (lit c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 1 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- cQ @043043: 7 steps
lem-cQ-at043043 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at043043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done


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


-- QVQ @043043: 3 steps
lem-QVQ-at043043 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at043043 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at043043 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @043043: 12 steps
lem-box-cP-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at043043 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0210 c4) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at043043 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done


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


-- F0-R: 11 steps
lem-F0-R : Ws → ⟪ (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) ⟫ʷ
lem-F0-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CS04⁻ ∷ CCZ034 ∷ CX34 ∷ [])
  b0 = at 0 2 (Toff412 ∷ CX34 ∷ []) (wl0472 (lit c4)) ▸
       at 1 2 (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) (sym (wp0325 c4)) ▸
       at 4 2 (Toff412 ∷ CX34 ∷ []) (wl0472 (lit c4)) ▸
       at 5 2 (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) (sym (wp0326 c4)) ▸
       at 2 2 (CCZ034 ∷ CS03 ∷ []) (sym (wp0327 c4)) ▸
       at 3 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4)) ▸
       at 4 3 (CS04⁻ ∷ []) (wp0328 c4) ▸
       at 2 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸ done

  b1 : Chain (Toff412 ∷ CS04 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CS04⁻ ∷ CCZ034 ∷ CX34 ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ CS04⁻ ∷ []) (sym (wp0329 c4)) ▸
       at 3 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 3 2 (CS04⁻ ∷ Bx4-1203 ∷ []) (sym (lem-CSdu-box-3-at043043 c4)) ▸ done


-- cQ @0330: 7 steps
lem-cQ-at0330 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done


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


-- SWbc-box @043043: 11 steps
lem-SWbc-box-at043043 : Ws → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-SWbc-box-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (CX20 ∷ Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 3 (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4) ▸
       at 3 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl0481 (lit c4)) ▸
       at 1 3 (Bx4-1203 ∷ CCZ013 ∷ []) (lem-CXcb-box-at043043 c4) ▸
       at 4 2 (CX20 ∷ CCZ123 ∷ []) (wl0482 (lit c4)) ▸
       at 3 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl0483 (lit c4)) ▸
       at 2 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl0483 (lit c4)) ▸ done

  b1 : Chain (CX20 ∷ Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (Bx4-1203 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0484 (lit c4)) ▸
       at 0 3 (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @043043: 23 steps
lem-nat-SWbc-at043043 : Ws → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-nat-SWbc-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ Sw02 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 1 2 (Toff401 ∷ Sw02 ∷ []) (wp0338 c4) ▸
       at 3 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 3 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸
       at 4 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 5 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ Sw02 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ Sw02 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Sw02 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 7 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 8 2 (Toff401 ∷ Sw02 ∷ []) (wp0338 c4) ▸
       at 9 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 11 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸
       at 12 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Sw02 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Sw02 ∷ []) (Bx4-1023 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸
       at 14 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 15 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-423 ∷ []) (refl) ▸
       at 5 6 (Bx1-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- sym-bc @043043: 2 steps
lem-sym-bc-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-bc-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at043043 c4)) ▸
       at 0 3 (Bx4-1023 ∷ []) (lem-nat-SWbc-at043043 c4) ▸ done


-- box-perm-1324 @043043: 1 steps
lem-box-perm-1324-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-1324-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-bc-at043043 c4) ▸ done


-- cQ @04203243: 7 steps
lem-cQ-at04203243 : Ws → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at04203243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 4 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸ done


-- tP @04203243: 7 steps
lem-tP-at04203243 : Ws → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at04203243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 3 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at04203243 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸
       at 1 3 (Toff401 ∷ []) (wp0303 c4) ▸ done


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


-- QVQ @04203243: 3 steps
lem-QVQ-at04203243 : Ws → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at04203243 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0457 (lit c4))) ▸
       at 1 4 (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at04203243 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @04203243: 12 steps
lem-box-cP-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at04203243 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 2 4 (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at04203243 c4) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸
       at 2 2 [] (wp0306 c4) ▸ done


-- sym-ab @04203243: 18 steps
lem-sym-ab-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-sym-ab-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (sym (wp0305 c4)) ▸
       at 4 1 (Bx4-03 ∷ []) (refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ [])
  b1 = at 2 6 (Bx0-423 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (sym (wp0305 c4)) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 10 1 (Bx4-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (Bx4-0123 ∷ [])
  b2 = at 5 6 (Bx0-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- box-perm-3124 @043043: 2 steps
lem-box-perm-3124-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-box-perm-3124-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-bc-at043043 c4) ▸
       at 0 1 (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4) ▸ done


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


-- QVQ @0330: 3 steps
lem-QVQ-at0330 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at0330 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0330 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @0330: 12 steps
lem-box-cP-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at0330 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at0330 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4) ▸
       at 2 2 [] (wl0489 (lit c4)) ▸ done


-- cQ @0310243142: 7 steps
lem-cQ-at0310243142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 4 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS34⁻ ∷ []) (sym (wl0491 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸ done


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


-- pairs @0330: 4 steps
lem-pairs-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-pairs-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) (sym (lem-P-box-at0330 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at0330 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done


-- sym-ab @0310243142: 18 steps
lem-sym-ab-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym-ab-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0412 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (wl0494 (lit c4)) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ [])
  b1 = at 2 6 (Bx4-312 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl0493 (lit c4)) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ []) (wl0494 (lit c4)) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (Bx3-4012 ∷ [])
  b2 = at 5 6 (Bx4-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done


-- box-perm-4312 @0330: 2 steps
lem-box-perm-4312-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-4312-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done


-- box-tQ @0410213243: 13 steps
lem-box-tQ-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 0 2 (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) (wp0355 c4) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at0410213243 c4) ▸
       at 2 4 (Toff401 ∷ []) (wp0356 c4) ▸ done


-- cQ @0314203142: 7 steps
lem-cQ-at0314203142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0314203142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 4 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS03⁻ ∷ []) (sym (wl0495 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸ done


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


-- QVQ @0314203142: 3 steps
lem-QVQ-at0314203142 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203142 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0314203142 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

