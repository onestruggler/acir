{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0156 ; wl0157 ; wl0158 ; wl0159 ; wl0162 ; wl0164 ; wl0166 ; wl0175 ; wl0179 ; wl0181 ; wl0199 ; wl0201 ; wl0202 ; wl0203 ; wl0205 ; wl0207 ; wl0222 ; wl0238 ; wl0251 ; wl0255 ; wl0256 ; wl0268 ; wl0274 ; wl0288 ; wl0289 ; wl0290 ; wl0291 ; wl0297 ; wl0298 ; wl0299 ; wl0305 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0312 ; wl0313 ; wl0314 ; wl0315 ; wl0317 ; wl0319 ; wl0321 ; wl0322 ; wl0328 ; wl0338 ; wl0339 ; wl0340 ; wl0341 ; wl0343 ; wl0344 ; wl0345 ; wl0346 ; wl0347 ; wl0348 ; wl0349 ; wl0350 ; wl0351 ; wl0352 ; wl0353 ; wl0354 ; wl0355 ; wl0356 ; wl0357 ; wl0358 ; wl0359 ; wl0360 ; wl0361 ; wl0362 ; wl0363 ; wl0364 ; wl0365 ; wl0366 ; wl0367 ; wl0368 ; wl0369 ; wl0370 ; wl0371 ; wl0372 ; wl0373 ; wl0374 ; wl0375 ; wl0376 ; wl0377 ; wl0378 ; wl0379 ; wl0380 ; wl0381 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0386 ; wl0387 ; wl0388 ; wl0389 ; wl0390 ; wl0391 ; wl0392 ; wl0393 ; wl0394 ; wl0395 ; wl0396 ; wl0397 ; wl0398 ; wl0399 ; wl0400 ; wl0401 ; wl0402 ; wl0403 ; wl0404 ; wl0405 ; wl0406 ; wl0407 ; wl0408 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0420 ; wl0421 ; wl0422 ; wp0001 ; wp0002 ; wp0003 ; wp0004 ; wp0005 ; wp0006 ; wp0008 ; wp0021 ; wp0032 ; wp0039 ; wp0046 ; wp0047 ; wp0048 ; wp0050 ; wp0051 ; wp0053 ; wp0056 ; wp0057 ; wp0062 ; wp0063 ; wp0064 ; wp0067 ; wp0081 ; wp0087 ; wp0092 ; wp0102 ; wp0103 ; wp0111 ; wp0116 ; wp0117 ; wp0120 ; wp0128 ; wp0129 ; wp0141 ; wp0142 ; wp0146 ; wp0154 ; wp0155 ; wp0156 ; wp0157 ; wp0161 ; wp0167 ; wp0171 ; wp0173 ; wp0175 ; wp0177 ; wp0202 ; wp0205 ; wp0211 ; wp0212 ; wp0215 ; wp0216 ; wp0217 ; wp0218 ; wp0219 ; wp0220 ; wp0221 ; wp0222 ; wp0223 ; wp0224 ; wp0225 ; wp0226 ; wp0227 ; wp0228 ; wp0229 ; wp0230 ; wp0231 ; wp0232 ; wp0233 ; wp0234 ; wp0235 ; wp0236 ; wp0237 ; wp0238 ; wp0239 ; wp0240 ; wp0241 ; wp0242 ; wp0243 ; wp0244 ; wp0245 ; wp0246 ; wp0247 ; wp0248 ; wp0249 ; wp0250 ; wp0251 ; wp0252 ; wp0253 ; wp0254 ; wp0255 ; wp0256 ; wp0257 ; wp0258 ; wp0259 ; wp0260 ; wp0261 ; wp0262 ; wp0263 ; wp0264 ; wp0265 ; wp0266 ; wp0267 ; wp0268 ; wp0269 ; wp0270 ; wp0271 ; wp0272 ; wp0273 ; wp0274 ; wp0275 ; wp0276 ; wp0277 ; wp0278 ; wp0279 ; wp0280 ; wp0281 ; wp0282 ; wp0283)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP ; lem-box-tQ ; lem-box-tQ-at1221 ; lem-sym-ab)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-P-box-at1331 ; lem-box-tQ-at13213442 ; lem-box-tQ-at13243241 ; lem-cQ-at13243241 ; lem-pairs-at1221 ; lem-pairs-at122331 ; lem-sym-ab-at122331 ; lem-sym-bc-at1221 ; lem-sym-bc-at13243241 ; lem-tP-at1331)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd14-TOFF023 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CSd23-TOFF014 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ23-CCZ014 ; lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CS14-TOFF023 ; lem-comm-CSd02-TOFF134 ; lem-comm-CSd12-CCZ034 ; lem-comm-CX02-CCZ134 ; lem-comm-CX02-TOFF134 ; lem-comm-CX12-TOFF034 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-SWAP24-BOX⟨0·31⟩ ; lem-comm-TOFF034-CSd12)
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


-- QVQ @1331: 3 steps
lem-QVQ-at1331 : Ws → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at1331 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (sym (wp0051 c4)) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at1331 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done


-- box-cP @1331: 12 steps
lem-box-cP-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at1331 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at1331 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4) ▸
       at 2 2 [] (wl0203 (lit c4)) ▸ done


-- cQ @2442: 7 steps
lem-cQ-at2442 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at2442 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 4 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸ done


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


-- pairs @1331: 4 steps
lem-pairs-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-pairs-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) (sym (lem-P-box-at1331 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at1331 c4) ▸
       at 4 2 [] (wp0051 c4) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done


-- box-perm-1432: 4 steps
lem-box-perm-1432 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1432 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-pairs-at1331 c4) ▸ done


-- sym-ab @243243: 18 steps
lem-sym-ab-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-ab-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp0216 c4) ▸
       at 4 1 (Bx0-43 ∷ []) (refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ [])
  b1 = at 2 6 (Bx4-023 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (wl0205 (lit c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp0216 c4) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸
       at 10 1 (Bx0-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (Bx0-4123 ∷ [])
  b2 = at 5 6 (Bx4-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- box-perm-4123: 4 steps
lem-box-perm-4123 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-4123 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸ done


-- sym-ab @133441: 18 steps
lem-sym-ab-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-ab-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3241 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0217 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp0218 c4) ▸
       at 4 1 (Bx0-21 ∷ []) (refl) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ [])
  b1 = at 2 6 (Bx2-041 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp0217 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (wp0218 c4) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸
       at 10 1 (Bx0-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (Bx0-2341 ∷ [])
  b2 = at 5 6 (Bx2-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- box-perm-2341: 4 steps
lem-box-perm-2341 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-2341 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym-ab-at133441 c4) ▸ done


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


-- CKu-box-1: 7 steps
lem-CKu-box-1 : Ws → ⟪ (CK10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10 ∷ []) ⟫ʷ
lem-CKu-box-1 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10 ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) (wl0362 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 1 5 (CK10 ∷ []) (sym (wl0362 (lit c4))) ▸ done


-- CKdu-box-1: 7 steps
lem-CKdu-box-1 : Ws → ⟪ (CK10⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CKdu-box-1 c4 = run b0
  where
  b0 : Chain (CK10⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10⁻ ∷ [])
  b0 = at 0 1 (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl0363 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 1 5 (CK10⁻ ∷ []) (sym (wl0363 (lit c4))) ▸ done


-- XCSX-box-1: 4 steps
lem-XCSX-box-1 : Ws → ⟪ (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-XCSX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 3 (S0 ∷ CS01⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X1 ∷ CS01 ∷ X1 ∷ []) (wl0364 (lit c4)) ▸ done


-- XCSdX-box-1: 4 steps
lem-XCSdX-box-1 : Ws → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCSdX-box-1 c4 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS01 ∷ []) (sym (wl0365 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (wl0365 (lit c4)) ▸ done


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


-- CKu-box-2: 7 steps
lem-CKu-box-2 : Ws → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-CKu-box-2 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  b0 = at 0 1 (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) (wl0375 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 1 5 (CK20 ∷ []) (sym (wl0375 (lit c4))) ▸ done


-- CKdu-box-2: 7 steps
lem-CKdu-box-2 : Ws → ⟪ (CK20⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2 c4 = run b0
  where
  b0 : Chain (CK20⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20⁻ ∷ [])
  b0 = at 0 1 (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) (wl0376 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 1 5 (CK20⁻ ∷ []) (sym (wl0376 (lit c4))) ▸ done


-- XCSX-box-2: 4 steps
lem-XCSX-box-2 : Ws → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-XCSX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 3 (S0 ∷ CS02⁻ ∷ []) (sym (wl0377 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X2 ∷ CS02 ∷ X2 ∷ []) (wl0377 (lit c4)) ▸ done


-- XCSdX-box-2: 4 steps
lem-XCSdX-box-2 : Ws → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCSdX-box-2 c4 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS02 ∷ []) (sym (wl0378 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wl0378 (lit c4)) ▸ done


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


-- CKu-box-3: 7 steps
lem-CKu-box-3 : Ws → ⟪ (CK30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30 ∷ []) ⟫ʷ
lem-CKu-box-3 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) (wl0385 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 1 5 (CK30 ∷ []) (sym (wl0385 (lit c4))) ▸ done


-- CKdu-box-3: 7 steps
lem-CKdu-box-3 : Ws → ⟪ (CK30⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CKdu-box-3 c4 = run b0
  where
  b0 : Chain (CK30⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30⁻ ∷ [])
  b0 = at 0 1 (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) (wl0386 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 1 5 (CK30⁻ ∷ []) (sym (wl0386 (lit c4))) ▸ done


-- XCSX-box-3: 4 steps
lem-XCSX-box-3 : Ws → ⟪ (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-XCSX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 0 3 (S0 ∷ CS03⁻ ∷ []) (sym (wl0387 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X3 ∷ CS03 ∷ X3 ∷ []) (wl0387 (lit c4)) ▸ done


-- XCSdX-box-3: 4 steps
lem-XCSdX-box-3 : Ws → ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCSdX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS03 ∷ []) (sym (wl0388 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X3 ∷ CS03⁻ ∷ X3 ∷ []) (wl0388 (lit c4)) ▸ done


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


-- CKu-box-4: 7 steps
lem-CKu-box-4 : Ws → ⟪ (CK40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-4 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp0255 c4) ▸
       at 4 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 1 5 (CK40 ∷ []) (sym (wp0255 c4)) ▸ done


-- CKdu-box-4: 7 steps
lem-CKdu-box-4 : Ws → ⟪ (CK40⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-4 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0256 c4) ▸
       at 4 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (sym (wp0256 c4)) ▸ done


-- XCSX-box-4: 4 steps
lem-XCSX-box-4 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done


-- XCSdX-box-4: 4 steps
lem-XCSdX-box-4 : Ws → ⟪ (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCSdX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS04 ∷ []) (sym (wp0258 c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X4 ∷ CS04⁻ ∷ X4 ∷ []) (wp0258 c4) ▸ done


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


-- cQ @12233441: 7 steps
lem-cQ-at12233441 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at12233441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸ done


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


-- cQ @0110: 7 steps
lem-cQ-at0110 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS12⁻ ∷ []) (sym (wl0392 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸ done


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


-- QVQ @0110: 3 steps
lem-QVQ-at0110 : Ws → ⟪ (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-QVQ-at0110 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ [])
  b0 = at 0 0 (Toff134 ∷ Toff134 ∷ []) (sym (wl0402 (lit c4))) ▸
       at 1 4 (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at0110 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


-- box-cP @0110: 12 steps
lem-box-cP-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-box-cP-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx1-0234 ∷ []) (CCZ012 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 2 4 (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-QVQ-at0110 c4) ▸
       at 1 2 (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4) ▸
       at 2 2 [] (wl0403 (lit c4)) ▸ done


-- sym-ab @12233441: 18 steps
lem-sym-ab-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-ab-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (wp0217 c4) ▸
       at 4 1 (Bx0-31 ∷ []) (refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ [])
  b1 = at 2 6 (Bx3-041 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (wp0217 c4) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸
       at 10 1 (Bx0-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (Bx0-3241 ∷ [])
  b2 = at 5 6 (Bx3-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- cQ @133441: 7 steps
lem-cQ-at133441 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at133441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸ done


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


-- SWbc-box @133441: 11 steps
lem-SWbc-box-at133441 : Ws → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-SWbc-box-at133441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (CX24 ∷ Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 1 3 (Bx0-3241 ∷ CCZ134 ∷ []) (lem-CXcb-box-at133441 c4) ▸
       at 4 2 (CX24 ∷ CCZ123 ∷ []) (wl0406 (lit c4)) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 2 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸ done

  b1 : Chain (CX24 ∷ Bx0-3241 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (Bx0-3241 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0407 (lit c4)) ▸
       at 0 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-CXbc-box-at133441 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @133441: 23 steps
lem-nat-SWbc-at133441 : Ws → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-nat-SWbc-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ Sw24 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 1 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 3 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 4 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 5 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ Sw24 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Sw24 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 7 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 9 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 12 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Sw24 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Sw24 ∷ []) (Bx0-3421 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 14 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 15 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx3-021 ∷ []) (refl) ▸
       at 5 6 (Bx3-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- sym-bc @133441: 2 steps
lem-sym-bc-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-bc-at133441 c4 = run b0
  where
  b0 : Chain (Bx0-3241 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at133441 c4)) ▸
       at 0 3 (Bx0-3421 ∷ []) (lem-nat-SWbc-at133441 c4) ▸ done


-- tP @13243241: 7 steps
lem-tP-at13243241 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243241 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done


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


-- QVQ @13243241: 3 steps
lem-QVQ-at13243241 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243241 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (sym (wl0162 (lit c4))) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at13243241 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @13243241: 12 steps
lem-box-cP-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at13243241 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at13243241 c4) ▸
       at 2 2 [] (wp0006 c4) ▸ done


-- pairs @13243241: 4 steps
lem-pairs-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-pairs-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (sym (lem-P-box-at13243241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243241 c4) ▸
       at 4 2 [] (wl0162 (lit c4)) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done


-- sym-ab @1221: 18 steps
lem-sym-ab-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym-ab-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 4 1 (Bx0-14 ∷ []) (refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ [])
  b1 = at 2 6 (Bx1-034 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸
       at 10 1 (Bx0-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 5 6 (Bx1-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done


-- box-perm-4123 @12233441: 4 steps
lem-box-perm-4123-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4123-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3241 ∷ []) (lem-sym-ab-at12233441 c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-sym-bc-at133441 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-pairs-at13243241 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done


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


-- cQ @233442: 7 steps
lem-cQ-at233442 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at233442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done


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


-- cQ @021021: 7 steps
lem-cQ-at021021 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS12⁻ ∷ []) (sym (wl0414 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸ done


-- tP @021021: 7 steps
lem-tP-at021021 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at021021 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸
       at 1 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸ done


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


-- QVQ @021021: 3 steps
lem-QVQ-at021021 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at021021 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at021021 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @021021: 12 steps
lem-box-cP-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at021021 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at021021 c4) ▸
       at 2 2 [] (wl0421 (lit c4)) ▸ done


-- sym-ab @233442: 18 steps
lem-sym-ab-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym-ab-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1342 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 4 1 (Bx0-32 ∷ []) (refl) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ [])
  b1 = at 2 6 (Bx3-042 ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (wp0211 c4) ▸
       at 7 1 (Bx0-32 ∷ []) (refl) ▸
       at 10 1 (Bx0-32 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (Bx0-3142 ∷ [])
  b2 = at 5 6 (Bx3-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


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

