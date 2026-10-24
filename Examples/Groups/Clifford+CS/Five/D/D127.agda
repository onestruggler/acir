{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD127 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D127 (Sᴰ : SD127) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R : Ws → St 1840
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R : Ws → St 1841
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R : Ws → St 1842
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R : Ws → St 1843
  lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R : Ws → St 1844
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : Ws → St 1847
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : Ws → St 1848
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R = pickᴰ 6 Sᴰ
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1686
  lem-F4-I-K3-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1863
  lem-F4-CS1-I-at0440 = pickᴰ 13 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS1-K3-at0440 : Ws → St 1872
  lem-F4-CS1-K3-at0440 = pickᴰ 15 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 16 Sᴰ
  lem-F5-12 : Ws → St 1816
  lem-F5-12 = pickᴰ 17 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 18 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 19 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1461 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 18 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 146 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 6 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 3 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (ℓ "丨乥") (ℓ "乥丨") (c₂ (CS) (Swap))
  q16 : Ws → Eqn
  q16 c4 = wlE 4 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (ℓ "丨乼") (ℓ "乼丨") (c₂ (CS) (Swap ↑))
  q18 : Ws → Eqn
  q18 c4 = wlE 24 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1816 (lem-F5-12 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (ℓ "丫並") (ℓ "並丫") (c₂ (Swap) (X ↑ ↑))
  q21 : Ws → Eqn
  q21 c4 = sE 1840 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (ℓ "乊並") (ℓ "並乊") (c₃ (Swap ↑) (X ↑))
  q23 : Ws → Eqn
  q23 c4 = sE 1841 (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (ℓ "乥並") (ℓ "並乥") (c₄ (Swap ↑ ↑) (X))
  q25 : Ws → Eqn
  q25 c4 = sE 1842 (lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 1456 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1843 (lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 1457 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1848 (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 1458 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1844 (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 1459 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1847 (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1863 (lem-F4-CS1-I-at0440 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1872 (lem-F4-CS1-K3-at0440 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1859 (lem-F4-CS1-CS2-at0440 c4)

-- ckt-TST @0440 part25: 89 steps
lem-ckt-TST-at0440-part25 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与中俵临与主与俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主与俭与俵俵主上俭丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part25 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与中俵临与主与俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主与俭与俵俵主上俭丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 279 (q1 c4) ∷
   rw⁻ 278 (q2 c4) ∷
   rw⁻ 277 (q3 c4) ∷
   rw⁻ 309 (q4 c4) ∷
   rw⁻ 308 (q5 c4) ∷
   rw⁻ 307 (q6 c4) ∷
   rw⁻ 306 (q6 c4) ∷
   rw⁻ 305 (q5 c4) ∷
   rw⁻ 304 (q7 c4) ∷
   rw⁻ 303 (q8 c4) ∷
   rw⁻ 302 (q6 c4) ∷
   rw⁻ 301 (q6 c4) ∷
   rw⁻ 300 (q8 c4) ∷
   rw⁻ 299 (q7 c4) ∷
   rw⁻ 298 (q5 c4) ∷
   rw⁻ 297 (q6 c4) ∷
   rw⁻ 296 (q6 c4) ∷
   rw⁻ 295 (q5 c4) ∷
   rw⁻ 294 (q7 c4) ∷
   rw⁻ 293 (q8 c4) ∷
   rw⁻ 292 (q9 c4) ∷
   rw⁻ 291 (q9 c4) ∷
   rw⁻ 290 (q8 c4) ∷
   rw⁻ 289 (q6 c4) ∷
   rw⁻ 288 (q6 c4) ∷
   rw⁻ 287 (q6 c4) ∷
   rw⁻ 286 (q7 c4) ∷
   rw⁻ 285 (q8 c4) ∷
   rw⁻ 284 (q9 c4) ∷
   rw⁻ 283 (q9 c4) ∷
   rw⁻ 282 (q8 c4) ∷
   rw⁻ 281 (q6 c4) ∷
   rw⁻ 280 (q10 c4) ∷
   rw⁻ 314 (q11 c4) ∷
   rw 313 (q12 c4) ∷
   rw⁻ 315 (q13 c4) ∷
   re 314 1 (ℓ "乊丨乊") ∷
   rw 316 (q13 c4) ∷
   rw⁻ 316 (q14 c4) ∷
   rw 315 (q15 c4) ∷
   rw⁻ 317 (q16 c4) ∷
   rw 316 (q17 c4) ∷
   rw⁻ 318 (q14 c4) ∷
   rw 317 (q15 c4) ∷
   rw⁻ 319 (q13 c4) ∷
   rw⁻ 318 (q13 c4) ∷
   re 319 3 (ℓ "丯") ∷
   rw⁻ 320 (q11 c4) ∷
   rw 319 (q18 c4) ∷
   rw⁻ 320 (q19 c4) ∷
   rw 319 (q20 c4) ∷
   rw 320 (q21 c4) ∷
   rw 321 (q20 c4) ∷
   rw 322 (q21 c4) ∷
   rw 323 (q11 c4) ∷
   rw 318 (q22 c4) ∷
   rw 319 (q23 c4) ∷
   rw 320 (q22 c4) ∷
   rw 321 (q23 c4) ∷
   rw 322 (q13 c4) ∷
   rw 317 (q24 c4) ∷
   rw 318 (q25 c4) ∷
   rw 319 (q24 c4) ∷
   rw 320 (q25 c4) ∷
   rw 321 (q14 c4) ∷
   rw 316 (q26 c4) ∷
   rw 317 (q27 c4) ∷
   rw 318 (q26 c4) ∷
   rw 319 (q27 c4) ∷
   rw 320 (q16 c4) ∷
   rw 315 (q28 c4) ∷
   rw 316 (q29 c4) ∷
   rw 317 (q28 c4) ∷
   rw 318 (q29 c4) ∷
   rw 319 (q14 c4) ∷
   rw 314 (q30 c4) ∷
   rw 315 (q31 c4) ∷
   rw 316 (q30 c4) ∷
   rw 317 (q31 c4) ∷
   rw 318 (q13 c4) ∷
   rw 313 (q32 c4) ∷
   rw 314 (q33 c4) ∷
   rw 315 (q32 c4) ∷
   rw 316 (q33 c4) ∷
   rw 317 (q11 c4) ∷
   rw⁻ 312 (q34 c4) ∷
   rw⁻ 311 (q35 c4) ∷
   rw⁻ 310 (q36 c4) ∷
   rw⁻ 309 (q36 c4) ∷ []) Eq.refl
