{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD123 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D123 (Sᴰ : SD123) where

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
  lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R : Ws → St 1680
  lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : Ws → St 1838
  lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : Ws → St 1839
  lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R : Ws → St 1681
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R : Ws → St 1682
  lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R : Ws → St 1845
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R : Ws → St 1846
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R = pickᴰ 6 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 10 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1838 (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1456 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 4 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1457 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1839 (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 3 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1458 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1845 (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 6 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 1459 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1846 (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 18 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q20 : Ws → Eqn
  q20 c4 = wlE 47 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (ℓ "乇乼") (ℓ "乼乇") (c₃ (CS ↑) (Swap))
  q22 : Ws → Eqn
  q22 c4 = wlE 46 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1590 (lem-F5-23 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (ℓ "丫並") (ℓ "並丫") (c₂ (Swap) (X ↑ ↑))
  q25 : Ws → Eqn
  q25 c4 = sE 1681 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (ℓ "乊並") (ℓ "並乊") (c₃ (Swap ↑) (X ↑))
  q27 : Ws → Eqn
  q27 c4 = sE 1682 (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (ℓ "乥並") (ℓ "並乥") (c₄ (Swap ↑ ↑) (X))
  q29 : Ws → Eqn
  q29 c4 = sE 1680 (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4)

-- ckt-TST @0440 part21: 95 steps
lem-ckt-TST-at0440-part21 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临丫乊乥丠乼俜並俜乼乥乊丫乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主与俵与上临俵俵丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part21 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临丫乊乥丠乼俜並俜乼乥乊丫乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主与俵与上临俵俵丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw 281 (q1 c4) ∷
   rw 282 (q2 c4) ∷
   rw 283 (q1 c4) ∷
   rw 284 (q3 c4) ∷
   rw 279 (q4 c4) ∷
   rw 280 (q5 c4) ∷
   rw 281 (q4 c4) ∷
   rw 282 (q5 c4) ∷
   rw 283 (q6 c4) ∷
   rw 278 (q7 c4) ∷
   rw 279 (q8 c4) ∷
   rw 280 (q7 c4) ∷
   rw 281 (q8 c4) ∷
   rw 282 (q9 c4) ∷
   rw 277 (q10 c4) ∷
   rw 278 (q11 c4) ∷
   rw 279 (q10 c4) ∷
   rw 280 (q11 c4) ∷
   rw 281 (q12 c4) ∷
   rw⁻ 276 (q13 c4) ∷
   rw⁻ 275 (q14 c4) ∷
   rw⁻ 274 (q15 c4) ∷
   rw⁻ 273 (q16 c4) ∷
   rw⁻ 272 (q16 c4) ∷
   rw⁻ 271 (q15 c4) ∷
   rw⁻ 270 (q14 c4) ∷
   rw⁻ 269 (q13 c4) ∷
   rw⁻ 268 (q17 c4) ∷
   rw⁻ 267 (q17 c4) ∷
   rw⁻ 266 (q13 c4) ∷
   rw⁻ 265 (q16 c4) ∷
   rw⁻ 264 (q16 c4) ∷
   rw⁻ 263 (q16 c4) ∷
   rw⁻ 262 (q14 c4) ∷
   rw⁻ 261 (q13 c4) ∷
   rw⁻ 260 (q17 c4) ∷
   rw⁻ 259 (q17 c4) ∷
   rw⁻ 258 (q13 c4) ∷
   rw⁻ 257 (q16 c4) ∷
   rw⁻ 256 (q18 c4) ∷
   rw⁻ 282 (q12 c4) ∷
   rw⁻ 281 (q19 c4) ∷
   rw⁻ 283 (q9 c4) ∷
   rw 282 (q20 c4) ∷
   rw⁻ 284 (q6 c4) ∷
   re 283 1 (ℓ "乥乇乥") ∷
   rw 285 (q6 c4) ∷
   rw⁻ 285 (q3 c4) ∷
   rw 284 (q21 c4) ∷
   rw⁻ 286 (q6 c4) ∷
   rw⁻ 285 (q6 c4) ∷
   re 286 3 (ℓ "乎") ∷
   rw⁻ 287 (q9 c4) ∷
   rw 286 (q22 c4) ∷
   rw⁻ 288 (q12 c4) ∷
   rw⁻ 287 (q19 c4) ∷
   rw⁻ 288 (q23 c4) ∷
   rw 287 (q24 c4) ∷
   rw 288 (q25 c4) ∷
   rw 289 (q24 c4) ∷
   rw 290 (q25 c4) ∷
   rw 291 (q12 c4) ∷
   rw 286 (q26 c4) ∷
   rw 287 (q27 c4) ∷
   rw 288 (q26 c4) ∷
   rw 289 (q27 c4) ∷
   rw 290 (q9 c4) ∷
   rw 285 (q28 c4) ∷
   rw 286 (q29 c4) ∷
   rw 287 (q28 c4) ∷
   rw 288 (q29 c4) ∷
   rw 289 (q6 c4) ∷
   rw 284 (q2 c4) ∷
   rw 285 (q1 c4) ∷
   rw 286 (q2 c4) ∷
   rw 287 (q1 c4) ∷
   rw 288 (q3 c4) ∷
   rw 283 (q4 c4) ∷
   rw 284 (q5 c4) ∷
   rw 285 (q4 c4) ∷
   rw 286 (q5 c4) ∷
   rw 287 (q6 c4) ∷
   rw 282 (q7 c4) ∷
   rw 283 (q8 c4) ∷
   rw 284 (q7 c4) ∷
   rw 285 (q8 c4) ∷
   rw 286 (q9 c4) ∷
   rw 281 (q10 c4) ∷
   rw 282 (q11 c4) ∷
   rw 283 (q10 c4) ∷
   rw 284 (q11 c4) ∷
   rw 285 (q12 c4) ∷
   rw⁻ 280 (q16 c4) ∷
   rw⁻ 279 (q13 c4) ∷
   rw⁻ 278 (q14 c4) ∷ []) Eq.refl
