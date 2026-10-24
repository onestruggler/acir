{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD116 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D116 (Sᴰ : SD116) where

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
  lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : Ws → St 1838
  lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R = pickᴰ 0 Sᴰ
  lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : Ws → St 1839
  lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R : Ws → St 1840
  lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R : Ws → St 1841
  lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R = pickᴰ 3 Sᴰ
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R : Ws → St 1842
  lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R : Ws → St 1843
  lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R : Ws → St 1844
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R : Ws → St 1845
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R = pickᴰ 7 Sᴰ
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R : Ws → St 1846
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : Ws → St 1847
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R = pickᴰ 9 Sᴰ
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : Ws → St 1848
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R = pickᴰ 10 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1852
  lem-F4-CS1-K1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 13 Sᴰ
  lem-F5-12 : Ws → St 1816
  lem-F5-12 = pickᴰ 14 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 15 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1858
  lem-F4-CS1-K2-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 17 Sᴰ

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
  q13 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1715 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 146 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (ℓ "丨乥") (ℓ "乥丨") (c₂ (CS) (Swap))
  q19 : Ws → Eqn
  q19 c4 = eqn (ℓ "丨乼") (ℓ "乼丨") (c₂ (CS) (Swap ↑))
  q20 : Ws → Eqn
  q20 c4 = wlE 24 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1816 (lem-F5-12 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (ℓ "丫並") (ℓ "並丫") (c₂ (Swap) (X ↑ ↑))
  q23 : Ws → Eqn
  q23 c4 = sE 1840 (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (ℓ "乊並") (ℓ "並乊") (c₃ (Swap ↑) (X ↑))
  q25 : Ws → Eqn
  q25 c4 = sE 1841 (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (ℓ "乥並") (ℓ "並乥") (c₄ (Swap ↑ ↑) (X))
  q27 : Ws → Eqn
  q27 c4 = sE 1842 (lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1843 (lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1848 (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1844 (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1847 (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1858 (lem-F4-CS1-K2-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1859 (lem-F4-CS1-CS2-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1852 (lem-F4-CS1-K1-at0440 c4)

-- ckt-TST @0440 part14: 115 steps
lem-ckt-TST-at0440-part14 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与中丫乊乥丠乼俜並俜乼乥乊丫丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与中俵临俭丫乊乥丠俨丠俨乥乊丫丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part14 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与中丫乊乥丠乼俜並俜乼乥乊丫丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与中俵临俭丫乊乥丠俨丠俨乥乊丫丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw 201 (q1 c4) ∷
   rw 202 (q2 c4) ∷
   rw 203 (q1 c4) ∷
   rw 204 (q3 c4) ∷
   rw 199 (q4 c4) ∷
   rw 200 (q5 c4) ∷
   rw 201 (q4 c4) ∷
   rw 202 (q5 c4) ∷
   rw 203 (q6 c4) ∷
   rw 198 (q7 c4) ∷
   rw 199 (q8 c4) ∷
   rw 200 (q7 c4) ∷
   rw 201 (q8 c4) ∷
   rw 202 (q9 c4) ∷
   rw 197 (q10 c4) ∷
   rw 198 (q11 c4) ∷
   rw 199 (q10 c4) ∷
   rw 200 (q11 c4) ∷
   rw 201 (q12 c4) ∷
   rw⁻ 196 (q13 c4) ∷
   rw 201 (q14 c4) ∷
   rw⁻ 200 (q15 c4) ∷
   rw⁻ 199 (q16 c4) ∷
   rw⁻ 206 (q12 c4) ∷
   rw 205 (q17 c4) ∷
   rw⁻ 207 (q9 c4) ∷
   re 206 1 (ℓ "乊丨乊") ∷
   rw 208 (q9 c4) ∷
   rw⁻ 208 (q6 c4) ∷
   rw 207 (q18 c4) ∷
   rw⁻ 209 (q3 c4) ∷
   rw 208 (q19 c4) ∷
   rw⁻ 210 (q6 c4) ∷
   rw 209 (q18 c4) ∷
   rw⁻ 211 (q9 c4) ∷
   rw⁻ 210 (q9 c4) ∷
   re 211 3 (ℓ "丯") ∷
   rw⁻ 212 (q12 c4) ∷
   rw 211 (q20 c4) ∷
   rw⁻ 212 (q21 c4) ∷
   rw 211 (q22 c4) ∷
   rw 212 (q23 c4) ∷
   rw 213 (q22 c4) ∷
   rw 214 (q23 c4) ∷
   rw 215 (q12 c4) ∷
   rw 210 (q24 c4) ∷
   rw 211 (q25 c4) ∷
   rw 212 (q24 c4) ∷
   rw 213 (q25 c4) ∷
   rw 214 (q9 c4) ∷
   rw 209 (q26 c4) ∷
   rw 210 (q27 c4) ∷
   rw 211 (q26 c4) ∷
   rw 212 (q27 c4) ∷
   rw 213 (q6 c4) ∷
   rw 208 (q2 c4) ∷
   rw 209 (q28 c4) ∷
   rw 210 (q2 c4) ∷
   rw 211 (q28 c4) ∷
   rw 212 (q3 c4) ∷
   rw 207 (q4 c4) ∷
   rw 208 (q29 c4) ∷
   rw 209 (q4 c4) ∷
   rw 210 (q29 c4) ∷
   rw 211 (q6 c4) ∷
   rw 206 (q7 c4) ∷
   rw 207 (q30 c4) ∷
   rw 208 (q7 c4) ∷
   rw 209 (q30 c4) ∷
   rw 210 (q9 c4) ∷
   rw 205 (q10 c4) ∷
   rw 206 (q31 c4) ∷
   rw 207 (q10 c4) ∷
   rw 208 (q31 c4) ∷
   rw 209 (q12 c4) ∷
   rw⁻ 204 (q32 c4) ∷
   rw⁻ 203 (q33 c4) ∷
   rw⁻ 202 (q34 c4) ∷
   rw⁻ 210 (q12 c4) ∷
   rw 209 (q17 c4) ∷
   rw⁻ 211 (q9 c4) ∷
   re 210 1 (ℓ "乊丨乊") ∷
   rw 212 (q9 c4) ∷
   rw⁻ 212 (q6 c4) ∷
   rw 211 (q18 c4) ∷
   rw⁻ 213 (q3 c4) ∷
   rw 212 (q19 c4) ∷
   rw⁻ 214 (q6 c4) ∷
   rw 213 (q18 c4) ∷
   rw⁻ 215 (q9 c4) ∷
   rw⁻ 214 (q9 c4) ∷
   re 215 3 (ℓ "丯") ∷
   rw⁻ 216 (q12 c4) ∷
   rw 215 (q20 c4) ∷
   rw⁻ 216 (q21 c4) ∷
   rw 215 (q22 c4) ∷
   rw 216 (q23 c4) ∷
   rw 217 (q22 c4) ∷
   rw 218 (q23 c4) ∷
   rw 219 (q12 c4) ∷
   rw 214 (q24 c4) ∷
   rw 215 (q25 c4) ∷
   rw 216 (q24 c4) ∷
   rw 217 (q25 c4) ∷
   rw 218 (q9 c4) ∷
   rw 213 (q26 c4) ∷
   rw 214 (q27 c4) ∷
   rw 215 (q26 c4) ∷
   rw 216 (q27 c4) ∷
   rw 217 (q6 c4) ∷
   rw 212 (q2 c4) ∷
   rw 213 (q28 c4) ∷
   rw 214 (q2 c4) ∷
   rw 215 (q28 c4) ∷
   rw 216 (q3 c4) ∷ []) Eq.refl
