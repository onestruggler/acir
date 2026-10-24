{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD117 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D117 (Sᴰ : SD117) where

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
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R : Ws → St 1844
  lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R : Ws → St 1845
  lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R = pickᴰ 6 Sᴰ
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R : Ws → St 1846
  lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R = pickᴰ 7 Sᴰ
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R : Ws → St 1847
  lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R : Ws → St 1848
  lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R = pickᴰ 9 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1850
  lem-F4-K2-K2-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1851
  lem-F4-CS1-CS1-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1852
  lem-F4-CS1-K1-at0440 = pickᴰ 15 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 17 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 18 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 19 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 20 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 21 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 22 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 23 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1858
  lem-F4-CS1-K2-at0440 = pickᴰ 24 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 25 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 26 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 27 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 1457 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1848 (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 3 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1458 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1844 (lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 6 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1459 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1847 (lem-comm-push-SBOX⟨4·0·12·3⟩-sw0-R c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 18 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1851 (lem-F4-CS1-CS1-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1858 (lem-F4-CS1-K2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1859 (lem-F4-CS1-CS2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1852 (lem-F4-CS1-K1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1715 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 1461 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q25 : Ws → Eqn
  q25 c4 = wlE 47 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 4 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (ℓ "乇乼") (ℓ "乼乇") (c₃ (CS ↑) (Swap))
  q28 : Ws → Eqn
  q28 c4 = wlE 46 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1590 (lem-F5-23 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (ℓ "丫並") (ℓ "並丫") (c₂ (Swap) (X ↑ ↑))
  q31 : Ws → Eqn
  q31 c4 = sE 1681 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (ℓ "乊並") (ℓ "並乊") (c₃ (Swap ↑) (X ↑))
  q33 : Ws → Eqn
  q33 c4 = sE 1682 (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (ℓ "乥並") (ℓ "並乥") (c₄ (Swap ↑ ↑) (X))
  q35 : Ws → Eqn
  q35 c4 = sE 1680 (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 1456 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1838 (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1839 (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1845 (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1846 (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q45 : Ws → Eqn
  q45 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)

-- ckt-TST @0440 part15: 111 steps
lem-ckt-TST-at0440-part15 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与中俵临俭丫乊乥丠俨丠俨乥乊丫丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与中俵临俭俭临上俵丫乊乥乼乥乊並侾並丫侬丫乊乥乼乥乊丫乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part15 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与中俵临俭丫乊乥丠俨丠俨乥乊丫丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与中俵临俭俭临上俵丫乊乥乼乥乊並侾並丫侬丫乊乥乼乥乊丫乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw 211 (q1 c4) ∷
   rw 212 (q2 c4) ∷
   rw 213 (q1 c4) ∷
   rw 214 (q2 c4) ∷
   rw 215 (q3 c4) ∷
   rw 210 (q4 c4) ∷
   rw 211 (q5 c4) ∷
   rw 212 (q4 c4) ∷
   rw 213 (q5 c4) ∷
   rw 214 (q6 c4) ∷
   rw 209 (q7 c4) ∷
   rw 210 (q8 c4) ∷
   rw 211 (q7 c4) ∷
   rw 212 (q8 c4) ∷
   rw 213 (q9 c4) ∷
   rw⁻ 208 (q10 c4) ∷
   rw⁻ 207 (q11 c4) ∷
   rw⁻ 206 (q12 c4) ∷
   rw⁻ 205 (q13 c4) ∷
   rw 213 (q14 c4) ∷
   rw⁻ 212 (q15 c4) ∷
   rw⁻ 211 (q15 c4) ∷
   rw⁻ 210 (q16 c4) ∷
   rw⁻ 209 (q17 c4) ∷
   rw⁻ 208 (q18 c4) ∷
   rw⁻ 217 (q19 c4) ∷
   rw⁻ 216 (q20 c4) ∷
   rw⁻ 215 (q21 c4) ∷
   rw⁻ 214 (q21 c4) ∷
   rw⁻ 213 (q20 c4) ∷
   rw⁻ 212 (q22 c4) ∷
   rw⁻ 211 (q23 c4) ∷
   rw⁻ 222 (q9 c4) ∷
   rw⁻ 221 (q24 c4) ∷
   rw⁻ 223 (q6 c4) ∷
   rw 222 (q25 c4) ∷
   rw⁻ 224 (q3 c4) ∷
   re 223 1 (ℓ "乥乇乥") ∷
   rw 225 (q3 c4) ∷
   rw⁻ 225 (q26 c4) ∷
   rw 224 (q27 c4) ∷
   rw⁻ 226 (q3 c4) ∷
   rw⁻ 225 (q3 c4) ∷
   re 226 3 (ℓ "乎") ∷
   rw⁻ 227 (q6 c4) ∷
   rw 226 (q28 c4) ∷
   rw⁻ 228 (q9 c4) ∷
   rw⁻ 227 (q24 c4) ∷
   rw⁻ 228 (q29 c4) ∷
   rw 227 (q30 c4) ∷
   rw 228 (q31 c4) ∷
   rw 229 (q30 c4) ∷
   rw 230 (q31 c4) ∷
   rw 231 (q9 c4) ∷
   rw 226 (q32 c4) ∷
   rw 227 (q33 c4) ∷
   rw 228 (q32 c4) ∷
   rw 229 (q33 c4) ∷
   rw 230 (q6 c4) ∷
   rw 225 (q34 c4) ∷
   rw 226 (q35 c4) ∷
   rw 227 (q34 c4) ∷
   rw 228 (q35 c4) ∷
   rw 229 (q3 c4) ∷
   rw 224 (q36 c4) ∷
   rw 225 (q37 c4) ∷
   rw 226 (q36 c4) ∷
   rw 227 (q37 c4) ∷
   rw 228 (q26 c4) ∷
   rw 223 (q1 c4) ∷
   rw 224 (q38 c4) ∷
   rw 225 (q1 c4) ∷
   rw 226 (q38 c4) ∷
   rw 227 (q3 c4) ∷
   rw 222 (q4 c4) ∷
   rw 223 (q39 c4) ∷
   rw 224 (q4 c4) ∷
   rw 225 (q39 c4) ∷
   rw 226 (q6 c4) ∷
   rw 221 (q7 c4) ∷
   rw 222 (q40 c4) ∷
   rw 223 (q7 c4) ∷
   rw 224 (q40 c4) ∷
   rw 225 (q9 c4) ∷
   rw⁻ 220 (q41 c4) ∷
   rw⁻ 219 (q42 c4) ∷
   rw⁻ 218 (q43 c4) ∷
   rw⁻ 217 (q43 c4) ∷
   rw⁻ 216 (q42 c4) ∷
   rw⁻ 215 (q44 c4) ∷
   rw⁻ 214 (q45 c4) ∷
   rw⁻ 226 (q9 c4) ∷
   rw⁻ 225 (q24 c4) ∷
   rw⁻ 227 (q6 c4) ∷
   rw 226 (q25 c4) ∷
   rw⁻ 228 (q3 c4) ∷
   re 227 1 (ℓ "乥乇乥") ∷
   rw 229 (q3 c4) ∷
   rw⁻ 229 (q26 c4) ∷
   rw 228 (q27 c4) ∷
   rw⁻ 230 (q3 c4) ∷
   rw⁻ 229 (q3 c4) ∷
   re 230 3 (ℓ "乎") ∷
   rw⁻ 231 (q6 c4) ∷
   rw 230 (q28 c4) ∷
   rw⁻ 232 (q9 c4) ∷
   rw⁻ 231 (q24 c4) ∷
   rw⁻ 232 (q29 c4) ∷
   rw 231 (q30 c4) ∷
   rw 232 (q31 c4) ∷
   rw 233 (q30 c4) ∷ []) Eq.refl
