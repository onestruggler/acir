{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD108 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D108 (Sᴰ : SD108) where

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
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1686
  lem-F4-I-K3-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K3-I-at0440 : Ws → St 1864
  lem-F4-K3-I-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 13 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1871
  lem-F4-K3-K3-at0440 = pickᴰ 14 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 15 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 16 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 17 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 18 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 19 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1867
  lem-F4-K3-CS1-at0440 = pickᴰ 20 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 21 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 22 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 23 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 24 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 25 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 18 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q9 : Ws → Eqn
  q9 c4 = wlE 6 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 47 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 3 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 4 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (ℓ "乇乼") (ℓ "乼乇") (c₃ (CS ↑) (Swap))
  q14 : Ws → Eqn
  q14 c4 = wlE 46 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1590 (lem-F5-23 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (ℓ "丫並") (ℓ "並丫") (c₂ (Swap) (X ↑ ↑))
  q17 : Ws → Eqn
  q17 c4 = sE 1681 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (ℓ "乊並") (ℓ "並乊") (c₃ (Swap ↑) (X ↑))
  q19 : Ws → Eqn
  q19 c4 = sE 1682 (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (ℓ "乥並") (ℓ "並乥") (c₄ (Swap ↑ ↑) (X))
  q21 : Ws → Eqn
  q21 c4 = sE 1680 (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 1456 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1838 (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 1457 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1839 (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 1458 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1845 (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 1459 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1846 (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 1716 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1871 (lem-F4-K3-K3-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1867 (lem-F4-K3-CS1-at0440 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 1461 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 146 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (ℓ "丨乥") (ℓ "乥丨") (c₂ (CS) (Swap))

-- ckt-TST @0440 part5: 162 steps
lem-ckt-TST-at0440-part5 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与中俵临俭俭临上俵俵俵临俭俭临上主与俵与俵俵主上临俵俵临上主俵乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上丫乊乥丨乼乼乥乊丫丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part5 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与中俵临俭俭临上俵俵俵临俭俭临上主与俵与俵俵主上临俵俵临上主俵乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上丫乊乥丨乼乼乥乊丫丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 93 (q1 c4) ∷
   rw⁻ 92 (q2 c4) ∷
   rw⁻ 91 (q3 c4) ∷
   rw⁻ 90 (q4 c4) ∷
   rw⁻ 89 (q4 c4) ∷
   rw⁻ 88 (q3 c4) ∷
   rw⁻ 87 (q5 c4) ∷
   rw⁻ 86 (q5 c4) ∷
   rw⁻ 85 (q5 c4) ∷
   rw⁻ 84 (q2 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q4 c4) ∷
   rw⁻ 81 (q4 c4) ∷
   rw⁻ 80 (q3 c4) ∷
   rw⁻ 79 (q5 c4) ∷
   rw⁻ 78 (q6 c4) ∷
   rw⁻ 109 (q7 c4) ∷
   rw⁻ 108 (q8 c4) ∷
   rw⁻ 110 (q9 c4) ∷
   rw 109 (q10 c4) ∷
   rw⁻ 111 (q11 c4) ∷
   re 110 1 (ℓ "乥乇乥") ∷
   rw 112 (q11 c4) ∷
   rw⁻ 112 (q12 c4) ∷
   rw 111 (q13 c4) ∷
   rw⁻ 113 (q11 c4) ∷
   rw⁻ 112 (q11 c4) ∷
   re 113 3 (ℓ "乎") ∷
   rw⁻ 114 (q9 c4) ∷
   rw 113 (q14 c4) ∷
   rw⁻ 115 (q7 c4) ∷
   rw⁻ 114 (q8 c4) ∷
   rw⁻ 115 (q15 c4) ∷
   rw 114 (q16 c4) ∷
   rw 115 (q17 c4) ∷
   rw 116 (q16 c4) ∷
   rw 117 (q17 c4) ∷
   rw 118 (q7 c4) ∷
   rw 113 (q18 c4) ∷
   rw 114 (q19 c4) ∷
   rw 115 (q18 c4) ∷
   rw 116 (q19 c4) ∷
   rw 117 (q9 c4) ∷
   rw 112 (q20 c4) ∷
   rw 113 (q21 c4) ∷
   rw 114 (q20 c4) ∷
   rw 115 (q21 c4) ∷
   rw 116 (q11 c4) ∷
   rw 111 (q22 c4) ∷
   rw 112 (q23 c4) ∷
   rw 113 (q22 c4) ∷
   rw 114 (q23 c4) ∷
   rw 115 (q12 c4) ∷
   rw 110 (q24 c4) ∷
   rw 111 (q25 c4) ∷
   rw 112 (q24 c4) ∷
   rw 113 (q25 c4) ∷
   rw 114 (q11 c4) ∷
   rw 109 (q26 c4) ∷
   rw 110 (q27 c4) ∷
   rw 111 (q26 c4) ∷
   rw 112 (q27 c4) ∷
   rw 113 (q9 c4) ∷
   rw 108 (q28 c4) ∷
   rw 109 (q29 c4) ∷
   rw 110 (q28 c4) ∷
   rw 111 (q29 c4) ∷
   rw 112 (q7 c4) ∷
   rw⁻ 107 (q5 c4) ∷
   rw⁻ 106 (q1 c4) ∷
   rw⁻ 105 (q2 c4) ∷
   rw⁻ 104 (q3 c4) ∷
   rw⁻ 103 (q5 c4) ∷
   rw⁻ 102 (q5 c4) ∷
   rw⁻ 101 (q3 c4) ∷
   rw⁻ 100 (q2 c4) ∷
   rw⁻ 99 (q1 c4) ∷
   rw⁻ 98 (q5 c4) ∷
   rw⁻ 97 (q5 c4) ∷
   rw⁻ 96 (q1 c4) ∷
   rw⁻ 95 (q2 c4) ∷
   rw⁻ 94 (q3 c4) ∷
   rw⁻ 93 (q4 c4) ∷
   rw⁻ 92 (q4 c4) ∷
   rw⁻ 91 (q3 c4) ∷
   rw⁻ 90 (q5 c4) ∷
   rw⁻ 89 (q5 c4) ∷
   rw⁻ 88 (q5 c4) ∷
   rw⁻ 87 (q2 c4) ∷
   rw⁻ 86 (q3 c4) ∷
   rw⁻ 85 (q4 c4) ∷
   rw⁻ 84 (q4 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q5 c4) ∷
   rw⁻ 81 (q6 c4) ∷
   rw 112 (q30 c4) ∷
   rw⁻ 111 (q31 c4) ∷
   rw⁻ 110 (q31 c4) ∷
   rw⁻ 109 (q32 c4) ∷
   rw⁻ 108 (q33 c4) ∷
   rw⁻ 107 (q34 c4) ∷
   rw⁻ 106 (q31 c4) ∷
   rw⁻ 105 (q31 c4) ∷
   rw⁻ 104 (q34 c4) ∷
   rw⁻ 103 (q33 c4) ∷
   rw⁻ 102 (q32 c4) ∷
   rw⁻ 101 (q31 c4) ∷
   rw⁻ 100 (q31 c4) ∷
   rw⁻ 99 (q32 c4) ∷
   rw⁻ 98 (q33 c4) ∷
   rw⁻ 97 (q34 c4) ∷
   rw⁻ 96 (q35 c4) ∷
   rw⁻ 95 (q35 c4) ∷
   rw⁻ 94 (q34 c4) ∷
   rw⁻ 93 (q31 c4) ∷
   rw⁻ 92 (q31 c4) ∷
   rw⁻ 91 (q31 c4) ∷
   rw⁻ 90 (q33 c4) ∷
   rw⁻ 89 (q34 c4) ∷
   rw⁻ 88 (q35 c4) ∷
   rw⁻ 87 (q35 c4) ∷
   rw⁻ 86 (q34 c4) ∷
   rw⁻ 85 (q31 c4) ∷
   rw⁻ 84 (q36 c4) ∷
   rw⁻ 116 (q37 c4) ∷
   rw⁻ 115 (q38 c4) ∷
   rw⁻ 114 (q39 c4) ∷
   rw⁻ 113 (q39 c4) ∷
   rw⁻ 112 (q38 c4) ∷
   rw⁻ 111 (q40 c4) ∷
   rw⁻ 110 (q41 c4) ∷
   rw⁻ 109 (q39 c4) ∷
   rw⁻ 108 (q39 c4) ∷
   rw⁻ 107 (q41 c4) ∷
   rw⁻ 106 (q40 c4) ∷
   rw⁻ 105 (q38 c4) ∷
   rw⁻ 104 (q39 c4) ∷
   rw⁻ 103 (q39 c4) ∷
   rw⁻ 102 (q38 c4) ∷
   rw⁻ 101 (q40 c4) ∷
   rw⁻ 100 (q41 c4) ∷
   rw⁻ 99 (q42 c4) ∷
   rw⁻ 98 (q42 c4) ∷
   rw⁻ 97 (q41 c4) ∷
   rw⁻ 96 (q39 c4) ∷
   rw⁻ 95 (q39 c4) ∷
   rw⁻ 94 (q39 c4) ∷
   rw⁻ 93 (q40 c4) ∷
   rw⁻ 92 (q41 c4) ∷
   rw⁻ 91 (q42 c4) ∷
   rw⁻ 90 (q42 c4) ∷
   rw⁻ 89 (q41 c4) ∷
   rw⁻ 88 (q39 c4) ∷
   rw⁻ 87 (q43 c4) ∷
   rw⁻ 121 (q7 c4) ∷
   rw 120 (q44 c4) ∷
   rw⁻ 122 (q9 c4) ∷
   re 121 1 (ℓ "乊丨乊") ∷
   rw 123 (q9 c4) ∷
   rw⁻ 123 (q11 c4) ∷
   rw 122 (q45 c4) ∷
   rw⁻ 124 (q12 c4) ∷ []) Eq.refl
