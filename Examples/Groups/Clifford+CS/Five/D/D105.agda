{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD105 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D105 (Sᴰ : SD105) where

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
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K2-I-at0440 : Ws → St 1862
  lem-F4-K2-I-at0440 = pickᴰ 13 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 14 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1850
  lem-F4-K2-K2-at0440 = pickᴰ 15 Sᴰ
  lem-F4-K3-I-at0440 : Ws → St 1864
  lem-F4-K3-I-at0440 = pickᴰ 16 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 17 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 18 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1851
  lem-F4-CS1-CS1-at0440 = pickᴰ 19 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1863
  lem-F4-CS1-I-at0440 = pickᴰ 20 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1852
  lem-F4-CS1-K1-at0440 = pickᴰ 21 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 22 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 23 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 24 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 25 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 26 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 27 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1867
  lem-F4-K3-CS1-at0440 = pickᴰ 28 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 29 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 30 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1858
  lem-F4-CS1-K2-at0440 = pickᴰ 31 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 32 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 33 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 34 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 35 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 36 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1848 (lem-comm-push-SBOX⟨4·0·31·2⟩-sw2-R c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1457 (lit c4)
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
  q13 c4 = sE 1863 (lem-F4-CS1-I-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1852 (lem-F4-CS1-K1-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 1715 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1862 (lem-F4-K2-I-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 1461 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 1716 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1867 (lem-F4-K3-CS1-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q34 : Ws → Eqn
  q34 c4 = wlE 47 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 4 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (ℓ "乇乼") (ℓ "乼乇") (c₃ (CS ↑) (Swap))
  q37 : Ws → Eqn
  q37 c4 = wlE 46 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1590 (lem-F5-23 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (ℓ "丫並") (ℓ "並丫") (c₂ (Swap) (X ↑ ↑))
  q40 : Ws → Eqn
  q40 c4 = sE 1681 (lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (ℓ "乊並") (ℓ "並乊") (c₃ (Swap ↑) (X ↑))
  q42 : Ws → Eqn
  q42 c4 = sE 1682 (lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (ℓ "乥並") (ℓ "並乥") (c₄ (Swap ↑ ↑) (X))
  q44 : Ws → Eqn
  q44 c4 = sE 1680 (lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 1456 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1838 (lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4)
  q47 : Ws → Eqn
  q47 c4 = sE 1839 (lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4)
  q48 : Ws → Eqn
  q48 c4 = sE 1845 (lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4)
  q49 : Ws → Eqn
  q49 c4 = sE 1846 (lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4)
  q50 : Ws → Eqn
  q50 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q55 : Ws → Eqn
  q55 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)

-- ckt-TST @0440 part2: 200 steps
lem-ckt-TST-at0440-part2 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与中俵临俭俭临上俵俵俵临俭丫乊业乥俨丠俨乥乊丫丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与中俵临俭俭临上俵与俵与俵俵临俭俭临上主俵俵丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part2 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与中俵临俭俭临上俵俵俵临俭丫乊业乥俨丠俨乥乊丫丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与中俵临俭俭临上俵与俵与俵俵临俭俭临上主俵俵丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw 51 (q1 c4) ∷
   rw 52 (q2 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q3 c4) ∷
   rw 49 (q4 c4) ∷
   rw 50 (q5 c4) ∷
   rw 51 (q4 c4) ∷
   rw 52 (q5 c4) ∷
   rw 53 (q6 c4) ∷
   rw 48 (q7 c4) ∷
   rw 49 (q8 c4) ∷
   rw 50 (q7 c4) ∷
   rw 51 (q8 c4) ∷
   rw 52 (q9 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q11 c4) ∷
   rw⁻ 45 (q12 c4) ∷
   rw⁻ 44 (q12 c4) ∷
   rw⁻ 43 (q12 c4) ∷
   rw⁻ 42 (q13 c4) ∷
   rw⁻ 41 (q11 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q11 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw 52 (q15 c4) ∷
   rw⁻ 51 (q16 c4) ∷
   rw⁻ 50 (q16 c4) ∷
   rw⁻ 49 (q17 c4) ∷
   rw⁻ 48 (q18 c4) ∷
   rw⁻ 47 (q18 c4) ∷
   rw⁻ 46 (q18 c4) ∷
   rw⁻ 45 (q19 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw⁻ 43 (q16 c4) ∷
   rw⁻ 42 (q16 c4) ∷
   rw⁻ 41 (q17 c4) ∷
   rw⁻ 40 (q18 c4) ∷
   rw⁻ 39 (q20 c4) ∷
   rw⁻ 56 (q21 c4) ∷
   rw⁻ 55 (q22 c4) ∷
   rw⁻ 54 (q23 c4) ∷
   rw⁻ 53 (q23 c4) ∷
   rw⁻ 52 (q22 c4) ∷
   rw⁻ 51 (q24 c4) ∷
   rw⁻ 50 (q24 c4) ∷
   rw⁻ 49 (q24 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 47 (q22 c4) ∷
   rw⁻ 46 (q23 c4) ∷
   rw⁻ 45 (q23 c4) ∷
   rw⁻ 44 (q22 c4) ∷
   rw⁻ 43 (q24 c4) ∷
   rw⁻ 42 (q26 c4) ∷
   rw 60 (q27 c4) ∷
   rw⁻ 59 (q28 c4) ∷
   rw⁻ 58 (q29 c4) ∷
   rw⁻ 57 (q30 c4) ∷
   rw⁻ 56 (q30 c4) ∷
   rw⁻ 55 (q29 c4) ∷
   rw⁻ 54 (q31 c4) ∷
   rw⁻ 53 (q31 c4) ∷
   rw⁻ 52 (q31 c4) ∷
   rw⁻ 51 (q28 c4) ∷
   rw⁻ 50 (q29 c4) ∷
   rw⁻ 49 (q30 c4) ∷
   rw⁻ 48 (q30 c4) ∷
   rw⁻ 47 (q29 c4) ∷
   rw⁻ 46 (q31 c4) ∷
   rw⁻ 45 (q32 c4) ∷
   rw⁻ 65 (q9 c4) ∷
   rw⁻ 64 (q33 c4) ∷
   rw⁻ 66 (q6 c4) ∷
   rw 65 (q34 c4) ∷
   rw⁻ 67 (q3 c4) ∷
   re 66 1 (ℓ "乥乇乥") ∷
   rw 68 (q3 c4) ∷
   rw⁻ 68 (q35 c4) ∷
   rw 67 (q36 c4) ∷
   rw⁻ 69 (q3 c4) ∷
   rw⁻ 68 (q3 c4) ∷
   re 69 3 (ℓ "乎") ∷
   rw⁻ 70 (q6 c4) ∷
   rw 69 (q37 c4) ∷
   rw⁻ 71 (q9 c4) ∷
   rw⁻ 70 (q33 c4) ∷
   rw⁻ 71 (q38 c4) ∷
   rw 70 (q39 c4) ∷
   rw 71 (q40 c4) ∷
   rw 72 (q39 c4) ∷
   rw 73 (q40 c4) ∷
   rw 74 (q9 c4) ∷
   rw 69 (q41 c4) ∷
   rw 70 (q42 c4) ∷
   rw 71 (q41 c4) ∷
   rw 72 (q42 c4) ∷
   rw 73 (q6 c4) ∷
   rw 68 (q43 c4) ∷
   rw 69 (q44 c4) ∷
   rw 70 (q43 c4) ∷
   rw 71 (q44 c4) ∷
   rw 72 (q3 c4) ∷
   rw 67 (q45 c4) ∷
   rw 68 (q46 c4) ∷
   rw 69 (q45 c4) ∷
   rw 70 (q46 c4) ∷
   rw 71 (q35 c4) ∷
   rw 66 (q2 c4) ∷
   rw 67 (q47 c4) ∷
   rw 68 (q2 c4) ∷
   rw 69 (q47 c4) ∷
   rw 70 (q3 c4) ∷
   rw 65 (q4 c4) ∷
   rw 66 (q48 c4) ∷
   rw 67 (q4 c4) ∷
   rw 68 (q48 c4) ∷
   rw 69 (q6 c4) ∷
   rw 64 (q7 c4) ∷
   rw 65 (q49 c4) ∷
   rw 66 (q7 c4) ∷
   rw 67 (q49 c4) ∷
   rw 68 (q9 c4) ∷
   rw⁻ 63 (q50 c4) ∷
   rw⁻ 62 (q51 c4) ∷
   rw⁻ 61 (q52 c4) ∷
   rw⁻ 60 (q53 c4) ∷
   rw⁻ 59 (q53 c4) ∷
   rw⁻ 58 (q52 c4) ∷
   rw⁻ 57 (q54 c4) ∷
   rw⁻ 56 (q54 c4) ∷
   rw⁻ 55 (q54 c4) ∷
   rw⁻ 54 (q51 c4) ∷
   rw⁻ 53 (q52 c4) ∷
   rw⁻ 52 (q53 c4) ∷
   rw⁻ 51 (q53 c4) ∷
   rw⁻ 50 (q52 c4) ∷
   rw⁻ 49 (q54 c4) ∷
   rw⁻ 48 (q55 c4) ∷
   rw⁻ 69 (q9 c4) ∷
   rw⁻ 68 (q33 c4) ∷
   rw⁻ 70 (q6 c4) ∷
   rw 69 (q34 c4) ∷
   rw⁻ 71 (q3 c4) ∷
   re 70 1 (ℓ "乥乇乥") ∷
   rw 72 (q3 c4) ∷
   rw⁻ 72 (q35 c4) ∷
   rw 71 (q36 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 72 (q3 c4) ∷
   re 73 3 (ℓ "乎") ∷
   rw⁻ 74 (q6 c4) ∷
   rw 73 (q37 c4) ∷
   rw⁻ 75 (q9 c4) ∷
   rw⁻ 74 (q33 c4) ∷
   rw⁻ 75 (q38 c4) ∷
   rw 74 (q39 c4) ∷
   rw 75 (q40 c4) ∷
   rw 76 (q39 c4) ∷
   rw 77 (q40 c4) ∷
   rw 78 (q9 c4) ∷
   rw 73 (q41 c4) ∷
   rw 74 (q42 c4) ∷
   rw 75 (q41 c4) ∷
   rw 76 (q42 c4) ∷
   rw 77 (q6 c4) ∷
   rw 72 (q43 c4) ∷
   rw 73 (q44 c4) ∷
   rw 74 (q43 c4) ∷
   rw 75 (q44 c4) ∷
   rw 76 (q3 c4) ∷
   rw 71 (q45 c4) ∷
   rw 72 (q46 c4) ∷
   rw 73 (q45 c4) ∷
   rw 74 (q46 c4) ∷
   rw 75 (q35 c4) ∷
   rw 70 (q2 c4) ∷
   rw 71 (q47 c4) ∷
   rw 72 (q2 c4) ∷
   rw 73 (q47 c4) ∷
   rw 74 (q3 c4) ∷
   rw 69 (q4 c4) ∷
   rw 70 (q48 c4) ∷
   rw 71 (q4 c4) ∷
   rw 72 (q48 c4) ∷
   rw 73 (q6 c4) ∷
   rw 68 (q7 c4) ∷
   rw 69 (q49 c4) ∷
   rw 70 (q7 c4) ∷
   rw 71 (q49 c4) ∷
   rw 72 (q9 c4) ∷
   rw⁻ 67 (q54 c4) ∷
   rw⁻ 66 (q50 c4) ∷
   rw⁻ 65 (q51 c4) ∷
   rw⁻ 64 (q52 c4) ∷
   rw⁻ 63 (q53 c4) ∷
   rw⁻ 62 (q53 c4) ∷
   rw⁻ 61 (q52 c4) ∷
   rw⁻ 60 (q54 c4) ∷
   rw⁻ 59 (q54 c4) ∷ []) Eq.refl
