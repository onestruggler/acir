{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD113 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D113 (Sᴰ : SD113) where

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
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R : Ws → St 1681
  lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R : Ws → St 1682
  lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R = pickᴰ 2 Sᴰ
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 3 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 4 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 5 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1686
  lem-F4-I-K3-at0440 = pickᴰ 6 Sᴰ
  lem-F4-K2-I-at0440 : Ws → St 1862
  lem-F4-K2-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1850
  lem-F4-K2-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-K2-K3-at0440 : Ws → St 1870
  lem-F4-K2-K3-at0440 = pickᴰ 10 Sᴰ
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
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 16 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 17 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1867
  lem-F4-K3-CS1-at0440 = pickᴰ 18 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 19 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 20 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 21 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1862 (lem-F4-K2-I-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1870 (lem-F4-K2-K3-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1461 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1716 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1871 (lem-F4-K3-K3-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1867 (lem-F4-K3-CS1-at0440 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 18 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q23 : Ws → Eqn
  q23 c4 = wlE 6 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 47 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 3 (lit c4)
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

-- ckt-TST @0440 part10: 134 steps
lem-ckt-TST-at0440-part10 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临与临与俵俵临上主俵俵主上俭主俵俵主上临俵俵临一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主丫乊乥乼並俜並乥俇乥乼乥乊丫乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part10 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临与临与俵俵临上主俵俵主上俭主俵俵主上临俵俵临一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主丫乊乥乼並俜並乥俇乥乼乥乊丫乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 137 (q1 c4) ∷
   rw⁻ 136 (q2 c4) ∷
   rw⁻ 135 (q3 c4) ∷
   rw⁻ 134 (q4 c4) ∷
   rw⁻ 133 (q4 c4) ∷
   rw⁻ 132 (q3 c4) ∷
   rw⁻ 131 (q2 c4) ∷
   rw⁻ 130 (q1 c4) ∷
   rw⁻ 129 (q5 c4) ∷
   rw⁻ 128 (q5 c4) ∷
   rw⁻ 127 (q1 c4) ∷
   rw⁻ 126 (q4 c4) ∷
   rw⁻ 125 (q4 c4) ∷
   rw⁻ 124 (q4 c4) ∷
   rw⁻ 123 (q2 c4) ∷
   rw⁻ 122 (q1 c4) ∷
   rw⁻ 121 (q5 c4) ∷
   rw⁻ 120 (q5 c4) ∷
   rw⁻ 119 (q1 c4) ∷
   rw⁻ 118 (q4 c4) ∷
   rw⁻ 117 (q6 c4) ∷
   rw⁻ 160 (q7 c4) ∷
   rw⁻ 159 (q8 c4) ∷
   rw⁻ 158 (q9 c4) ∷
   rw⁻ 157 (q9 c4) ∷
   rw⁻ 156 (q8 c4) ∷
   rw⁻ 155 (q10 c4) ∷
   rw⁻ 154 (q11 c4) ∷
   rw⁻ 153 (q9 c4) ∷
   rw⁻ 152 (q9 c4) ∷
   rw⁻ 151 (q11 c4) ∷
   rw⁻ 150 (q12 c4) ∷
   rw⁻ 149 (q10 c4) ∷
   rw⁻ 148 (q11 c4) ∷
   rw⁻ 147 (q9 c4) ∷
   rw⁻ 146 (q9 c4) ∷
   rw⁻ 145 (q11 c4) ∷
   rw⁻ 144 (q10 c4) ∷
   rw⁻ 143 (q8 c4) ∷
   rw⁻ 142 (q9 c4) ∷
   rw⁻ 141 (q9 c4) ∷
   rw⁻ 140 (q8 c4) ∷
   rw⁻ 139 (q10 c4) ∷
   rw⁻ 138 (q11 c4) ∷
   rw⁻ 137 (q9 c4) ∷
   rw⁻ 136 (q9 c4) ∷
   rw⁻ 135 (q11 c4) ∷
   rw⁻ 134 (q10 c4) ∷
   rw⁻ 133 (q8 c4) ∷
   rw⁻ 132 (q12 c4) ∷
   rw⁻ 131 (q12 c4) ∷
   rw⁻ 130 (q8 c4) ∷
   rw⁻ 129 (q9 c4) ∷
   rw⁻ 128 (q9 c4) ∷
   rw⁻ 127 (q9 c4) ∷
   rw⁻ 126 (q10 c4) ∷
   rw⁻ 125 (q8 c4) ∷
   rw⁻ 124 (q12 c4) ∷
   rw⁻ 123 (q12 c4) ∷
   rw⁻ 122 (q8 c4) ∷
   rw⁻ 121 (q9 c4) ∷
   rw⁻ 120 (q13 c4) ∷
   rw 164 (q14 c4) ∷
   rw⁻ 163 (q15 c4) ∷
   rw⁻ 162 (q16 c4) ∷
   rw⁻ 161 (q17 c4) ∷
   rw⁻ 160 (q17 c4) ∷
   rw⁻ 159 (q16 c4) ∷
   rw⁻ 158 (q15 c4) ∷
   rw⁻ 157 (q18 c4) ∷
   rw⁻ 156 (q17 c4) ∷
   rw⁻ 155 (q17 c4) ∷
   rw⁻ 154 (q18 c4) ∷
   rw⁻ 153 (q19 c4) ∷
   rw⁻ 152 (q15 c4) ∷
   rw⁻ 151 (q18 c4) ∷
   rw⁻ 150 (q17 c4) ∷
   rw⁻ 149 (q17 c4) ∷
   rw⁻ 148 (q18 c4) ∷
   rw⁻ 147 (q15 c4) ∷
   rw⁻ 146 (q16 c4) ∷
   rw⁻ 145 (q17 c4) ∷
   rw⁻ 144 (q17 c4) ∷
   rw⁻ 143 (q16 c4) ∷
   rw⁻ 142 (q15 c4) ∷
   rw⁻ 141 (q18 c4) ∷
   rw⁻ 140 (q17 c4) ∷
   rw⁻ 139 (q17 c4) ∷
   rw⁻ 138 (q18 c4) ∷
   rw⁻ 137 (q15 c4) ∷
   rw⁻ 136 (q16 c4) ∷
   rw⁻ 135 (q19 c4) ∷
   rw⁻ 134 (q19 c4) ∷
   rw⁻ 133 (q16 c4) ∷
   rw⁻ 132 (q17 c4) ∷
   rw⁻ 131 (q17 c4) ∷
   rw⁻ 130 (q17 c4) ∷
   rw⁻ 129 (q15 c4) ∷
   rw⁻ 128 (q16 c4) ∷
   rw⁻ 127 (q19 c4) ∷
   rw⁻ 126 (q19 c4) ∷
   rw⁻ 125 (q16 c4) ∷
   rw⁻ 124 (q17 c4) ∷
   rw⁻ 123 (q20 c4) ∷
   rw⁻ 169 (q21 c4) ∷
   rw⁻ 168 (q22 c4) ∷
   rw⁻ 170 (q23 c4) ∷
   rw 169 (q24 c4) ∷
   rw⁻ 171 (q25 c4) ∷
   re 170 1 (ℓ "乥乇乥") ∷
   rw 172 (q25 c4) ∷
   rw⁻ 172 (q26 c4) ∷
   rw 171 (q27 c4) ∷
   rw⁻ 173 (q25 c4) ∷
   rw⁻ 172 (q25 c4) ∷
   re 173 3 (ℓ "乎") ∷
   rw⁻ 174 (q23 c4) ∷
   rw 173 (q28 c4) ∷
   rw⁻ 175 (q21 c4) ∷
   rw⁻ 174 (q22 c4) ∷
   rw⁻ 175 (q29 c4) ∷
   rw 174 (q30 c4) ∷
   rw 175 (q31 c4) ∷
   rw 176 (q30 c4) ∷
   rw 177 (q31 c4) ∷
   rw 178 (q21 c4) ∷
   rw 173 (q32 c4) ∷
   rw 174 (q33 c4) ∷
   rw 175 (q32 c4) ∷
   rw 176 (q33 c4) ∷
   rw 177 (q23 c4) ∷
   rw 172 (q34 c4) ∷
   rw 173 (q35 c4) ∷
   rw 174 (q34 c4) ∷ []) Eq.refl
