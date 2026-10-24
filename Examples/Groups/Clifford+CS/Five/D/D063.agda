{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD063 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D063 (Sᴰ : SD063) where

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
  lem-F4-K1-I-at0440 : Ws → St 1687
  lem-F4-K1-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K1-K1-at0440 : Ws → St 1688
  lem-F4-K1-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K1-K2-at0440 : Ws → St 1689
  lem-F4-K1-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-K1-K3-at0440 : Ws → St 1690
  lem-F4-K1-K3-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K1-CS1-at0440 : Ws → St 1692
  lem-F4-K1-CS1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 13 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 14 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1689 (lem-F4-K1-K2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1694 (lem-F4-K1-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1687 (lem-F4-K1-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1690 (lem-F4-K1-K3-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1692 (lem-F4-K1-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1688 (lem-F4-K1-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1461 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1460 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 18 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q17 : Ws → Eqn
  q17 c4 = wlE 6 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wlE 47 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 3 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 4 (lit c4)
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
  q30 : Ws → Eqn
  q30 c4 = wlE 1456 (lit c4)

-- ckt-TST @0440 part13: 122 steps
lem-ckt-TST-at0440-part13 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临与中与上主俵俵主上中一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与中丫乊乥丠乼俜並俜乼乥乊丫丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part13 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临与中与上主俵俵主上中一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与中丫乊乥丠乼俜並俜乼乥乊丫丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 177 (q1 c4) ∷
   rw⁻ 176 (q2 c4) ∷
   rw⁻ 175 (q2 c4) ∷
   rw⁻ 174 (q1 c4) ∷
   rw⁻ 173 (q3 c4) ∷
   rw⁻ 172 (q4 c4) ∷
   rw⁻ 171 (q2 c4) ∷
   rw⁻ 170 (q2 c4) ∷
   rw⁻ 169 (q4 c4) ∷
   rw⁻ 168 (q5 c4) ∷
   rw⁻ 167 (q3 c4) ∷
   rw⁻ 166 (q4 c4) ∷
   rw⁻ 165 (q2 c4) ∷
   rw⁻ 164 (q2 c4) ∷
   rw⁻ 163 (q4 c4) ∷
   rw⁻ 162 (q3 c4) ∷
   rw⁻ 161 (q1 c4) ∷
   rw⁻ 160 (q2 c4) ∷
   rw⁻ 159 (q2 c4) ∷
   rw⁻ 158 (q1 c4) ∷
   rw⁻ 157 (q3 c4) ∷
   rw⁻ 156 (q4 c4) ∷
   rw⁻ 155 (q2 c4) ∷
   rw⁻ 154 (q2 c4) ∷
   rw⁻ 153 (q4 c4) ∷
   rw⁻ 152 (q3 c4) ∷
   rw⁻ 151 (q1 c4) ∷
   rw⁻ 150 (q5 c4) ∷
   rw⁻ 149 (q5 c4) ∷
   rw⁻ 148 (q1 c4) ∷
   rw⁻ 147 (q2 c4) ∷
   rw⁻ 146 (q2 c4) ∷
   rw⁻ 145 (q2 c4) ∷
   rw⁻ 144 (q3 c4) ∷
   rw⁻ 143 (q1 c4) ∷
   rw⁻ 142 (q5 c4) ∷
   rw⁻ 141 (q5 c4) ∷
   rw⁻ 140 (q1 c4) ∷
   rw⁻ 139 (q2 c4) ∷
   rw⁻ 138 (q6 c4) ∷
   rw⁻ 188 (q7 c4) ∷
   rw⁻ 187 (q8 c4) ∷
   rw⁻ 186 (q9 c4) ∷
   rw⁻ 185 (q10 c4) ∷
   rw⁻ 184 (q11 c4) ∷
   rw⁻ 183 (q11 c4) ∷
   rw⁻ 182 (q10 c4) ∷
   rw⁻ 181 (q9 c4) ∷
   rw⁻ 180 (q12 c4) ∷
   rw⁻ 179 (q11 c4) ∷
   rw⁻ 178 (q11 c4) ∷
   rw⁻ 177 (q12 c4) ∷
   rw⁻ 176 (q9 c4) ∷
   rw⁻ 175 (q10 c4) ∷
   rw⁻ 174 (q11 c4) ∷
   rw⁻ 173 (q11 c4) ∷
   rw⁻ 172 (q10 c4) ∷
   rw⁻ 171 (q13 c4) ∷
   rw⁻ 170 (q9 c4) ∷
   rw⁻ 169 (q10 c4) ∷
   rw⁻ 168 (q11 c4) ∷
   rw⁻ 167 (q11 c4) ∷
   rw⁻ 166 (q10 c4) ∷
   rw⁻ 165 (q9 c4) ∷
   rw⁻ 164 (q12 c4) ∷
   rw⁻ 163 (q11 c4) ∷
   rw⁻ 162 (q11 c4) ∷
   rw⁻ 161 (q12 c4) ∷
   rw⁻ 160 (q9 c4) ∷
   rw⁻ 159 (q10 c4) ∷
   rw⁻ 158 (q11 c4) ∷
   rw⁻ 157 (q11 c4) ∷
   rw⁻ 156 (q10 c4) ∷
   rw⁻ 155 (q9 c4) ∷
   rw⁻ 154 (q12 c4) ∷
   rw⁻ 153 (q13 c4) ∷
   rw⁻ 152 (q13 c4) ∷
   rw⁻ 151 (q12 c4) ∷
   rw⁻ 150 (q11 c4) ∷
   rw⁻ 149 (q11 c4) ∷
   rw⁻ 148 (q11 c4) ∷
   rw⁻ 147 (q9 c4) ∷
   rw⁻ 146 (q12 c4) ∷
   rw⁻ 145 (q13 c4) ∷
   rw⁻ 144 (q13 c4) ∷
   rw⁻ 143 (q12 c4) ∷
   rw⁻ 142 (q11 c4) ∷
   rw⁻ 141 (q8 c4) ∷
   rw 193 (q14 c4) ∷
   rw⁻ 198 (q15 c4) ∷
   rw⁻ 197 (q16 c4) ∷
   rw⁻ 199 (q17 c4) ∷
   rw 198 (q18 c4) ∷
   rw⁻ 200 (q19 c4) ∷
   re 199 1 (ℓ "乥乇乥") ∷
   rw 201 (q19 c4) ∷
   rw⁻ 201 (q20 c4) ∷
   rw 200 (q21 c4) ∷
   rw⁻ 202 (q19 c4) ∷
   rw⁻ 201 (q19 c4) ∷
   re 202 3 (ℓ "乎") ∷
   rw⁻ 203 (q17 c4) ∷
   rw 202 (q22 c4) ∷
   rw⁻ 204 (q15 c4) ∷
   rw⁻ 203 (q16 c4) ∷
   rw⁻ 204 (q23 c4) ∷
   rw 203 (q24 c4) ∷
   rw 204 (q25 c4) ∷
   rw 205 (q24 c4) ∷
   rw 206 (q25 c4) ∷
   rw 207 (q15 c4) ∷
   rw 202 (q26 c4) ∷
   rw 203 (q27 c4) ∷
   rw 204 (q26 c4) ∷
   rw 205 (q27 c4) ∷
   rw 206 (q17 c4) ∷
   rw 201 (q28 c4) ∷
   rw 202 (q29 c4) ∷
   rw 203 (q28 c4) ∷
   rw 204 (q29 c4) ∷
   rw 205 (q19 c4) ∷
   rw 200 (q30 c4) ∷ []) Eq.refl
