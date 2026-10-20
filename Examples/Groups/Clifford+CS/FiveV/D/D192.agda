{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D192 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-6ab04641)
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-F4-I-I ; lem-F4-I-K3 ; lem-F4-I-S2 ; lem-F4-I-S3 ; lem-F4-K3-I ; lem-F4-K3-K3 ; lem-F4-K3-S2 ; lem-F4-K3-S3 ; lem-F4-S2-I ; lem-F4-S2-K3 ; lem-F4-S2-S2 ; lem-F4-S2-S3)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S2 ; lem-F4-CS2-S3 ; lem-F4-I-CS2 ; lem-F4-S2-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1 ; lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F2-K1-CS2 ; lem-F4-CS2-K3 ; lem-F4-K3-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1 ; lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D147 using (lem-deb-P-lo-eps)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-TR2-6ab04641 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) [] (lem-deb-P-lo-eps c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-CS2 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS2 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K3 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S2 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S2 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-I c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-I c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4)

-- deb-P-lo part0: 248 steps
lem-deb-P-lo-part0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-P-lo-part0 c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q4 c4) ∷
   rw 74 (q5 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q6 c4) ∷
   rw 65 (q6 c4) ∷
   rw 62 (q4 c4) ∷
   rw 59 (q7 c4) ∷
   rw 56 (q4 c4) ∷
   rw 53 (q7 c4) ∷
   rw 50 (q4 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q4 c4) ∷
   rw 75 (q5 c4) ∷
   rw 72 (q6 c4) ∷
   rw 69 (q6 c4) ∷
   rw 66 (q6 c4) ∷
   rw 63 (q4 c4) ∷
   rw 60 (q7 c4) ∷
   rw 57 (q4 c4) ∷
   rw 54 (q7 c4) ∷
   rw 51 (q4 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q4 c4) ∷
   rw 76 (q5 c4) ∷
   rw 73 (q6 c4) ∷
   rw 70 (q6 c4) ∷
   rw 67 (q6 c4) ∷
   rw 64 (q4 c4) ∷
   rw 61 (q7 c4) ∷
   rw 58 (q4 c4) ∷
   rw 55 (q7 c4) ∷
   rw 52 (q4 c4) ∷
   rw 83 (q4 c4) ∷
   rw 80 (q4 c4) ∷
   rw 77 (q5 c4) ∷
   rw 74 (q6 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q6 c4) ∷
   rw 65 (q4 c4) ∷
   rw 62 (q7 c4) ∷
   rw 59 (q4 c4) ∷
   rw 56 (q7 c4) ∷
   rw 53 (q4 c4) ∷
   rw 84 (q4 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q5 c4) ∷
   rw 75 (q6 c4) ∷
   rw 72 (q6 c4) ∷
   rw 69 (q6 c4) ∷
   rw 66 (q4 c4) ∷
   rw 63 (q7 c4) ∷
   rw 60 (q4 c4) ∷
   rw 57 (q7 c4) ∷
   rw 54 (q4 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q5 c4) ∷
   rw 76 (q6 c4) ∷
   rw 73 (q6 c4) ∷
   rw 70 (q6 c4) ∷
   rw 67 (q4 c4) ∷
   rw 64 (q7 c4) ∷
   rw 61 (q4 c4) ∷
   rw 58 (q7 c4) ∷
   rw 55 (q4 c4) ∷
   rw 86 (q4 c4) ∷
   rw 83 (q4 c4) ∷
   rw 80 (q5 c4) ∷
   rw 77 (q6 c4) ∷
   rw 74 (q6 c4) ∷
   rw 71 (q6 c4) ∷
   rw 68 (q4 c4) ∷
   rw 65 (q7 c4) ∷
   rw 62 (q4 c4) ∷
   rw 59 (q7 c4) ∷
   rw 56 (q4 c4) ∷
   rw 87 (q8 c4) ∷
   rw 84 (q8 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q10 c4) ∷
   rw 75 (q10 c4) ∷
   rw 72 (q10 c4) ∷
   rw 69 (q8 c4) ∷
   rw 66 (q11 c4) ∷
   rw 63 (q8 c4) ∷
   rw 60 (q11 c4) ∷
   rw 57 (q8 c4) ∷
   rw 88 (q4 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q5 c4) ∷
   rw 79 (q6 c4) ∷
   rw 76 (q6 c4) ∷
   rw 73 (q6 c4) ∷
   rw 70 (q4 c4) ∷
   rw 67 (q7 c4) ∷
   rw 64 (q4 c4) ∷
   rw 61 (q7 c4) ∷
   rw 58 (q4 c4) ∷
   rw 89 (q8 c4) ∷
   rw 86 (q8 c4) ∷
   rw 83 (q9 c4) ∷
   rw 80 (q10 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q10 c4) ∷
   rw 71 (q8 c4) ∷
   rw 68 (q11 c4) ∷
   rw 65 (q8 c4) ∷
   rw 62 (q11 c4) ∷
   rw 59 (q8 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q5 c4) ∷
   rw 81 (q6 c4) ∷
   rw 78 (q6 c4) ∷
   rw 75 (q6 c4) ∷
   rw 72 (q4 c4) ∷
   rw 69 (q7 c4) ∷
   rw 66 (q4 c4) ∷
   rw 63 (q7 c4) ∷
   rw 60 (q4 c4) ∷
   rw 91 (q12 c4) ∷
   rw 88 (q12 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q14 c4) ∷
   rw 73 (q12 c4) ∷
   rw 70 (q15 c4) ∷
   rw 67 (q12 c4) ∷
   rw 64 (q15 c4) ∷
   rw 61 (q12 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q12 c4) ∷
   rw 86 (q13 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q14 c4) ∷
   rw 74 (q12 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q12 c4) ∷
   rw 65 (q15 c4) ∷
   rw 62 (q12 c4) ∷
   rw 93 (q12 c4) ∷
   rw 90 (q12 c4) ∷
   rw 87 (q13 c4) ∷
   rw 84 (q14 c4) ∷
   rw 81 (q14 c4) ∷
   rw 78 (q14 c4) ∷
   rw 75 (q12 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q12 c4) ∷
   rw 66 (q15 c4) ∷
   rw 63 (q12 c4) ∷
   rw 94 (q16 c4) ∷
   rw 91 (q16 c4) ∷
   rw 88 (q17 c4) ∷
   rw 85 (q18 c4) ∷
   rw 82 (q18 c4) ∷
   rw 79 (q18 c4) ∷
   rw 76 (q16 c4) ∷
   rw 73 (q19 c4) ∷
   rw 70 (q16 c4) ∷
   rw 67 (q19 c4) ∷
   rw 64 (q16 c4) ∷
   rw 95 (q12 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q13 c4) ∷
   rw 86 (q14 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q12 c4) ∷
   rw 68 (q15 c4) ∷
   rw 65 (q12 c4) ∷
   rw 96 (q20 c4) ∷
   rw 93 (q20 c4) ∷
   rw 90 (q21 c4) ∷
   rw 87 (q22 c4) ∷
   rw 84 (q22 c4) ∷
   rw 81 (q22 c4) ∷
   rw 78 (q20 c4) ∷
   rw 75 (q23 c4) ∷
   rw 72 (q20 c4) ∷
   rw 69 (q23 c4) ∷
   rw 66 (q20 c4) ∷
   rw 97 (q20 c4) ∷
   rw 94 (q20 c4) ∷
   rw 91 (q21 c4) ∷
   rw 88 (q22 c4) ∷
   rw 85 (q22 c4) ∷
   rw 82 (q22 c4) ∷
   rw 79 (q20 c4) ∷
   rw 76 (q23 c4) ∷
   rw 73 (q20 c4) ∷
   rw 70 (q23 c4) ∷
   rw 67 (q20 c4) ∷
   rw 98 (q20 c4) ∷
   rw 95 (q20 c4) ∷
   rw 92 (q21 c4) ∷
   rw 89 (q22 c4) ∷
   rw 86 (q22 c4) ∷
   rw 83 (q22 c4) ∷
   rw 80 (q20 c4) ∷
   rw 77 (q23 c4) ∷
   rw 74 (q20 c4) ∷
   rw 71 (q23 c4) ∷
   rw 68 (q20 c4) ∷
   rw 99 (q20 c4) ∷
   rw 96 (q20 c4) ∷
   rw 93 (q21 c4) ∷
   rw 90 (q22 c4) ∷
   rw 87 (q22 c4) ∷
   rw 84 (q22 c4) ∷
   rw 81 (q20 c4) ∷
   rw 78 (q23 c4) ∷
   rw 75 (q20 c4) ∷
   rw 72 (q23 c4) ∷
   rw 69 (q20 c4) ∷
   rw 100 (q20 c4) ∷
   rw 97 (q20 c4) ∷
   rw 94 (q21 c4) ∷
   rw 91 (q22 c4) ∷
   rw 88 (q22 c4) ∷
   rw 85 (q22 c4) ∷
   rw 82 (q20 c4) ∷
   rw 79 (q23 c4) ∷
   rw 76 (q20 c4) ∷
   rw 73 (q23 c4) ∷
   rw 70 (q20 c4) ∷
   rw 101 (q20 c4) ∷
   rw 98 (q20 c4) ∷
   rw 95 (q21 c4) ∷
   rw 92 (q22 c4) ∷
   rw 89 (q22 c4) ∷
   rw 86 (q22 c4) ∷
   rw 83 (q20 c4) ∷
   rw 80 (q23 c4) ∷
   rw 77 (q20 c4) ∷
   rw 74 (q23 c4) ∷
   rw 71 (q20 c4) ∷
   rw 102 (q20 c4) ∷
   rw 99 (q20 c4) ∷
   rw 96 (q21 c4) ∷ []) Eq.refl
