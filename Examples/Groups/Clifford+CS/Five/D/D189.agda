{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D189 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0004 ; wl0003 ; wl0928)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-570a2ddc)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-K2 ; lem-F4-I-S2 ; lem-F4-I-S3 ; lem-F4-K2-I ; lem-F4-K2-K2 ; lem-F4-K2-S2 ; lem-F4-K2-S3 ; lem-F4-S3-I ; lem-F4-S3-K2 ; lem-F4-S3-S2 ; lem-F4-S3-S3 ; lem-nat-S ; lem-nat-S-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2 ; lem-nat-S-at01143043)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S2 ; lem-F4-CS2-S3 ; lem-F4-I-CS2 ; lem-F4-K2-CS2 ; lem-F4-S3-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-F4-CS2-K2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1 ; lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1 ; lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.Five.D.D147 using (lem-SW-S ; lem-SW-S-at01143043 ; lem-SW-S-at14213243 ; lem-deb-P-hi-eps)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ Sw34 ∷ []) (lem-SW-S c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw34 ∷ Sb3-0-12-4 ∷ Sw34 ∷ []) (Sb4-0-12-3 ∷ []) (lem-nat-S c4)

-- F0: 3 steps
lem-F0 : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-12-3 ∷ []) ⟫ʷ
lem-F0 c4 = derive (Sb3-0-12-4 ∷ []) (Sb4-0-12-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-SW-S-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ []) (lem-nat-S-at14213243 c4)

-- F0 @14213243: 3 steps
lem-F0-at14213243 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = derive (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw03 ∷ Sw03 ∷ []) [] (wl0928 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw03 ∷ []) (lem-SW-S-at01143043 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) (Sb3-1-42-0 ∷ []) (lem-nat-S-at01143043 c4)

-- F0 @01143043: 3 steps
lem-F0-at01143043 : Ws → ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F0-at01143043 c4 = derive (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-570a2ddc c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) [] (lem-deb-P-hi-eps c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-CS2 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-K2 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-K2 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S3 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S3 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-I c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-I c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3-S2 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2-S2 c4)

-- deb-P-hi part0: 248 steps
lem-deb-P-hi-part0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-hi-part0 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 80 (q13 c4) ∷
   rw 77 (q13 c4) ∷
   rw 74 (q14 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q15 c4) ∷
   rw 65 (q15 c4) ∷
   rw 62 (q13 c4) ∷
   rw 59 (q16 c4) ∷
   rw 56 (q13 c4) ∷
   rw 53 (q16 c4) ∷
   rw 50 (q13 c4) ∷
   rw 81 (q13 c4) ∷
   rw 78 (q13 c4) ∷
   rw 75 (q14 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q15 c4) ∷
   rw 66 (q15 c4) ∷
   rw 63 (q13 c4) ∷
   rw 60 (q16 c4) ∷
   rw 57 (q13 c4) ∷
   rw 54 (q16 c4) ∷
   rw 51 (q13 c4) ∷
   rw 82 (q13 c4) ∷
   rw 79 (q13 c4) ∷
   rw 76 (q14 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q15 c4) ∷
   rw 67 (q15 c4) ∷
   rw 64 (q13 c4) ∷
   rw 61 (q16 c4) ∷
   rw 58 (q13 c4) ∷
   rw 55 (q16 c4) ∷
   rw 52 (q13 c4) ∷
   rw 83 (q13 c4) ∷
   rw 80 (q13 c4) ∷
   rw 77 (q14 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q15 c4) ∷
   rw 65 (q13 c4) ∷
   rw 62 (q16 c4) ∷
   rw 59 (q13 c4) ∷
   rw 56 (q16 c4) ∷
   rw 53 (q13 c4) ∷
   rw 84 (q13 c4) ∷
   rw 81 (q13 c4) ∷
   rw 78 (q14 c4) ∷
   rw 75 (q15 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q15 c4) ∷
   rw 66 (q13 c4) ∷
   rw 63 (q16 c4) ∷
   rw 60 (q13 c4) ∷
   rw 57 (q16 c4) ∷
   rw 54 (q13 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q13 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q15 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q15 c4) ∷
   rw 67 (q13 c4) ∷
   rw 64 (q16 c4) ∷
   rw 61 (q13 c4) ∷
   rw 58 (q16 c4) ∷
   rw 55 (q13 c4) ∷
   rw 86 (q13 c4) ∷
   rw 83 (q13 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q15 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q15 c4) ∷
   rw 68 (q13 c4) ∷
   rw 65 (q16 c4) ∷
   rw 62 (q13 c4) ∷
   rw 59 (q16 c4) ∷
   rw 56 (q13 c4) ∷
   rw 87 (q17 c4) ∷
   rw 84 (q17 c4) ∷
   rw 81 (q18 c4) ∷
   rw 78 (q19 c4) ∷
   rw 75 (q19 c4) ∷
   rw 72 (q19 c4) ∷
   rw 69 (q17 c4) ∷
   rw 66 (q20 c4) ∷
   rw 63 (q17 c4) ∷
   rw 60 (q20 c4) ∷
   rw 57 (q17 c4) ∷
   rw 88 (q13 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q15 c4) ∷
   rw 76 (q15 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q13 c4) ∷
   rw 67 (q16 c4) ∷
   rw 64 (q13 c4) ∷
   rw 61 (q16 c4) ∷
   rw 58 (q13 c4) ∷
   rw 89 (q17 c4) ∷
   rw 86 (q17 c4) ∷
   rw 83 (q18 c4) ∷
   rw 80 (q19 c4) ∷
   rw 77 (q19 c4) ∷
   rw 74 (q19 c4) ∷
   rw 71 (q17 c4) ∷
   rw 68 (q20 c4) ∷
   rw 65 (q17 c4) ∷
   rw 62 (q20 c4) ∷
   rw 59 (q17 c4) ∷
   rw 90 (q13 c4) ∷
   rw 87 (q13 c4) ∷
   rw 84 (q14 c4) ∷
   rw 81 (q15 c4) ∷
   rw 78 (q15 c4) ∷
   rw 75 (q15 c4) ∷
   rw 72 (q13 c4) ∷
   rw 69 (q16 c4) ∷
   rw 66 (q13 c4) ∷
   rw 63 (q16 c4) ∷
   rw 60 (q13 c4) ∷
   rw 91 (q21 c4) ∷
   rw 88 (q21 c4) ∷
   rw 85 (q22 c4) ∷
   rw 82 (q23 c4) ∷
   rw 79 (q23 c4) ∷
   rw 76 (q23 c4) ∷
   rw 73 (q21 c4) ∷
   rw 70 (q24 c4) ∷
   rw 67 (q21 c4) ∷
   rw 64 (q24 c4) ∷
   rw 61 (q21 c4) ∷
   rw 92 (q21 c4) ∷
   rw 89 (q21 c4) ∷
   rw 86 (q22 c4) ∷
   rw 83 (q23 c4) ∷
   rw 80 (q23 c4) ∷
   rw 77 (q23 c4) ∷
   rw 74 (q21 c4) ∷
   rw 71 (q24 c4) ∷
   rw 68 (q21 c4) ∷
   rw 65 (q24 c4) ∷
   rw 62 (q21 c4) ∷
   rw 93 (q21 c4) ∷
   rw 90 (q21 c4) ∷
   rw 87 (q22 c4) ∷
   rw 84 (q23 c4) ∷
   rw 81 (q23 c4) ∷
   rw 78 (q23 c4) ∷
   rw 75 (q21 c4) ∷
   rw 72 (q24 c4) ∷
   rw 69 (q21 c4) ∷
   rw 66 (q24 c4) ∷
   rw 63 (q21 c4) ∷
   rw 94 (q25 c4) ∷
   rw 91 (q25 c4) ∷
   rw 88 (q26 c4) ∷
   rw 85 (q27 c4) ∷
   rw 82 (q27 c4) ∷
   rw 79 (q27 c4) ∷
   rw 76 (q25 c4) ∷
   rw 73 (q28 c4) ∷
   rw 70 (q25 c4) ∷
   rw 67 (q28 c4) ∷
   rw 64 (q25 c4) ∷
   rw 95 (q21 c4) ∷
   rw 92 (q21 c4) ∷
   rw 89 (q22 c4) ∷
   rw 86 (q23 c4) ∷
   rw 83 (q23 c4) ∷
   rw 80 (q23 c4) ∷
   rw 77 (q21 c4) ∷
   rw 74 (q24 c4) ∷
   rw 71 (q21 c4) ∷
   rw 68 (q24 c4) ∷
   rw 65 (q21 c4) ∷
   rw 96 (q29 c4) ∷
   rw 93 (q29 c4) ∷
   rw 90 (q30 c4) ∷
   rw 87 (q31 c4) ∷
   rw 84 (q31 c4) ∷
   rw 81 (q31 c4) ∷
   rw 78 (q29 c4) ∷
   rw 75 (q32 c4) ∷
   rw 72 (q29 c4) ∷
   rw 69 (q32 c4) ∷
   rw 66 (q29 c4) ∷
   rw 97 (q29 c4) ∷
   rw 94 (q29 c4) ∷
   rw 91 (q30 c4) ∷
   rw 88 (q31 c4) ∷
   rw 85 (q31 c4) ∷
   rw 82 (q31 c4) ∷
   rw 79 (q29 c4) ∷
   rw 76 (q32 c4) ∷
   rw 73 (q29 c4) ∷
   rw 70 (q32 c4) ∷
   rw 67 (q29 c4) ∷
   rw 98 (q29 c4) ∷
   rw 95 (q29 c4) ∷
   rw 92 (q30 c4) ∷
   rw 89 (q31 c4) ∷
   rw 86 (q31 c4) ∷
   rw 83 (q31 c4) ∷
   rw 80 (q29 c4) ∷
   rw 77 (q32 c4) ∷
   rw 74 (q29 c4) ∷
   rw 71 (q32 c4) ∷
   rw 68 (q29 c4) ∷
   rw 99 (q29 c4) ∷
   rw 96 (q29 c4) ∷
   rw 93 (q30 c4) ∷
   rw 90 (q31 c4) ∷
   rw 87 (q31 c4) ∷
   rw 84 (q31 c4) ∷
   rw 81 (q29 c4) ∷
   rw 78 (q32 c4) ∷
   rw 75 (q29 c4) ∷
   rw 72 (q32 c4) ∷
   rw 69 (q29 c4) ∷
   rw 100 (q29 c4) ∷
   rw 97 (q29 c4) ∷
   rw 94 (q30 c4) ∷
   rw 91 (q31 c4) ∷
   rw 88 (q31 c4) ∷
   rw 85 (q31 c4) ∷
   rw 82 (q29 c4) ∷
   rw 79 (q32 c4) ∷
   rw 76 (q29 c4) ∷
   rw 73 (q32 c4) ∷
   rw 70 (q29 c4) ∷
   rw 101 (q29 c4) ∷
   rw 98 (q29 c4) ∷
   rw 95 (q30 c4) ∷
   rw 92 (q31 c4) ∷
   rw 89 (q31 c4) ∷
   rw 86 (q31 c4) ∷
   rw 83 (q29 c4) ∷
   rw 80 (q32 c4) ∷
   rw 77 (q29 c4) ∷
   rw 74 (q32 c4) ∷
   rw 71 (q29 c4) ∷
   rw 102 (q29 c4) ∷
   rw 99 (q29 c4) ∷
   rw 96 (q30 c4) ∷ []) Eq.refl
