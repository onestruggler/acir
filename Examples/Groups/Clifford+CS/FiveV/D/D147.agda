{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D147 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-0d166c34 ; lem-TR2-4726ca8d)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D018 using (lem-CXAu-S)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-CXAu-S-at14213243 ; lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-CXAu-S-at01143043 ; lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D031 using (lem-L-CCZ-1-part2)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D045 using (lem-L-CCZ-1-part1 ; lem-L-CCZ-1-part3)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-CXuA-S ; lem-CXuA-S-at14213243 ; lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-CXuA-S-at01143043 ; lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D071 using (lem-L-CCZ-1-part0)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-push-CK40-sw1-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ []) (wl 547 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CX34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ CX34 ∷ []) (lem-CXuA-S c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CX43 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ CX43 ∷ []) (lem-CXAu-S c4)

-- SW-S: 5 steps
lem-SW-S : Ws → ⟪ (Sw34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-SW-S c4 = derive (Sw34 ∷ Sb3-0-12-4 ∷ []) (Sb3-0-12-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = eqn (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) (wl 258 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CX23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CX23 ∷ []) (lem-CXuA-S-at14213243 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CX32 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CX32 ∷ []) (lem-CXAu-S-at14213243 c4)

-- SW-S @14213243: 5 steps
lem-SW-S-at14213243 : Ws → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at14213243 c4 = derive (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q4 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CX03 ∷ CX30 ∷ CX03 ∷ []) (Sw03 ∷ []) (wl 961 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CX03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CX03 ∷ []) (lem-CXuA-S-at01143043 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CX30 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CX30 ∷ []) (lem-CXAu-S-at01143043 c4)

-- SW-S @01143043: 5 steps
lem-SW-S-at01143043 : Ws → ⟪ (Sw03 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw03 ∷ []) ⟫ʷ
lem-SW-S-at01143043 c4 = derive (Sw03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw03 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q7 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ []) (lem-L-CCZ-1-part0 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (lem-L-CCZ-1-part1 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (lem-L-CCZ-1-part2 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (Bx0-1234 ∷ []) (lem-L-CCZ-1-part3 c4)

-- L-CCZ-1: 4 steps
lem-L-CCZ-1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-L-CCZ-1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl 1083 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) [] (lem-TR2-0d166c34 c4)

-- deb-P-hi-eps: 28 steps
lem-deb-P-hi-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q25 : Ws → Eqn
  q25 c4 = eqn (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl 99 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q33 : Ws → Eqn
  q33 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))

-- deb-P-hi-eps @02132031: 144 steps
lem-deb-P-hi-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 24 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   rw 22 (q19 c4) ∷
   rw 21 (q17 c4) ∷
   rw 20 (q20 c4) ∷
   rw 19 (q17 c4) ∷
   rw 18 (q20 c4) ∷
   rw 17 (q17 c4) ∷
   rw 16 (q19 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 14 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   rw 12 (q19 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q20 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q20 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q17 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q17 c4) ∷
   rw 2 (q17 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw 28 (q22 c4) ∷
   rw 27 (q22 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw 22 (q22 c4) ∷
   rw 21 (q25 c4) ∷
   rw 20 (q22 c4) ∷
   rw 19 (q25 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw 12 (q22 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q22 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q22 c4) ∷
   rw 3 (q22 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw 29 (q27 c4) ∷
   rw 28 (q27 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw 26 (q29 c4) ∷
   rw 25 (q29 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q27 c4) ∷
   rw 22 (q30 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q30 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q29 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 16 (q29 c4) ∷
   rw 15 (q29 c4) ∷
   rw 14 (q29 c4) ∷
   rw 13 (q27 c4) ∷
   rw 12 (q30 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw 30 (q31 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw⁻ 27 (q32 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw 23 (q33 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q33 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 14 (q31 c4) ∷
   rw 13 (q33 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

-- deb-P-hi-eps @132132: 86 steps
lem-deb-P-hi-eps-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-hi-eps-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw⁻ 28 (q26 c4) ∷
   rw 27 (q27 c4) ∷
   rw 26 (q27 c4) ∷
   rw⁻ 25 (q28 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q29 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q30 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q30 c4) ∷
   rw 17 (q27 c4) ∷
   rw 16 (q29 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw 14 (q29 c4) ∷
   rw 13 (q29 c4) ∷
   rw 12 (q29 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q30 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw 28 (q31 c4) ∷
   rw 27 (q31 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q33 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q33 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q33 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) [] (lem-TR2-4726ca8d c4)

-- deb-P-lo-eps: 28 steps
lem-deb-P-lo-eps : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))

-- deb-P-lo-eps @02132031: 144 steps
lem-deb-P-lo-eps-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-deb-P-lo-eps-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) []
  (rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q14 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q14 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q14 c4) ∷
   rw 25 (q14 c4) ∷
   rw 26 (q14 c4) ∷
   rw 27 (q14 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw 27 (q17 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q18 c4) ∷
   rw 24 (q35 c4) ∷
   rw 23 (q35 c4) ∷
   rw 22 (q35 c4) ∷
   rw 21 (q17 c4) ∷
   rw 20 (q33 c4) ∷
   rw 19 (q17 c4) ∷
   rw 18 (q33 c4) ∷
   rw 17 (q17 c4) ∷
   rw 16 (q35 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 14 (q35 c4) ∷
   rw 13 (q35 c4) ∷
   rw 12 (q35 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q33 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q33 c4) ∷
   rw 7 (q17 c4) ∷
   rw 6 (q17 c4) ∷
   rw 5 (q17 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q17 c4) ∷
   rw 2 (q17 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw 28 (q22 c4) ∷
   rw 27 (q22 c4) ∷
   rw⁻ 26 (q23 c4) ∷
   rw 25 (q36 c4) ∷
   rw 24 (q36 c4) ∷
   rw 23 (q36 c4) ∷
   rw 22 (q22 c4) ∷
   rw⁻ 21 (q37 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q37 c4) ∷
   rw 18 (q22 c4) ∷
   rw 17 (q36 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 15 (q36 c4) ∷
   rw 14 (q36 c4) ∷
   rw 13 (q36 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 11 (q37 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 8 (q22 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q22 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q22 c4) ∷
   rw 3 (q22 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 30 (q26 c4) ∷
   rw 29 (q27 c4) ∷
   rw 28 (q27 c4) ∷
   rw⁻ 27 (q28 c4) ∷
   rw 26 (q38 c4) ∷
   rw 25 (q38 c4) ∷
   rw 24 (q38 c4) ∷
   rw 23 (q27 c4) ∷
   rw 22 (q39 c4) ∷
   rw 21 (q27 c4) ∷
   rw 20 (q39 c4) ∷
   rw 19 (q27 c4) ∷
   rw 18 (q38 c4) ∷
   rw⁻ 17 (q28 c4) ∷
   rw 16 (q38 c4) ∷
   rw 15 (q38 c4) ∷
   rw 14 (q38 c4) ∷
   rw 13 (q27 c4) ∷
   rw 12 (q39 c4) ∷
   rw 11 (q27 c4) ∷
   rw 10 (q39 c4) ∷
   rw 9 (q27 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw 30 (q31 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 28 (q18 c4) ∷
   rw 27 (q19 c4) ∷
   rw 26 (q19 c4) ∷
   rw 25 (q19 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q40 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 21 (q40 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q19 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 17 (q19 c4) ∷
   rw 16 (q19 c4) ∷
   rw 15 (q19 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 11 (q40 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q31 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q16 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q21 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl
