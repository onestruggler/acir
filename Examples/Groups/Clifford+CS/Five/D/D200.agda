{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D200 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-e425e28a)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-K3 ; lem-F4-I-S2 ; lem-F4-K3-I ; lem-F4-K3-K3 ; lem-F4-K3-S2 ; lem-F4-S2-I ; lem-F4-S2-K3 ; lem-F4-S2-S2)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S2 ; lem-F4-I-CS2 ; lem-F4-S2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1 ; lem-F4-CS2-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2 ; lem-F4-CS2-K3 ; lem-F4-K3-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1 ; lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.Five.D.D149 using (lem-deb-CKS-eps)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) (lem-TR2-e425e28a c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) [] (lem-deb-CKS-eps c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-CS2 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-CS2 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S2 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S2 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-I c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-I c4)

-- deb-CKS part0: 175 steps
lem-deb-CKS-part0 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-CKS-part0 c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw 124 (q4 c4) ∷
   rw 121 (q5 c4) ∷
   rw 118 (q5 c4) ∷
   rw 115 (q5 c4) ∷
   rw 112 (q6 c4) ∷
   rw 109 (q7 c4) ∷
   rw 106 (q6 c4) ∷
   rw 103 (q7 c4) ∷
   rw 100 (q6 c4) ∷
   rw 97 (q6 c4) ∷
   rw 94 (q4 c4) ∷
   rw 91 (q5 c4) ∷
   rw 88 (q5 c4) ∷
   rw 85 (q5 c4) ∷
   rw 82 (q6 c4) ∷
   rw 79 (q7 c4) ∷
   rw 76 (q6 c4) ∷
   rw 73 (q7 c4) ∷
   rw 70 (q6 c4) ∷
   rw 125 (q8 c4) ∷
   rw 122 (q9 c4) ∷
   rw 119 (q9 c4) ∷
   rw 116 (q9 c4) ∷
   rw 113 (q10 c4) ∷
   rw 110 (q11 c4) ∷
   rw 107 (q10 c4) ∷
   rw 104 (q11 c4) ∷
   rw 101 (q10 c4) ∷
   rw 98 (q10 c4) ∷
   rw 95 (q8 c4) ∷
   rw 92 (q9 c4) ∷
   rw 89 (q9 c4) ∷
   rw 86 (q9 c4) ∷
   rw 83 (q10 c4) ∷
   rw 80 (q11 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q11 c4) ∷
   rw 71 (q10 c4) ∷
   rw 126 (q4 c4) ∷
   rw 123 (q5 c4) ∷
   rw 120 (q5 c4) ∷
   rw 117 (q5 c4) ∷
   rw 114 (q6 c4) ∷
   rw 111 (q7 c4) ∷
   rw 108 (q6 c4) ∷
   rw 105 (q7 c4) ∷
   rw 102 (q6 c4) ∷
   rw 99 (q6 c4) ∷
   rw 96 (q4 c4) ∷
   rw 93 (q5 c4) ∷
   rw 90 (q5 c4) ∷
   rw 87 (q5 c4) ∷
   rw 84 (q6 c4) ∷
   rw 81 (q7 c4) ∷
   rw 78 (q6 c4) ∷
   rw 75 (q7 c4) ∷
   rw 72 (q6 c4) ∷
   rw 127 (q8 c4) ∷
   rw 124 (q9 c4) ∷
   rw 121 (q9 c4) ∷
   rw 118 (q9 c4) ∷
   rw 115 (q10 c4) ∷
   rw 112 (q11 c4) ∷
   rw 109 (q10 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q10 c4) ∷
   rw 100 (q10 c4) ∷
   rw 97 (q8 c4) ∷
   rw 94 (q9 c4) ∷
   rw 91 (q9 c4) ∷
   rw 88 (q9 c4) ∷
   rw 85 (q10 c4) ∷
   rw 82 (q11 c4) ∷
   rw 79 (q10 c4) ∷
   rw 76 (q11 c4) ∷
   rw 73 (q10 c4) ∷
   rw 128 (q4 c4) ∷
   rw 125 (q5 c4) ∷
   rw 122 (q5 c4) ∷
   rw 119 (q5 c4) ∷
   rw 116 (q6 c4) ∷
   rw 113 (q7 c4) ∷
   rw 110 (q6 c4) ∷
   rw 107 (q7 c4) ∷
   rw 104 (q6 c4) ∷
   rw 101 (q6 c4) ∷
   rw 98 (q4 c4) ∷
   rw 95 (q5 c4) ∷
   rw 92 (q5 c4) ∷
   rw 89 (q5 c4) ∷
   rw 86 (q6 c4) ∷
   rw 83 (q7 c4) ∷
   rw 80 (q6 c4) ∷
   rw 77 (q7 c4) ∷
   rw 74 (q6 c4) ∷
   rw 129 (q12 c4) ∷
   rw 126 (q13 c4) ∷
   rw 123 (q13 c4) ∷
   rw 120 (q13 c4) ∷
   rw 117 (q14 c4) ∷
   rw 114 (q15 c4) ∷
   rw 111 (q14 c4) ∷
   rw 108 (q15 c4) ∷
   rw 105 (q14 c4) ∷
   rw 102 (q14 c4) ∷
   rw 99 (q12 c4) ∷
   rw 96 (q13 c4) ∷
   rw 93 (q13 c4) ∷
   rw 90 (q13 c4) ∷
   rw 87 (q14 c4) ∷
   rw 84 (q15 c4) ∷
   rw 81 (q14 c4) ∷
   rw 78 (q15 c4) ∷
   rw 75 (q14 c4) ∷
   rw 130 (q12 c4) ∷
   rw 127 (q13 c4) ∷
   rw 124 (q13 c4) ∷
   rw 121 (q13 c4) ∷
   rw 118 (q14 c4) ∷
   rw 115 (q15 c4) ∷
   rw 112 (q14 c4) ∷
   rw 109 (q15 c4) ∷
   rw 106 (q14 c4) ∷
   rw 103 (q14 c4) ∷
   rw 100 (q12 c4) ∷
   rw 97 (q13 c4) ∷
   rw 94 (q13 c4) ∷
   rw 91 (q13 c4) ∷
   rw 88 (q14 c4) ∷
   rw 85 (q15 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q15 c4) ∷
   rw 76 (q14 c4) ∷
   rw 131 (q12 c4) ∷
   rw 128 (q13 c4) ∷
   rw 125 (q13 c4) ∷
   rw 122 (q13 c4) ∷
   rw 119 (q14 c4) ∷
   rw 116 (q15 c4) ∷
   rw 113 (q14 c4) ∷
   rw 110 (q15 c4) ∷
   rw 107 (q14 c4) ∷
   rw 104 (q14 c4) ∷
   rw 101 (q12 c4) ∷
   rw 98 (q13 c4) ∷
   rw 95 (q13 c4) ∷
   rw 92 (q13 c4) ∷
   rw 89 (q14 c4) ∷
   rw 86 (q15 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q15 c4) ∷
   rw 77 (q14 c4) ∷
   rw 132 (q16 c4) ∷
   rw 129 (q17 c4) ∷
   rw 126 (q17 c4) ∷
   rw 123 (q17 c4) ∷
   rw 120 (q18 c4) ∷
   rw 117 (q19 c4) ∷
   rw 114 (q18 c4) ∷
   rw 111 (q19 c4) ∷
   rw 108 (q18 c4) ∷
   rw 105 (q18 c4) ∷
   rw 102 (q16 c4) ∷
   rw 99 (q17 c4) ∷
   rw 96 (q17 c4) ∷
   rw 93 (q17 c4) ∷
   rw 90 (q18 c4) ∷
   rw 87 (q19 c4) ∷
   rw 84 (q18 c4) ∷
   rw 81 (q19 c4) ∷
   rw 78 (q18 c4) ∷
   rw 133 (q12 c4) ∷ []) Eq.refl
