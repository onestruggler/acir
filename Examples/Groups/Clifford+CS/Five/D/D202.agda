{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D202 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0283 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0892 ; wl0893 ; wl0895 ; wl0896 ; wl0897 ; wl0898 ; wl0899 ; wl0930 ; wl0931 ; wl0932 ; wl0933 ; wl0934 ; wl0935 ; wl0936 ; wl0937 ; wl0938 ; wl0939 ; wl0940 ; wl0941 ; wl0942 ; wl0943 ; wl0944 ; wl0945 ; wl0946 ; wl0947 ; wl0948 ; wl0949 ; wl0950 ; wl0951 ; wl0952 ; wl0953 ; wl0954 ; wl0955 ; wl0956 ; wl0957 ; wl0958 ; wl0959 ; wl0960 ; wl0961 ; wl0962 ; wl0963 ; wl0964 ; wl0965 ; wl0966 ; wl0967 ; wl0968 ; wl0969 ; wl0970 ; wl0971 ; wl0972 ; wl0973 ; wl0974 ; wp0461 ; wp0465 ; wp0502 ; wp0503 ; wp0504 ; wp0505 ; wp0506 ; wp0507 ; wp0508 ; wp0509 ; wp0510 ; wp0511 ; wp0512 ; wp0513 ; wp0514 ; wp0515 ; wp0516 ; wp0517)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1 ; lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-K1ᵖ0∣CS23ᵖ1 ; lem-F4-K2ᵖ0∣CS01ᵖ1 ; lem-F4-K2ᵖ0∣CS12ᵖ1 ; lem-F4-K2ᵖ0∣CS23ᵖ1 ; lem-F4-K3ᵖ0∣CS01ᵖ1 ; lem-F4-K3ᵖ0∣CS12ᵖ1 ; lem-F4-K3ᵖ0∣CS23ᵖ1 ; lem-F4-S1ᵖ0∣CS01ᵖ1 ; lem-F4-S1ᵖ0∣CS12ᵖ1 ; lem-F4-S1ᵖ0∣CS23ᵖ1 ; lem-F4-S2ᵖ0∣CS01ᵖ1 ; lem-F4-S2ᵖ0∣CS12ᵖ1 ; lem-F4-S2ᵖ0∣CS23ᵖ1 ; lem-F4-S3ᵖ0∣CS01ᵖ1 ; lem-F4-S3ᵖ0∣CS12ᵖ1 ; lem-F4-S3ᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K0ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣K2ᵖ1 ; lem-F4-CS01ᵖ0∣K3ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1 ; lem-F4-CS01ᵖ0∣S1ᵖ1 ; lem-F4-CS01ᵖ0∣S2ᵖ1 ; lem-F4-CS01ᵖ0∣S3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D175 using (lem-F4-CS01ᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS01ᵖ0∣CS23ᵖ1 ; lem-F4-CS12ᵖ0∣S0ᵖ1 ; lem-F4-CS12ᵖ0∣S1ᵖ1 ; lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣S3ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K0ᵖ1 ; lem-F4-CS12ᵖ0∣K1ᵖ1 ; lem-F4-CS12ᵖ0∣K2ᵖ1 ; lem-F4-CS12ᵖ0∣K3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS01ᵖ1 ; lem-F4-CS12ᵖ0∣CS12ᵖ1 ; lem-F5-CS12)
open import Examples.Groups.Clifford+CS.Five.D.D180 using (lem-F4-CS12ᵖ0∣CS23ᵖ1 ; lem-F4-CS23ᵖ0∣K0ᵖ1 ; lem-F4-CS23ᵖ0∣S0ᵖ1 ; lem-F4-CS23ᵖ0∣S1ᵖ1 ; lem-F4-CS23ᵖ0∣S2ᵖ1 ; lem-F4-CS23ᵖ0∣S3ᵖ1 ; lem-F4-CS23ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-F4-CS23ᵖ0∣K1ᵖ1 ; lem-F4-CS23ᵖ0∣K2ᵖ1 ; lem-F4-CS23ᵖ0∣K3ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D183 using (lem-F4-CS23ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D184 using (lem-F4-CS23ᵖ0∣CS12ᵖ1 ; lem-F4-CS23ᵖ0∣CS23ᵖ1 ; lem-F5-CS23)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (wp0502 c4)

-- calc F4 S1 S0: 1 steps
lem-calc-F4-S1-S0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S0 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q2 : Ws → Eqn
  q2 c4 = eqn (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (wp0503 c4)

-- calc F4 S1 K0: 1 steps
lem-calc-F4-S1-K0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K0 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = eqn (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl0930 (lit c4))

-- calc F4 S1 S1: 1 steps
lem-calc-F4-S1-S1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q3 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = eqn (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (wl0931 (lit c4))

-- calc F4 S1 K1: 1 steps
lem-calc-F4-S1-K1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K1 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (wl0932 (lit c4))

-- calc F4 S1 S2: 1 steps
lem-calc-F4-S1-S2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S2 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q5 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = eqn (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (wl0933 (lit c4))

-- calc F4 S1 K2: 1 steps
lem-calc-F4-S1-K2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K2 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (wl0934 (lit c4))

-- calc F4 S1 S3: 1 steps
lem-calc-F4-S1-S3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S3 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q7 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = eqn (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (wl0935 (lit c4))

-- calc F4 S1 K3: 1 steps
lem-calc-F4-S1-K3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K3 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw⁻ 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S1ᵖ0∣CS01ᵖ1 c4)

-- calc F4 S1 CS01: 1 steps
lem-calc-F4-S1-CS01 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-CS01 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw 0 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S1ᵖ0∣CS12ᵖ1 c4)

-- calc F4 S1 CS12: 1 steps
lem-calc-F4-S1-CS12 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-CS12 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw 0 (q10 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S1ᵖ0∣CS23ᵖ1 c4)

-- calc F4 S1 CS23: 1 steps
lem-calc-F4-S1-CS23 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-CS23 c4 = derive (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  (rw 0 (q11 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))

-- calc F4 K1 I: 1 steps
lem-calc-F4-K1-I : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-I c4 = derive (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4)

-- calc F4 K1 S0: 1 steps
lem-calc-F4-K1-S0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S0 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (wp0504 c4)

-- calc F4 K1 K0: 1 steps
lem-calc-F4-K1-K0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K0 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = eqn (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4))

-- calc F4 K1 S1: 1 steps
lem-calc-F4-K1-S1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q15 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))

-- calc F4 K1 K1: 1 steps
lem-calc-F4-K1-K1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4))

-- calc F4 K1 S2: 1 steps
lem-calc-F4-K1-S2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S2 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (wl0936 (lit c4))

-- calc F4 K1 K2: 1 steps
lem-calc-F4-K1-K2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K2 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (wl0937 (lit c4))

-- calc F4 K1 S3: 1 steps
lem-calc-F4-K1-S3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S3 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = eqn (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (wl0938 (lit c4))

-- calc F4 K1 K3: 1 steps
lem-calc-F4-K1-K3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K3 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)

-- calc F4 K1 CS01: 1 steps
lem-calc-F4-K1-CS01 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-CS01 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw 0 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)

-- calc F4 K1 CS12: 1 steps
lem-calc-F4-K1-CS12 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-CS12 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS23ᵖ1 c4)

-- calc F4 K1 CS23: 1 steps
lem-calc-F4-K1-CS23 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-CS23 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (rw 0 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4))

-- calc F4 S2 I: 1 steps
lem-calc-F4-S2-I : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-I c4 = derive (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (wp0505 c4)

-- calc F4 S2 S0: 1 steps
lem-calc-F4-S2-S0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S0 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q25 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (wp0506 c4)

-- calc F4 S2 K0: 1 steps
lem-calc-F4-S2-K0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K0 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (wl0898 (lit c4))

-- calc F4 S2 S1: 1 steps
lem-calc-F4-S2-S1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = eqn (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (wl0899 (lit c4))

-- calc F4 S2 K1: 1 steps
lem-calc-F4-S2-K1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K1 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4))

-- calc F4 S2 S2: 1 steps
lem-calc-F4-S2-S2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S2 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (wl0939 (lit c4))

-- calc F4 S2 K2: 1 steps
lem-calc-F4-S2-K2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K2 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = eqn (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (wl0940 (lit c4))

-- calc F4 S2 S3: 1 steps
lem-calc-F4-S2-S3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S3 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (wl0941 (lit c4))

-- calc F4 S2 K3: 1 steps
lem-calc-F4-S2-K3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K3 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw⁻ 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS01ᵖ1 c4)

-- calc F4 S2 CS01: 1 steps
lem-calc-F4-S2-CS01 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-CS01 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)

-- calc F4 S2 CS12: 1 steps
lem-calc-F4-S2-CS12 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-CS12 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw 0 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS23ᵖ1 c4)

-- calc F4 S2 CS23: 1 steps
lem-calc-F4-S2-CS23 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-CS23 c4 = derive (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  (rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (wl0942 (lit c4))

-- calc F4 K2 I: 1 steps
lem-calc-F4-K2-I : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-I c4 = derive (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (wp0507 c4)

-- calc F4 K2 S0: 1 steps
lem-calc-F4-K2-S0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S0 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q37 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (wp0508 c4)

-- calc F4 K2 K0: 1 steps
lem-calc-F4-K2-K0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K0 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (wl0943 (lit c4))

-- calc F4 K2 S1: 1 steps
lem-calc-F4-K2-S1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (wl0944 (lit c4))

-- calc F4 K2 K1: 1 steps
lem-calc-F4-K2-K1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (wl0945 (lit c4))

-- calc F4 K2 S2: 1 steps
lem-calc-F4-K2-S2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S2 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl0946 (lit c4))

-- calc F4 K2 K2: 1 steps
lem-calc-F4-K2-K2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K2 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q42 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (wl0947 (lit c4))

-- calc F4 K2 S3: 1 steps
lem-calc-F4-K2-S3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S3 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (wl0948 (lit c4))

-- calc F4 K2 K3: 1 steps
lem-calc-F4-K2-K3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K3 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS01ᵖ1 c4)

-- calc F4 K2 CS01: 1 steps
lem-calc-F4-K2-CS01 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS01 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw 0 (q45 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS12ᵖ1 c4)

-- calc F4 K2 CS12: 1 steps
lem-calc-F4-K2-CS12 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS12 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS23ᵖ1 c4)

-- calc F4 K2 CS23: 1 steps
lem-calc-F4-K2-CS23 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS23 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (wl0949 (lit c4))

-- calc F4 S3 I: 1 steps
lem-calc-F4-S3-I : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-I c4 = derive (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (wp0509 c4)

-- calc F4 S3 S0: 1 steps
lem-calc-F4-S3-S0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S0 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (wp0510 c4)

-- calc F4 S3 K0: 1 steps
lem-calc-F4-S3-K0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K0 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (wl0950 (lit c4))

-- calc F4 S3 S1: 1 steps
lem-calc-F4-S3-S1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (wl0951 (lit c4))

-- calc F4 S3 K1: 1 steps
lem-calc-F4-S3-K1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K1 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (wl0952 (lit c4))

-- calc F4 S3 S2: 1 steps
lem-calc-F4-S3-S2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S2 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (wl0953 (lit c4))

-- calc F4 S3 K2: 1 steps
lem-calc-F4-S3-K2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K2 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl0954 (lit c4))

-- calc F4 S3 S3: 1 steps
lem-calc-F4-S3-S3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S3 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (wl0955 (lit c4))

-- calc F4 S3 K3: 1 steps
lem-calc-F4-S3-K3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K3 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS01ᵖ1 c4)

-- calc F4 S3 CS01: 1 steps
lem-calc-F4-S3-CS01 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS01 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS12ᵖ1 c4)

-- calc F4 S3 CS12: 1 steps
lem-calc-F4-S3-CS12 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS12 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS23ᵖ1 c4)

-- calc F4 S3 CS23: 1 steps
lem-calc-F4-S3-CS23 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS23 c4 = derive (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  (rw 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (wl0956 (lit c4))

-- calc F4 K3 I: 1 steps
lem-calc-F4-K3-I : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-I c4 = derive (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (wp0511 c4)

-- calc F4 K3 S0: 1 steps
lem-calc-F4-K3-S0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S0 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (wp0512 c4)

-- calc F4 K3 K0: 1 steps
lem-calc-F4-K3-K0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K0 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (wl0957 (lit c4))

-- calc F4 K3 S1: 1 steps
lem-calc-F4-K3-S1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (wl0958 (lit c4))

-- calc F4 K3 K1: 1 steps
lem-calc-F4-K3-K1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K1 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (wl0959 (lit c4))

-- calc F4 K3 S2: 1 steps
lem-calc-F4-K3-S2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S2 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (wl0960 (lit c4))

-- calc F4 K3 K2: 1 steps
lem-calc-F4-K3-K2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K2 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (wl0961 (lit c4))

-- calc F4 K3 S3: 1 steps
lem-calc-F4-K3-S3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S3 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl0962 (lit c4))

-- calc F4 K3 K3: 1 steps
lem-calc-F4-K3-K3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K3 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw⁻ 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS01ᵖ1 c4)

-- calc F4 K3 CS01: 1 steps
lem-calc-F4-K3-CS01 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS01 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS12ᵖ1 c4)

-- calc F4 K3 CS12: 1 steps
lem-calc-F4-K3-CS12 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS12 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS23ᵖ1 c4)

-- calc F4 K3 CS23: 1 steps
lem-calc-F4-K3-CS23 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS23 c4 = derive (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4)

-- calc F4 CS01 I: 1 steps
lem-calc-F4-CS01-I : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-I c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)

-- calc F4 CS01 S0: 1 steps
lem-calc-F4-CS01-S0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S0 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K0ᵖ1 c4)

-- calc F4 CS01 K0: 1 steps
lem-calc-F4-CS01-K0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K0 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)

-- calc F4 CS01 S1: 1 steps
lem-calc-F4-CS01-S1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)

-- calc F4 CS01 K1: 1 steps
lem-calc-F4-CS01-K1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S2ᵖ1 c4)

-- calc F4 CS01 S2: 1 steps
lem-calc-F4-CS01-S2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S2 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K2ᵖ1 c4)

-- calc F4 CS01 K2: 1 steps
lem-calc-F4-CS01-K2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K2 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S3ᵖ1 c4)

-- calc F4 CS01 S3: 1 steps
lem-calc-F4-CS01-S3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S3 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K3ᵖ1 c4)

-- calc F4 CS01 K3: 1 steps
lem-calc-F4-CS01-K3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K3 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)

-- calc F4 CS01 CS01: 1 steps
lem-calc-F4-CS01-CS01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS01 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS12ᵖ1 c4)

-- calc F4 CS01 CS12: 1 steps
lem-calc-F4-CS01-CS12 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS12 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1 c4)

-- calc F4 CS01 CS23: 1 steps
lem-calc-F4-CS01-CS23 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS23 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4)

-- calc F4 CS12 I: 1 steps
lem-calc-F4-CS12-I : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-I c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q84 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S0ᵖ1 c4)

-- calc F4 CS12 S0: 1 steps
lem-calc-F4-CS12-S0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S0 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K0ᵖ1 c4)

-- calc F4 CS12 K0: 1 steps
lem-calc-F4-CS12-K0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K0 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S1ᵖ1 c4)

-- calc F4 CS12 S1: 1 steps
lem-calc-F4-CS12-S1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)

-- calc F4 CS12 K1: 1 steps
lem-calc-F4-CS12-K1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q88 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)

-- calc F4 CS12 S2: 1 steps
lem-calc-F4-CS12-S2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S2 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q89 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K2ᵖ1 c4)

-- calc F4 CS12 K2: 1 steps
lem-calc-F4-CS12-K2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K2 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q90 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S3ᵖ1 c4)

-- calc F4 CS12 S3: 1 steps
lem-calc-F4-CS12-S3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S3 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K3ᵖ1 c4)

-- calc F4 CS12 K3: 1 steps
lem-calc-F4-CS12-K3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K3 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS01ᵖ1 c4)

-- calc F4 CS12 CS01: 1 steps
lem-calc-F4-CS12-CS01 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS01 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)

-- calc F4 CS12 CS12: 1 steps
lem-calc-F4-CS12-CS12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS12 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS23ᵖ1 c4)

-- calc F4 CS12 CS23: 1 steps
lem-calc-F4-CS12-CS23 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS23 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 0 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣iIᵖ1 c4)

-- calc F4 CS23 I: 1 steps
lem-calc-F4-CS23-I : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-I c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S0ᵖ1 c4)

-- calc F4 CS23 S0: 1 steps
lem-calc-F4-CS23-S0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S0 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K0ᵖ1 c4)

-- calc F4 CS23 K0: 1 steps
lem-calc-F4-CS23-K0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K0 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S1ᵖ1 c4)

-- calc F4 CS23 S1: 1 steps
lem-calc-F4-CS23-S1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K1ᵖ1 c4)

-- calc F4 CS23 K1: 1 steps
lem-calc-F4-CS23-K1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K1 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S2ᵖ1 c4)

-- calc F4 CS23 S2: 1 steps
lem-calc-F4-CS23-S2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S2 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q101 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K2ᵖ1 c4)

-- calc F4 CS23 K2: 1 steps
lem-calc-F4-CS23-K2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K2 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S3ᵖ1 c4)

-- calc F4 CS23 S3: 1 steps
lem-calc-F4-CS23-S3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S3 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K3ᵖ1 c4)

-- calc F4 CS23 K3: 1 steps
lem-calc-F4-CS23-K3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K3 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1 c4)

-- calc F4 CS23 CS01: 1 steps
lem-calc-F4-CS23-CS01 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS01 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q105 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS12ᵖ1 c4)

-- calc F4 CS23 CS12: 1 steps
lem-calc-F4-CS23-CS12 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS12 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS23ᵖ1 c4)

-- calc F4 CS23 CS23: 1 steps
lem-calc-F4-CS23-CS23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS23 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw 0 (q107 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl0886 (lit c4))

-- calc F5 I 0: 1 steps
lem-calc-F5-I-0 : Ws → ⟪ (ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-0 c4 = derive (ι ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  (rw⁻ 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι1 ∷ []) (wl0963 (lit c4))

-- calc F5 I 1: 1 steps
lem-calc-F5-I-1 : Ws → ⟪ (ι1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-1 c4 = derive (ι1 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  (rw⁻ 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι2 ∷ []) (wl0964 (lit c4))

-- calc F5 I 2: 1 steps
lem-calc-F5-I-2 : Ws → ⟪ (ι2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-2 c4 = derive (ι2 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  (rw⁻ 0 (q110 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι3 ∷ []) (wl0965 (lit c4))

-- calc F5 I 3: 1 steps
lem-calc-F5-I-3 : Ws → ⟪ (ι3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-3 c4 = derive (ι3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  (rw⁻ 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι4 ∷ []) (wl0966 (lit c4))

-- calc F5 I 4: 1 steps
lem-calc-F5-I-4 : Ws → ⟪ (ι4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-4 c4 = derive (ι4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  (rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4)

-- calc F5 S0: 1 steps
lem-calc-F5-S0 : Ws → ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
lem-calc-F5-S0 c4 = derive (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ [])
  (rw 0 (q113 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = eqn (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp0513 c4)

-- calc F5 K0: 1 steps
lem-calc-F5-K0 : Ws → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
lem-calc-F5-K0 c4 = derive (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ [])
  (rw 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl0967 (lit c4))

-- calc F5 S1: 1 steps
lem-calc-F5-S1 : Ws → ⟪ (S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
lem-calc-F5-S1 c4 = derive (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ [])
  (rw 0 (q115 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4))

-- calc F5 K1: 1 steps
lem-calc-F5-K1 : Ws → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
lem-calc-F5-K1 c4 = derive (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ [])
  (rw 0 (q116 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4))

-- calc F5 S2: 1 steps
lem-calc-F5-S2 : Ws → ⟪ (S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
lem-calc-F5-S2 c4 = derive (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ [])
  (rw 0 (q117 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = eqn (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl0968 (lit c4))

-- calc F5 K2: 1 steps
lem-calc-F5-K2 : Ws → ⟪ (K2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
lem-calc-F5-K2 c4 = derive (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ [])
  (rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl0969 (lit c4))

-- calc F5 S3: 1 steps
lem-calc-F5-S3 : Ws → ⟪ (S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
lem-calc-F5-S3 c4 = derive (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ [])
  (rw 0 (q119 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl0970 (lit c4))

-- calc F5 K3: 1 steps
lem-calc-F5-K3 : Ws → ⟪ (K3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
lem-calc-F5-K3 c4 = derive (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ [])
  (rw 0 (q120 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)

-- calc F5 CS01: 1 steps
lem-calc-F5-CS01 : Ws → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-calc-F5-CS01 c4 = derive (CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q121 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-CS12 c4)

-- calc F5 CS12: 1 steps
lem-calc-F5-CS12 : Ws → ⟪ (CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-calc-F5-CS12 c4 = derive (CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q122 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-CS23 c4)

-- calc F5 CS23: 1 steps
lem-calc-F5-CS23 : Ws → ⟪ (CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-calc-F5-CS23 c4 = derive (CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q123 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = eqn (CX14 ∷ []) (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) (wp0514 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)

-- f6 cx14: 2 steps
lem-f6-cx14 : Ws → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ []) ⟫ʷ
lem-f6-cx14 c4 = derive (CX14 ∷ []) (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  (rw 0 (q124 c4) ∷
   rw 4 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (wp0515 c4)

-- f6 w1: 1 steps
lem-f6-w1 : Ws → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-f6-w1 c4 = derive (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  (rw⁻ 0 (q126 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = eqn (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) (wp0516 c4)

-- f6 w2: 1 steps
lem-f6-w2 : Ws → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
lem-f6-w2 c4 = derive (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ [])
  (rw 0 (q127 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (CX14 ∷ CX14 ∷ []) [] (wl0971 (lit c4))

-- f6 aa: 1 steps
lem-f6-aa : Ws → ⟪ (CX14 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-f6-aa c4 = derive (CX14 ∷ CX14 ∷ []) []
  (rw 0 (q128 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) [] (wp0517 c4)

-- f6 ee: 1 steps
lem-f6-ee : Ws → ⟪ (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-f6-ee c4 = derive (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) []
  (rw 0 (q129 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) (CX43 ∷ []) (wl0972 (lit c4))

-- f6 cx43: 1 steps
lem-f6-cx43 : Ws → ⟪ (CX43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-f6-cx43 c4 = derive (CX43 ∷ []) (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ [])
  (rw⁻ 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (CX34 ∷ []) (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ []) (wl0973 (lit c4))

-- f6 cx34: 1 steps
lem-f6-cx34 : Ws → ⟪ (CX34 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-f6-cx34 c4 = derive (CX34 ∷ []) (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ []) (wl0974 (lit c4))

-- f6 sw34: 1 steps
lem-f6-sw34 : Ws → ⟪ (Sw34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CX43 ∷ CX34 ∷ []) ⟫ʷ
lem-f6-sw34 c4 = derive (Sw34 ∷ []) (CX34 ∷ CX43 ∷ CX34 ∷ [])
  (rw⁻ 0 (q132 c4) ∷ []) Eq.refl
