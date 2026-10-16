{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D202 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0283 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0892 ; wl0893 ; wl0895 ; wl0896 ; wl0897 ; wl0898 ; wl0899 ; wl0930 ; wl0931 ; wl0932 ; wl0933 ; wl0934 ; wl0935 ; wl0936 ; wl0937 ; wl0938 ; wl0939 ; wl0940 ; wl0941 ; wl0942 ; wl0943 ; wl0944 ; wl0945 ; wl0946 ; wl0947 ; wl0948 ; wl0949 ; wl0950 ; wl0951 ; wl0952 ; wl0953 ; wl0954 ; wl0955 ; wl0956 ; wl0957 ; wl0958 ; wl0959 ; wl0960 ; wl0961 ; wl0962 ; wl0963 ; wl0964 ; wl0965 ; wl0966 ; wl0967 ; wl0968 ; wl0969 ; wl0970 ; wl0971 ; wl0972 ; wl0973 ; wl0974 ; wp0461 ; wp0465 ; wp0502 ; wp0503 ; wp0504 ; wp0505 ; wp0506 ; wp0507 ; wp0508 ; wp0509 ; wp0510 ; wp0511 ; wp0512 ; wp0513 ; wp0514 ; wp0515 ; wp0516 ; wp0517)
open import Examples.Groups.Clifford+CS.Five.Chain
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
-- calc F4 S1 S0: 1 steps
lem-calc-F4-S1-S0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0502 c4)) ▸ done


-- calc F4 S1 K0: 1 steps
lem-calc-F4-S1-K0 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wp0503 c4)) ▸ done


-- calc F4 S1 S1: 1 steps
lem-calc-F4-S1-S1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0930 (lit c4))) ▸ done


-- calc F4 S1 K1: 1 steps
lem-calc-F4-S1-K1 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0931 (lit c4))) ▸ done


-- calc F4 S1 S2: 1 steps
lem-calc-F4-S1-S2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0932 (lit c4))) ▸ done


-- calc F4 S1 K2: 1 steps
lem-calc-F4-S1-K2 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0933 (lit c4))) ▸ done


-- calc F4 S1 S3: 1 steps
lem-calc-F4-S1-S3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0934 (lit c4))) ▸ done


-- calc F4 S1 K3: 1 steps
lem-calc-F4-S1-K3 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (sym (wl0935 (lit c4))) ▸ done


-- calc F4 S1 CS01: 1 steps
lem-calc-F4-S1-CS01 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S1ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 S1 CS12: 1 steps
lem-calc-F4-S1-CS12 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S1ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 S1 CS23: 1 steps
lem-calc-F4-S1-CS23 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S1-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S1ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 K1 I: 1 steps
lem-calc-F4-K1-I : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0887 (lit c4))) ▸ done


-- calc F4 K1 S0: 1 steps
lem-calc-F4-K1-S0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0465 c4)) ▸ done


-- calc F4 K1 K0: 1 steps
lem-calc-F4-K1-K0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0504 c4)) ▸ done


-- calc F4 K1 S1: 1 steps
lem-calc-F4-K1-S1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0892 (lit c4))) ▸ done


-- calc F4 K1 K1: 1 steps
lem-calc-F4-K1-K1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0888 (lit c4))) ▸ done


-- calc F4 K1 S2: 1 steps
lem-calc-F4-K1-S2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0897 (lit c4))) ▸ done


-- calc F4 K1 K2: 1 steps
lem-calc-F4-K1-K2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0936 (lit c4))) ▸ done


-- calc F4 K1 S3: 1 steps
lem-calc-F4-K1-S3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0937 (lit c4))) ▸ done


-- calc F4 K1 K3: 1 steps
lem-calc-F4-K1-K3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0938 (lit c4))) ▸ done


-- calc F4 K1 CS01: 1 steps
lem-calc-F4-K1-CS01 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 K1 CS12: 1 steps
lem-calc-F4-K1-CS12 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 K1 CS23: 1 steps
lem-calc-F4-K1-CS23 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K1-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 S2 I: 1 steps
lem-calc-F4-S2-I : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0895 (lit c4))) ▸ done


-- calc F4 S2 S0: 1 steps
lem-calc-F4-S2-S0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0505 c4)) ▸ done


-- calc F4 S2 K0: 1 steps
lem-calc-F4-S2-K0 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wp0506 c4)) ▸ done


-- calc F4 S2 S1: 1 steps
lem-calc-F4-S2-S1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0898 (lit c4))) ▸ done


-- calc F4 S2 K1: 1 steps
lem-calc-F4-S2-K1 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0899 (lit c4))) ▸ done


-- calc F4 S2 S2: 1 steps
lem-calc-F4-S2-S2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸ done


-- calc F4 S2 K2: 1 steps
lem-calc-F4-S2-K2 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0939 (lit c4))) ▸ done


-- calc F4 S2 S3: 1 steps
lem-calc-F4-S2-S3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0940 (lit c4))) ▸ done


-- calc F4 S2 K3: 1 steps
lem-calc-F4-S2-K3 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (sym (wl0941 (lit c4))) ▸ done


-- calc F4 S2 CS01: 1 steps
lem-calc-F4-S2-CS01 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 S2 CS12: 1 steps
lem-calc-F4-S2-CS12 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 S2 CS23: 1 steps
lem-calc-F4-S2-CS23 : Ws → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S2-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 K2 I: 1 steps
lem-calc-F4-K2-I : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0942 (lit c4))) ▸ done


-- calc F4 K2 S0: 1 steps
lem-calc-F4-K2-S0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0507 c4)) ▸ done


-- calc F4 K2 K0: 1 steps
lem-calc-F4-K2-K0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0508 c4)) ▸ done


-- calc F4 K2 S1: 1 steps
lem-calc-F4-K2-S1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0943 (lit c4))) ▸ done


-- calc F4 K2 K1: 1 steps
lem-calc-F4-K2-K1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0944 (lit c4))) ▸ done


-- calc F4 K2 S2: 1 steps
lem-calc-F4-K2-S2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0945 (lit c4))) ▸ done


-- calc F4 K2 K2: 1 steps
lem-calc-F4-K2-K2 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0946 (lit c4))) ▸ done


-- calc F4 K2 S3: 1 steps
lem-calc-F4-K2-S3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0947 (lit c4))) ▸ done


-- calc F4 K2 K3: 1 steps
lem-calc-F4-K2-K3 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0948 (lit c4))) ▸ done


-- calc F4 K2 CS01: 1 steps
lem-calc-F4-K2-CS01 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 K2 CS12: 1 steps
lem-calc-F4-K2-CS12 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 K2 CS23: 1 steps
lem-calc-F4-K2-CS23 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K2-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K2ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 S3 I: 1 steps
lem-calc-F4-S3-I : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0949 (lit c4))) ▸ done


-- calc F4 S3 S0: 1 steps
lem-calc-F4-S3-S0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0509 c4)) ▸ done


-- calc F4 S3 K0: 1 steps
lem-calc-F4-S3-K0 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wp0510 c4)) ▸ done


-- calc F4 S3 S1: 1 steps
lem-calc-F4-S3-S1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0950 (lit c4))) ▸ done


-- calc F4 S3 K1: 1 steps
lem-calc-F4-S3-K1 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0951 (lit c4))) ▸ done


-- calc F4 S3 S2: 1 steps
lem-calc-F4-S3-S2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0952 (lit c4))) ▸ done


-- calc F4 S3 K2: 1 steps
lem-calc-F4-S3-K2 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0953 (lit c4))) ▸ done


-- calc F4 S3 S3: 1 steps
lem-calc-F4-S3-S3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0954 (lit c4))) ▸ done


-- calc F4 S3 K3: 1 steps
lem-calc-F4-S3-K3 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (sym (wl0955 (lit c4))) ▸ done


-- calc F4 S3 CS01: 1 steps
lem-calc-F4-S3-CS01 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 S3 CS12: 1 steps
lem-calc-F4-S3-CS12 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 S3 CS23: 1 steps
lem-calc-F4-S3-CS23 : Ws → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-S3-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lem-F4-S3ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 K3 I: 1 steps
lem-calc-F4-K3-I : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0956 (lit c4))) ▸ done


-- calc F4 K3 S0: 1 steps
lem-calc-F4-K3-S0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0511 c4)) ▸ done


-- calc F4 K3 K0: 1 steps
lem-calc-F4-K3-K0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0512 c4)) ▸ done


-- calc F4 K3 S1: 1 steps
lem-calc-F4-K3-S1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0957 (lit c4))) ▸ done


-- calc F4 K3 K1: 1 steps
lem-calc-F4-K3-K1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0958 (lit c4))) ▸ done


-- calc F4 K3 S2: 1 steps
lem-calc-F4-K3-S2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0959 (lit c4))) ▸ done


-- calc F4 K3 K2: 1 steps
lem-calc-F4-K3-K2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0960 (lit c4))) ▸ done


-- calc F4 K3 S3: 1 steps
lem-calc-F4-K3-S3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0961 (lit c4))) ▸ done


-- calc F4 K3 K3: 1 steps
lem-calc-F4-K3-K3 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0962 (lit c4))) ▸ done


-- calc F4 K3 CS01: 1 steps
lem-calc-F4-K3-CS01 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 K3 CS12: 1 steps
lem-calc-F4-K3-CS12 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 K3 CS23: 1 steps
lem-calc-F4-K3-CS23 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-K3-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 CS01 I: 1 steps
lem-calc-F4-CS01-I : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-I c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4) ▸ done


-- calc F4 CS01 S0: 1 steps
lem-calc-F4-CS01-S0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4) ▸ done


-- calc F4 CS01 K0: 1 steps
lem-calc-F4-CS01-K0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K0ᵖ1 c4) ▸ done


-- calc F4 CS01 S1: 1 steps
lem-calc-F4-CS01-S1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S1ᵖ1 c4) ▸ done


-- calc F4 CS01 K1: 1 steps
lem-calc-F4-CS01-K1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4) ▸ done


-- calc F4 CS01 S2: 1 steps
lem-calc-F4-CS01-S2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S2ᵖ1 c4) ▸ done


-- calc F4 CS01 K2: 1 steps
lem-calc-F4-CS01-K2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K2ᵖ1 c4) ▸ done


-- calc F4 CS01 S3: 1 steps
lem-calc-F4-CS01-S3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S3ᵖ1 c4) ▸ done


-- calc F4 CS01 K3: 1 steps
lem-calc-F4-CS01-K3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K3ᵖ1 c4) ▸ done


-- calc F4 CS01 CS01: 1 steps
lem-calc-F4-CS01-CS01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 CS01 CS12: 1 steps
lem-calc-F4-CS01-CS12 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 CS01 CS23: 1 steps
lem-calc-F4-CS01-CS23 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS01-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 CS12 I: 1 steps
lem-calc-F4-CS12-I : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-I c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4) ▸ done


-- calc F4 CS12 S0: 1 steps
lem-calc-F4-CS12-S0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S0ᵖ1 c4) ▸ done


-- calc F4 CS12 K0: 1 steps
lem-calc-F4-CS12-K0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K0ᵖ1 c4) ▸ done


-- calc F4 CS12 S1: 1 steps
lem-calc-F4-CS12-S1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S1ᵖ1 c4) ▸ done


-- calc F4 CS12 K1: 1 steps
lem-calc-F4-CS12-K1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4) ▸ done


-- calc F4 CS12 S2: 1 steps
lem-calc-F4-CS12-S2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4) ▸ done


-- calc F4 CS12 K2: 1 steps
lem-calc-F4-CS12-K2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K2ᵖ1 c4) ▸ done


-- calc F4 CS12 S3: 1 steps
lem-calc-F4-CS12-S3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S3ᵖ1 c4) ▸ done


-- calc F4 CS12 K3: 1 steps
lem-calc-F4-CS12-K3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K3ᵖ1 c4) ▸ done


-- calc F4 CS12 CS01: 1 steps
lem-calc-F4-CS12-CS01 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 CS12 CS12: 1 steps
lem-calc-F4-CS12-CS12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 CS12 CS23: 1 steps
lem-calc-F4-CS12-CS23 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS12-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F4 CS23 I: 1 steps
lem-calc-F4-CS23-I : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-I c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣iIᵖ1 c4) ▸ done


-- calc F4 CS23 S0: 1 steps
lem-calc-F4-CS23-S0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S0ᵖ1 c4) ▸ done


-- calc F4 CS23 K0: 1 steps
lem-calc-F4-CS23-K0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K0ᵖ1 c4) ▸ done


-- calc F4 CS23 S1: 1 steps
lem-calc-F4-CS23-S1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S1ᵖ1 c4) ▸ done


-- calc F4 CS23 K1: 1 steps
lem-calc-F4-CS23-K1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K1ᵖ1 c4) ▸ done


-- calc F4 CS23 S2: 1 steps
lem-calc-F4-CS23-S2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S2ᵖ1 c4) ▸ done


-- calc F4 CS23 K2: 1 steps
lem-calc-F4-CS23-K2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K2ᵖ1 c4) ▸ done


-- calc F4 CS23 S3: 1 steps
lem-calc-F4-CS23-S3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣S3ᵖ1 c4) ▸ done


-- calc F4 CS23 K3: 1 steps
lem-calc-F4-CS23-K3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣K3ᵖ1 c4) ▸ done


-- calc F4 CS23 CS01: 1 steps
lem-calc-F4-CS23-CS01 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 CS23 CS12: 1 steps
lem-calc-F4-CS23-CS12 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 CS23 CS23: 1 steps
lem-calc-F4-CS23-CS23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-CS23-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS23ᵖ0∣CS23ᵖ1 c4) ▸ done


-- calc F5 I 0: 1 steps
lem-calc-F5-I-0 : Ws → ⟪ (ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-0 c4 = run b0
  where
  b0 : Chain (ι ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸ done


-- calc F5 I 1: 1 steps
lem-calc-F5-I-1 : Ws → ⟪ (ι1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-1 c4 = run b0
  where
  b0 : Chain (ι1 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0963 (lit c4))) ▸ done


-- calc F5 I 2: 1 steps
lem-calc-F5-I-2 : Ws → ⟪ (ι2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-2 c4 = run b0
  where
  b0 : Chain (ι2 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0964 (lit c4))) ▸ done


-- calc F5 I 3: 1 steps
lem-calc-F5-I-3 : Ws → ⟪ (ι3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-3 c4 = run b0
  where
  b0 : Chain (ι3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0965 (lit c4))) ▸ done


-- calc F5 I 4: 1 steps
lem-calc-F5-I-4 : Ws → ⟪ (ι4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
lem-calc-F5-I-4 c4 = run b0
  where
  b0 : Chain (ι4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0966 (lit c4))) ▸ done


-- calc F5 S0: 1 steps
lem-calc-F5-S0 : Ws → ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
lem-calc-F5-S0 c4 = run b0
  where
  b0 : Chain (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ [])
  b0 = at 0 1 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4) ▸ done


-- calc F5 K0: 1 steps
lem-calc-F5-K0 : Ws → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
lem-calc-F5-K0 c4 = run b0
  where
  b0 : Chain (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ [])
  b0 = at 0 1 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp0513 c4) ▸ done


-- calc F5 S1: 1 steps
lem-calc-F5-S1 : Ws → ⟪ (S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
lem-calc-F5-S1 c4 = run b0
  where
  b0 : Chain (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ [])
  b0 = at 0 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl0967 (lit c4)) ▸ done


-- calc F5 K1: 1 steps
lem-calc-F5-K1 : Ws → ⟪ (K1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
lem-calc-F5-K1 c4 = run b0
  where
  b0 : Chain (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ [])
  b0 = at 0 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸ done


-- calc F5 S2: 1 steps
lem-calc-F5-S2 : Ws → ⟪ (S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
lem-calc-F5-S2 c4 = run b0
  where
  b0 : Chain (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ [])
  b0 = at 0 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸ done


-- calc F5 K2: 1 steps
lem-calc-F5-K2 : Ws → ⟪ (K2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
lem-calc-F5-K2 c4 = run b0
  where
  b0 : Chain (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ [])
  b0 = at 0 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl0968 (lit c4)) ▸ done


-- calc F5 S3: 1 steps
lem-calc-F5-S3 : Ws → ⟪ (S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
lem-calc-F5-S3 c4 = run b0
  where
  b0 : Chain (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ [])
  b0 = at 0 1 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (wl0969 (lit c4)) ▸ done


-- calc F5 K3: 1 steps
lem-calc-F5-K3 : Ws → ⟪ (K3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
lem-calc-F5-K3 c4 = run b0
  where
  b0 : Chain (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ [])
  b0 = at 0 1 (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) (wl0970 (lit c4)) ▸ done


-- calc F5 CS01: 1 steps
lem-calc-F5-CS01 : Ws → ⟪ (CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-calc-F5-CS01 c4 = run b0
  where
  b0 : Chain (CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-CS01 c4)) ▸ done


-- calc F5 CS12: 1 steps
lem-calc-F5-CS12 : Ws → ⟪ (CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-calc-F5-CS12 c4 = run b0
  where
  b0 : Chain (CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸ done


-- calc F5 CS23: 1 steps
lem-calc-F5-CS23 : Ws → ⟪ (CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-calc-F5-CS23 c4 = run b0
  where
  b0 : Chain (CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-CS23 c4)) ▸ done


-- f6 cx14: 2 steps
lem-f6-cx14 : Ws → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ []) ⟫ʷ
lem-f6-cx14 c4 = run b0
  where
  b0 : Chain (CX14 ∷ []) (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b0 = at 0 1 (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) (wp0514 c4) ▸
       at 4 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸ done


-- f6 w1: 1 steps
lem-f6-w1 : Ws → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-f6-w1 c4 = run b0
  where
  b0 : Chain (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 5 (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (sym (wp0515 c4)) ▸ done


-- f6 w2: 1 steps
lem-f6-w2 : Ws → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
lem-f6-w2 c4 = run b0
  where
  b0 : Chain (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ [])
  b0 = at 0 11 (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) (wp0516 c4) ▸ done


-- f6 aa: 1 steps
lem-f6-aa : Ws → ⟪ (CX14 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-f6-aa c4 = run b0
  where
  b0 : Chain (CX14 ∷ CX14 ∷ []) []
  b0 = at 0 2 [] (wl0971 (lit c4)) ▸ done


-- f6 ee: 1 steps
lem-f6-ee : Ws → ⟪ (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-f6-ee c4 = run b0
  where
  b0 : Chain (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) []
  b0 = at 0 4 [] (wp0517 c4) ▸ done


-- f6 cx43: 1 steps
lem-f6-cx43 : Ws → ⟪ (CX43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-f6-cx43 c4 = run b0
  where
  b0 : Chain (CX43 ∷ []) (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 0 1 (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) (sym (wl0972 (lit c4))) ▸ done


-- f6 cx34: 1 steps
lem-f6-cx34 : Ws → ⟪ (CX34 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-f6-cx34 c4 = run b0
  where
  b0 : Chain (CX34 ∷ []) (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ []) (wl0973 (lit c4)) ▸ done


-- f6 sw34: 1 steps
lem-f6-sw34 : Ws → ⟪ (Sw34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ CX43 ∷ CX34 ∷ []) ⟫ʷ
lem-f6-sw34 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ []) (CX34 ∷ CX43 ∷ CX34 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0974 (lit c4))) ▸ done

