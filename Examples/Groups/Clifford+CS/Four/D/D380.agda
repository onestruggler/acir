{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D380 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00006 ; wn00007 ; wn00027 ; wn00029 ; wn00031 ; wn00039 ; wn00047 ; wn00048 ; wn00056 ; wn00065 ; wn00076 ; wn00084 ; wn00100 ; wn00104 ; wn00151)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00371)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00464)
open import Examples.Groups.Clifford+CS.Four.Wins.W04 using (wn00551 ; wn00552)
open import Examples.Groups.Clifford+CS.Four.Wins.W14 using (wn00890)
open import Examples.Groups.Clifford+CS.Four.Wins.W15 using (wn00908 ; wn00909)
open import Examples.Groups.Clifford+CS.Four.Wins.W20 using (wn01048 ; wn01049 ; wn01050 ; wn01051 ; wn01052 ; wn01053 ; wn01054 ; wn01055 ; wn01056 ; wn01057 ; wn01058 ; wn01059 ; wn01060 ; wn01061 ; wn01062 ; wn01063 ; wn01064 ; wn01065 ; wn01066 ; wn01067 ; wn01068 ; wn01069 ; wn01070 ; wn01071 ; wn01072 ; wn01073 ; wn01074 ; wn01075 ; wn01076 ; wn01077 ; wn01078 ; wn01079 ; wn01080 ; wn01081 ; wn01082)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CSd01 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 32 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 31 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 30 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 29 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸
       at 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] wn00003 ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b1 = at 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] wn00003 ▸
       at 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] wn00003 ▸
       at 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] wn00003 ▸ done

  b2 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b2 = at 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 [] wn00003 ▸
       at 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸
       at 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] wn00003 ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸ done

  b3 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b3 = at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] wn00003 ▸
       at 15 2 (Sw23 ∷ S2 ∷ []) wn00464 ▸
       at 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ Sw23 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 16 2 [] wn00003 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ S2 ∷ []) wn00464 ▸ done

  b5 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ Sw23 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ Sw23 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ S2 ∷ []) wn00464 ▸
       at 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸ done

  b6 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ Sw23 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ Sw23 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ [])
  b6 = at 4 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 2 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 32 (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) wn01048 ▸
       at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 1 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸ done

  b7 : Chain (X1 ∷ CS01⁻ ∷ Sw23 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ [])
  b7 = at 2 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 3 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 4 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 5 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 6 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 7 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 8 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b8 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ [])
  b8 = at 9 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b9 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ [])
  b9 = at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 15 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 16 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸ done

  b10 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ [])
  b10 = at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 21 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 24 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 22 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ [])
  b11 = at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 23 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ [])
  b12 = at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 27 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 32 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 30 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b13 = at 33 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 31 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] wn00003 ▸ done

-- pass [X1 CS13 X1] [CS02]: 7 steps
lem-pass-X1-CS13-X1-vs-CS02 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-CS02 = run b0
  where
  b0 : Chain (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  b0 = at 2 2 (CS02 ∷ X1 ∷ []) wn01049 ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 2 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ X1 ∷ []) wn01049 ▸ done

-- pass [X1 CS13 X1] [TOFF013]: 65 steps
lem-pass-X1-CS13-X1-vs-TOFF013 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X1 ∷ CS13 ∷ X1 ∷ Toff013 ∷ []) (X1 ∷ CS13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X1 ∷ CS13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ CS13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X1 ∷ CS13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (X1 ∷ CS13 ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X1 ∷ CS13 ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff012 ∷ Sw23 ∷ [])
  b3 = at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b4 : Chain (Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ Toff012 ∷ Sw23 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 1 4 (Toff012 ∷ X1 ∷ CS12 ∷ X1 ∷ []) wn01050 ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ [])
  b6 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b8 : Chain (Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [X1 CS13 X1] [CSd02]: 7 steps
lem-pass-X1-CS13-X1-vs-CSd02 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-CSd02 = run b0
  where
  b0 : Chain (X1 ∷ CS13 ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  b0 = at 2 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 2 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 1 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸ done

-- pass [X1 CK13 X1] [CS02]: 7 steps
lem-pass-X1-CK13-X1-vs-CS02 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-CS02 = run b0
  where
  b0 : Chain (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  b0 = at 2 2 (CS02 ∷ X1 ∷ []) wn01049 ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 2 2 (CS01 ∷ CK23 ∷ []) (sym (low-comm (CS) (CK₀₁))) ▸
       at 3 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ X1 ∷ []) wn01049 ▸ done

-- pass [X1 CK13 X1] [TOFF013]: 65 steps
lem-pass-X1-CK13-X1-vs-TOFF013 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X1 ∷ CK13 ∷ X1 ∷ Toff013 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X1 ∷ CK13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X1 ∷ CK13 ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X1 ∷ CK13 ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Toff012 ∷ Sw23 ∷ [])
  b3 = at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b4 : Chain (Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Toff012 ∷ Sw23 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CK12 ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 1 4 (Toff012 ∷ X1 ∷ CK12 ∷ X1 ∷ []) wn01054 ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CK12 ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw23 ∷ [])
  b6 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b8 : Chain (Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [X1 CK13 X1] [CSd02]: 7 steps
lem-pass-X1-CK13-X1-vs-CSd02 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-CSd02 = run b0
  where
  b0 : Chain (X1 ∷ CK13 ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  b0 = at 2 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 2 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 3 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 1 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸ done

-- pass [X1 CSd13 X1] [CS02]: 7 steps
lem-pass-X1-CSd13-X1-vs-CS02 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CS02 = run b0
  where
  b0 : Chain (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  b0 = at 2 2 (CS02 ∷ X1 ∷ []) wn01049 ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 2 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸
       at 3 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ X1 ∷ []) wn01049 ▸ done

-- pass [X1 CSd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CSd13-X1-vs-TOFF013 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X1 ∷ CS13⁻ ∷ X1 ∷ Toff013 ∷ []) (X1 ∷ CS13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X1 ∷ CS13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ CS13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X1 ∷ CS13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (X1 ∷ CS13⁻ ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X1 ∷ CS13⁻ ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Toff012 ∷ Sw23 ∷ [])
  b3 = at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b4 : Chain (Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Toff012 ∷ Sw23 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 1 4 (Toff012 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) wn01055 ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b6 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b8 : Chain (Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [X1 CSd13 X1] [CSd02]: 7 steps
lem-pass-X1-CSd13-X1-vs-CSd02 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CSd02 = run b0
  where
  b0 : Chain (X1 ∷ CS13⁻ ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  b0 = at 2 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 2 2 (CS01⁻ ∷ CS23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((CS • CS • CS)))) ▸
       at 3 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 1 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸ done

-- pass [CCZ123] [X1 CS01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CS01-X1 : ⟪ (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CS01-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) wn01056 ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CS01 ∷ CX23 ∷ []) (sym (low-comm (CS) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 4 (X1 ∷ CS01 ∷ X1 ∷ CS12⁻ ∷ []) wn01057 ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] wn00003 ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CS01 ∷ CX23 ∷ []) (sym (low-comm (CS) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 4 (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) wn01058 ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] wn00003 ▸
       at 0 4 (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) wn01058 ▸
       at 3 5 (CCZ123 ∷ []) wn01059 ▸ done

-- pass [CCZ123] [X1 CK10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CK10-X1 : ⟪ (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CK10-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) wn01056 ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CK10 ∷ CX23 ∷ []) (sym (low-comm (CK₁₀) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 4 (X1 ∷ CK10 ∷ X1 ∷ CS12⁻ ∷ []) wn01060 ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] wn00003 ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CK10 ∷ CX23 ∷ []) (sym (low-comm (CK₁₀) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 4 (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) wn01061 ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] wn00003 ▸
       at 0 4 (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) wn01061 ▸
       at 3 5 (CCZ123 ∷ []) wn01059 ▸ done

-- pass [CS03] [iI]: 9 steps
lem-pass-CS03-vs-iI : ⟪ (CS03 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-iI = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ ι ∷ []) (ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (ι ∷ CS02 ∷ []) wn01062 ▸
       at 0 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (ι ∷ CS03 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CS03] [Z1]: 9 steps
lem-pass-CS03-vs-Z1 : ⟪ (CS03 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z1 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Z1 ∷ []) (Z1 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (Z1 ∷ CS02 ∷ []) wn01063 ▸
       at 0 2 (Z1 ∷ Sw23 ∷ []) (sym (low-comm ((Z ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z1 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (Z1 ∷ CS03 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CS03] [Z2]: 15 steps
lem-pass-CS03-vs-Z2 : ⟪ (CS03 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Z2 ∷ []) (Sw01 ∷ Z2 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ Z2 ∷ []) (sym (low-comm (Swap) (Z))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Z2 ∷ CS13 ∷ []) wn01064 ▸ done

  b1 : Chain (Sw01 ∷ Z2 ∷ CS13 ∷ Sw01 ∷ []) (Z2 ∷ CS03 ∷ [])
  b1 = at 0 2 (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CS03] [Z3]: 9 steps
lem-pass-CS03-vs-Z3 : ⟪ (CS03 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Z3 ∷ []) (Z3 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ Z2 ∷ []) wn01065 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (Z2 ∷ CS02 ∷ []) wn01066 ▸
       at 0 2 (Z3 ∷ Sw23 ∷ []) wn00371 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z3 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (Z3 ∷ CS03 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CS03] [CZ13]: 11 steps
lem-pass-CS03-vs-CZ13 : ⟪ (CS03 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ13 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CZ13 ∷ []) (CZ13 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CZ12 ∷ CS02 ∷ []) wn00552 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ13 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CZ13 ∷ CS03 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

-- pass [CS03] [CZ23]: 15 steps
lem-pass-CS03-vs-CZ23 : ⟪ (CS03 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CZ23 ∷ []) (Sw01 ∷ CZ23 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ CS13 ∷ []) wn00890 ▸ done

  b1 : Chain (Sw01 ∷ CZ23 ∷ CS13 ∷ Sw01 ∷ []) (CZ23 ∷ CS03 ∷ [])
  b1 = at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [TOFF012] [iI]: 1 steps
lem-pass-TOFF012-vs-iI : ⟪ (Toff012 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-iI = run b0
  where
  b0 : Chain (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ [])
  b0 = at 0 2 (ι ∷ Toff012 ∷ []) wn01067 ▸ done

-- pass [TOFF012] [Z1]: 1 steps
lem-pass-TOFF012-vs-Z1 : ⟪ (Toff012 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z1 = run b0
  where
  b0 : Chain (Toff012 ∷ Z1 ∷ []) (Z1 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Z1 ∷ Toff012 ∷ []) wn01068 ▸ done

-- pass [TOFF012] [Z2]: 1 steps
lem-pass-TOFF012-vs-Z2 : ⟪ (Toff012 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z2 = run b0
  where
  b0 : Chain (Toff012 ∷ Z2 ∷ []) (Z2 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Z2 ∷ Toff012 ∷ []) wn01069 ▸ done

-- pass [TOFF012] [CZ12]: 1 steps
lem-pass-TOFF012-vs-CZ12 : ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CZ12 = run b0
  where
  b0 : Chain (Toff012 ∷ CZ12 ∷ []) (CZ12 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CZ12 ∷ Toff012 ∷ []) wn01070 ▸ done

-- pass [TOFF012] [Z3]: 1 steps
lem-pass-TOFF012-vs-Z3 : ⟪ (Toff012 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z3 = run b0
  where
  b0 : Chain (Toff012 ∷ Z3 ∷ []) (Z3 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Z3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (Z)) ▸ done

-- comm CCZ012 CZ23: 19 steps
lem-comm-CCZ012-CZ23 : ⟪ (CCZ012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ23 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ012 ∷ CZ23 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) wn00100 ▸
       at 4 2 (CZ23 ∷ CS12 ∷ []) wn00909 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (CZ23 ∷ CX21 ∷ []) wn00908 ▸
       at 3 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸ done

  b1 : Chain (CS01 ∷ CX20 ∷ CS01⁻ ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS12 ∷ []) (CS01 ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
  b1 = at 5 2 [] wn00031 ▸
       at 2 2 (CZ23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CZ)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 1 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (CZ23 ∷ CX21 ∷ []) wn00908 ▸
       at 1 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸ done

  b2 : Chain (CS01 ∷ CZ23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CZ23 ∷ CCZ012 ∷ [])
  b2 = at 3 2 [] wn00031 ▸
       at 0 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 1 5 (CCZ012 ∷ []) wn00104 ▸ done

-- pass [CSd03] [iI]: 9 steps
lem-pass-CSd03-vs-iI : ⟪ (CS03⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-iI = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ ι ∷ []) (ι ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (ι ∷ CS02⁻ ∷ []) wn01071 ▸
       at 0 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (ι ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (ι ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CSd03] [Z1]: 9 steps
lem-pass-CSd03-vs-Z1 : ⟪ (CS03⁻ ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z1 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Z1 ∷ []) (Z1 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (Z1 ∷ CS02⁻ ∷ []) wn01072 ▸
       at 0 2 (Z1 ∷ Sw23 ∷ []) (sym (low-comm ((Z ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z1 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Z1 ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CSd03] [Z2]: 15 steps
lem-pass-CSd03-vs-Z2 : ⟪ (CS03⁻ ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Z2 ∷ []) (Sw01 ∷ Z2 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ Z2 ∷ []) (sym (low-comm (Swap) (Z))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Z2 ∷ CS13⁻ ∷ []) wn01073 ▸ done

  b1 : Chain (Sw01 ∷ Z2 ∷ CS13⁻ ∷ Sw01 ∷ []) (Z2 ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CSd03] [Z3]: 9 steps
lem-pass-CSd03-vs-Z3 : ⟪ (CS03⁻ ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Z3 ∷ []) (Z3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ Z2 ∷ []) wn01065 ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (Z2 ∷ CS02⁻ ∷ []) wn01074 ▸
       at 0 2 (Z3 ∷ Sw23 ∷ []) wn00371 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Z3 ∷ CS03⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CSd03] [CZ13]: 11 steps
lem-pass-CSd03-vs-CZ13 : ⟪ (CS03⁻ ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ13 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CZ13 ∷ []) (CZ13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CZ12 ∷ CS02⁻ ∷ []) wn00551 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (CZ13 ∷ CS03⁻ ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

-- pass [CSd03] [CZ23]: 15 steps
lem-pass-CSd03-vs-CZ23 : ⟪ (CS03⁻ ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CZ23 ∷ []) (Sw01 ∷ CZ23 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ CS13⁻ ∷ []) wn01075 ▸ done

  b1 : Chain (Sw01 ∷ CZ23 ∷ CS13⁻ ∷ Sw01 ∷ []) (CZ23 ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CCZ123] [X1 CKd10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CKd10-X1 : ⟪ (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CKd10-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) wn01056 ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CK10⁻ ∷ CX23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CS12⁻ ∷ []) wn01076 ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] wn00003 ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CK10⁻ ∷ CX23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) wn01077 ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] wn00003 ▸
       at 0 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) wn01077 ▸
       at 3 5 (CCZ123 ∷ []) wn01059 ▸ done

-- pass [CCZ123] [X1 CSd01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CSd01-X1 : ⟪ (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CSd01-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) wn01056 ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CS01⁻ ∷ CX23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CS12⁻ ∷ []) wn01078 ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] wn00003 ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CS01⁻ ∷ CX23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) wn01079 ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] wn00003 ▸
       at 0 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) wn01079 ▸
       at 3 5 (CCZ123 ∷ []) wn01059 ▸ done

-- pass [X1 CKd13 X1] [CS02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CS02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS02 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 2 2 (CS02 ∷ X1 ∷ []) wn01049 ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK23⁻ ∷ []) wn01080 ▸
       at 2 2 (CS01 ∷ CK23⁻ ∷ []) (sym (low-comm (CS) ((S • CK₀₁)))) ▸
       at 3 2 (Sw12 ∷ CK13⁻ ∷ []) wn01081 ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ X1 ∷ []) wn01049 ▸ done

-- pass [X1 CKd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CKd13-X1-vs-TOFF013 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ Sw23 ∷ [])
  b3 = at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b4 : Chain (Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ Sw23 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 1 4 (Toff012 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) wn01082 ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b6 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b8 : Chain (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [X1 CKd13 X1] [CSd02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CSd02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CSd02 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 2 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK23⁻ ∷ []) wn01080 ▸
       at 2 2 (CS01⁻ ∷ CK23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((S • CK₀₁)))) ▸
       at 3 2 (Sw12 ∷ CK13⁻ ∷ []) wn01081 ▸
       at 1 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸ done
