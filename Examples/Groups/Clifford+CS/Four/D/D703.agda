{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D703 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00024 ; wn00025 ; wn00027 ; wn00029 ; wn00030 ; wn00031 ; wn00076 ; wn00122 ; wn00124 ; wn00151 ; wn00153 ; wn00173 ; wn00175 ; wn00196)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00231 ; wn00257 ; wn00258 ; wn00334)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00464)
open import Examples.Groups.Clifford+CS.Four.Wins.W08 using (wn00689)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01357 ; wn01377 ; wn01379 ; wn01380 ; wn01381)
open import Examples.Groups.Clifford+CS.Four.Wins.W29 using (wn01523 ; wn01524 ; wn01525)
open import Examples.Groups.Clifford+CS.Four.Wins.W35 using (wn01694)
open import Examples.Groups.Clifford+CS.Four.Wins.W41 using (wn01962 ; wn01963 ; wn01965 ; wn01966 ; wn01967 ; wn01968 ; wn01969 ; wn01970 ; wn01971)
open import Examples.Groups.Clifford+CS.Four.Wins.W42 using (wn01999 ; wn02016 ; wn02017)
open import Examples.Groups.Clifford+CS.Four.Wins.W43 using (wn02041 ; wn02042 ; wn02051 ; wn02052 ; wn02053 ; wn02054 ; wn02055 ; wn02056 ; wn02057 ; wn02058)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D677 using (lem-S2-at0213 ; lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D678 using (lem-S2-at1203 ; lem-S2-at2013)
open import Examples.Groups.Clifford+CS.Four.D.D679 using (lem-S2-at2103)
open import Examples.Groups.Clifford+CS.Four.D.D683 using (lem-S2-ᵖ-1 ; lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D684 using (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 ; lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 ; lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D685 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3)
open import Examples.Groups.Clifford+CS.Four.D.D686 using (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3)

-- S2 @2013 ^-1: 129 steps
lem-S2-at2013-ᵖ-1 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) ⟫ʷ
lem-S2-at2013-ᵖ-1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Toff213 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 0 (Toff213 ∷ Toff213 ∷ []) wn02051 ▸
       at 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b1 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K2 ∷ ι1 ∷ Toff213 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  b1 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 11 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b2 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Sw01 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  b2 = at 5 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸ done

  b3 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 12 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 5 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 5 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 5 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b5 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 12 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b6 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b6 = at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸ done

  b7 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ Toff213 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b7 = at 13 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 6 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 6 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 0 (CS12 ∷ CS12⁻ ∷ []) wn02052 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 0 (Toff213 ∷ Toff213 ∷ []) wn02051 ▸ done

  b8 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ Toff213 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b8 = at 7 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K2 ∷ ι1 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b9 = at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 13 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b10 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b10 = at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K2 ∷ ι ∷ Sw01 ∷ Toff213 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ K2 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b11 = at 13 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 14 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 7 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸
       at 7 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b12 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ K2 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b12 = at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K2 ∷ ι1 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b13 = at 13 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 14 2 (ι ∷ Sw01 ∷ []) wn00122 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b14 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b14 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 15 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 8 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) wn00334 ▸ done

  b15 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ Sw01 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS23 ∷ CS23⁻ ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b15 = at 8 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 7 0 (CS12⁻ ∷ CS12 ∷ []) wn02053 ▸
       at 4 4 (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-S2-at2013) ▸
       at 3 2 [] wn01524 ▸
       at 2 2 [] wn01523 ▸
       at 1 2 [] wn01524 ▸ done

  b16 : Chain (CS23 ∷ CS23⁻ ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ [])
  b16 = at 0 2 [] wn01525 ▸ done

-- S2 @1023 ^-1: 121 steps
lem-S2-at1023-ᵖ-1 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) ⟫ʷ
lem-S2-at1023-ᵖ-1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (run b15)))))))))))))))
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Toff102 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Toff102 ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ [])
  b1 = at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b2 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ [])
  b2 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b3 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b3 = at 11 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b5 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b6 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ Toff103 ∷ Sw23 ∷ Sw23 ∷ [])
  b6 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 6 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ Toff103 ∷ Sw23 ∷ Sw23 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b7 = at 6 2 [] wn00003 ▸
       at 5 0 (CS12 ∷ CS12⁻ ∷ []) wn02052 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b8 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b9 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b9 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b10 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b10 = at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 7 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b11 = at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b12 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b12 = at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b13 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b13 = at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 14 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 8 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸ done

  b14 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS13 ∷ CS13⁻ ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b14 = at 8 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 7 0 (CS12⁻ ∷ CS12 ∷ []) wn02053 ▸
       at 4 4 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-S2-at1023) ▸
       at 3 2 [] wn01380 ▸
       at 2 2 [] wn01379 ▸
       at 1 2 [] wn01380 ▸ done

  b15 : Chain (CS13 ∷ CS13⁻ ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ [])
  b15 = at 0 2 [] wn01381 ▸ done

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 12 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

-- pass [TOFF013 CS02 TOFF013 CSd02] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b0 = at 0 14 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (sym lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02) ▸ done

-- pass [CS03] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 1 steps
lem-pass-CS03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = run b0
  where
  b0 : Chain (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ [])
  b0 = at 0 7 (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) (sym lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03) ▸ done

-- pass [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 247 steps
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) wn01962 ▸
       at 9 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ [])
  b1 = at 11 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 12 2 [] wn00003 ▸
       at 11 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 13 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) wn01963 ▸ done

  b2 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b2 = at 12 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 2 [] wn00003 ▸
       at 14 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 8 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b3 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b3 = at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 10 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b4 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 [] wn00031 ▸
       at 10 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) wn02016 ▸
       at 13 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸ done

  b5 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ X3 ∷ [])
  b5 = at 16 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 16 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 16 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 15 2 (CS13 ∷ X2 ∷ []) wn00257 ▸ done

  b6 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b6 = at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 16 2 [] wn00031 ▸
       at 15 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) wn02016 ▸ done

  b7 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b7 = at 7 2 (ι ∷ S0⁻ ∷ X0 ∷ []) wn01965 ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 10 2 (S2⁻ ∷ CS02 ∷ X0 ∷ []) wn01966 ▸
       at 9 2 (S3⁻ ∷ Sw23 ∷ []) wn00153 ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b8 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b8 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 12 2 [] wn00003 ▸
       at 11 4 (X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ []) wn02054 ▸
       at 14 2 (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) wn01970 ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸ done

  b9 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b9 = at 18 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 19 2 (S2 ∷ CS02⁻ ∷ X0 ∷ []) wn02055 ▸
       at 18 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 21 2 [] wn00003 ▸
       at 20 4 (X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ []) wn02054 ▸ done

  b10 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι3 ∷ S3 ∷ X3 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b10 = at 3 20 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2) ▸
       at 3 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 2 2 (ι3 ∷ X3 ∷ []) wn01967 ▸
       at 2 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 3 2 (S0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑ ↑)))) ▸
       at 4 2 (ι3 ∷ ι3 ∷ ι3 ∷ S3 ∷ X3 ∷ []) wn01968 ▸
       at 4 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 5 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸ done

  b11 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι3 ∷ S3 ∷ X3 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b11 = at 6 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) wn01962 ▸
       at 8 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b12 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι3 ∷ X3 ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b12 = at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 11 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 12 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 14 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 13 2 (ι3 ∷ X3 ∷ []) wn01967 ▸ done

  b13 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι3 ∷ X3 ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X3 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b13 = at 13 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 15 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 14 2 (ι3 ∷ X3 ∷ []) wn01967 ▸
       at 14 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 16 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 15 2 (ι3 ∷ X3 ∷ []) wn01967 ▸
       at 15 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 16 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸ done

  b14 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X3 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b14 = at 17 2 (ι3 ∷ S3⁻ ∷ X3 ∷ []) wn02056 ▸
       at 17 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] wn00003 ▸
       at 19 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 20 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) wn01963 ▸
       at 19 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸ done

  b15 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ X2 ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b15 = at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 22 2 [] wn00003 ▸
       at 21 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 22 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 23 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 1 2 (ι ∷ X2 ∷ []) wn01999 ▸ done

  b16 : Chain (X0 ∷ ι ∷ X2 ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b16 = at 2 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 3 2 (ι ∷ X2 ∷ []) wn01999 ▸
       at 4 2 (ι ∷ X2 ∷ []) wn01999 ▸
       at 5 2 (ι ∷ X2 ∷ []) wn01999 ▸
       at 6 2 (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S)) ▸
       at 7 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b17 = at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b18 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ X2 ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b18 = at 9 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 10 2 [] wn00031 ▸
       at 9 4 (Toff012 ∷ X2 ∷ []) wn02017 ▸
       at 10 2 (ι ∷ X2 ∷ []) wn01999 ▸
       at 11 2 (ι ∷ X2 ∷ []) wn01999 ▸ done

  b19 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ X2 ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b19 = at 12 2 (ι ∷ X2 ∷ []) wn01999 ▸
       at 13 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 14 2 (ι ∷ X2 ∷ []) wn01999 ▸
       at 15 2 (S3⁻ ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) ((S • S • S))) ▸
       at 16 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b20 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b20 = at 19 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 18 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b21 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ X0 ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b21 = at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 19 2 [] wn00031 ▸
       at 18 4 (Toff012 ∷ X2 ∷ []) wn02017 ▸
       at 0 2 (ι ∷ X0 ∷ []) wn01969 ▸
       at 1 2 (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) wn01970 ▸
       at 5 2 (ι ∷ X0 ∷ []) wn01969 ▸ done

  b22 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ X0 ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ Sw23 ∷ X0 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b22 = at 6 2 (ι ∷ X0 ∷ []) wn01969 ▸
       at 7 2 (ι ∷ X0 ∷ []) wn01969 ▸
       at 8 2 (S3 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑ ↑))) ▸
       at 9 2 (ι ∷ S0⁻ ∷ X0 ∷ []) wn01965 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸ done

  b23 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ Sw23 ∷ X0 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ X0 ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b23 = at 12 2 (S2⁻ ∷ CS02 ∷ X0 ∷ []) wn01966 ▸
       at 11 2 (S3⁻ ∷ Sw23 ∷ []) wn00153 ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 14 2 [] wn00003 ▸
       at 13 2 (Toff012 ∷ X0 ∷ []) wn02057 ▸
       at 14 2 (ι ∷ X0 ∷ []) wn01969 ▸ done

  b24 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ X0 ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b24 = at 15 2 (ι ∷ X0 ∷ []) wn01969 ▸
       at 16 2 (ι ∷ X0 ∷ []) wn01969 ▸
       at 17 2 (ι ∷ S0⁻ ∷ X0 ∷ []) wn01965 ▸
       at 19 2 (ι ∷ X0 ∷ []) wn01969 ▸
       at 20 2 (S3⁻ ∷ X0 ∷ []) (low₁-comm (X) (((S • S • S) ↑ ↑))) ▸
       at 21 2 (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) wn01970 ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X0 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b25 = at 28 2 [] wn00003 ▸
       at 25 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 26 2 (S2 ∷ CS02⁻ ∷ X0 ∷ []) wn02055 ▸
       at 25 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 28 2 [] wn00003 ▸ done

  b26 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X0 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ Sw23 ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b26 = at 27 2 (Toff012 ∷ X0 ∷ []) wn02057 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ S2⁻ ∷ []) wn00689 ▸
       at 10 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ S2 ∷ []) wn00464 ▸ done

  b27 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ Sw23 ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (Sw23 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b27 = at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b28 : Chain (Sw23 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ Sw23 ∷ S2 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b28 = at 1 13 (CS02 ∷ []) wn01971 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 13 2 (Sw23 ∷ S2 ∷ []) wn00464 ▸ done

  b29 : Chain (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ Sw23 ∷ S2 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ Sw23 ∷ ι ∷ S0⁻ ∷ ι ∷ S2⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S2 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b29 = at 12 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 11 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ S2⁻ ∷ []) wn00689 ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b30 : Chain (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ Sw23 ∷ ι ∷ S0⁻ ∷ ι ∷ S2⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S2 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b30 = at 4 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 3 13 (CS02⁻ ∷ []) wn02058 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

-- resp TOFF123 CS01 TOFF123 CSd01: 1 steps
lem-resp-TOFF123-CS01-TOFF123-CSd01 : ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-resp-TOFF123-CS01-TOFF123-CSd01 = run b0
  where
  b0 : Chain (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 4 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-S2-at1203) ▸ done

-- resp TOFF023 CS01 TOFF023 CSd01: 1 steps
lem-resp-TOFF023-CS01-TOFF023-CSd01 : ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-resp-TOFF023-CS01-TOFF023-CSd01 = run b0
  where
  b0 : Chain (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-S2-at0213) ▸ done

-- S2 @1203 ^-1: 9 steps
lem-S2-at1203-ᵖ-1 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ
lem-S2-at1203-ᵖ-1 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ CS13⁻ ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ [])
  b0 = at 4 0 (Toff123 ∷ Toff123 ∷ []) wn02041 ▸
       at 5 0 (CS01 ∷ CS01⁻ ∷ []) wn02042 ▸
       at 6 0 (Toff123 ∷ Toff123 ∷ []) wn02041 ▸
       at 7 0 (CS01⁻ ∷ CS01 ∷ []) wn01694 ▸
       at 4 4 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-S2-at1203) ▸
       at 3 2 [] wn01380 ▸
       at 2 2 [] wn01379 ▸
       at 1 2 [] wn01380 ▸ done

  b1 : Chain (CS13 ∷ CS13⁻ ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ [])
  b1 = at 0 2 [] wn01381 ▸ done

-- resp S0 K0 CS02 TOFF013 CSd02 TOFF013 Kd0 Sd0: 1 steps
lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 : ⟪ (S0 ∷ K0 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 = run b0
  where
  b0 : Chain (S0 ∷ K0 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b0 = at 2 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-ᵖ-1) ▸ done

-- S2 @2103 ^-1: 9 steps
lem-S2-at2103-ᵖ-1 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) ⟫ʷ
lem-S2-at2103-ᵖ-1 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ CS23⁻ ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ [])
  b0 = at 4 0 (Toff213 ∷ Toff213 ∷ []) wn02051 ▸
       at 5 0 (CS02 ∷ CS02⁻ ∷ []) wn01357 ▸
       at 6 0 (Toff213 ∷ Toff213 ∷ []) wn02051 ▸
       at 7 0 (CS02⁻ ∷ CS02 ∷ []) wn00231 ▸
       at 4 4 (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-S2-at2103) ▸
       at 3 2 [] wn01524 ▸
       at 2 2 [] wn01523 ▸
       at 1 2 [] wn01524 ▸ done

  b1 : Chain (CS23 ∷ CS23⁻ ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ []) (CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ [])
  b1 = at 0 2 [] wn01525 ▸ done

-- Bar(SSKSKK;3,2->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = run b0
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  b0 = at 0 60 (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3) ▸ done

-- Bar(SSSKSS;3,2->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01 X3: 1 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3 = run b0
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  b0 = at 0 62 (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-X3) ▸ done
