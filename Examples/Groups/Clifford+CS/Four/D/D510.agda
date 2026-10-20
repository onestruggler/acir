{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D510 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00002 ; wn00003 ; wn00005 ; wn00006 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00011 ; wn00012 ; wn00013 ; wn00014 ; wn00015 ; wn00016 ; wn00017 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00032 ; wn00033 ; wn00042 ; wn00043 ; wn00045 ; wn00048 ; wn00053 ; wn00054 ; wn00055 ; wn00056 ; wn00065 ; wn00074 ; wn00076 ; wn00080 ; wn00090 ; wn00096 ; wn00097 ; wn00111 ; wn00116 ; wn00118 ; wn00205)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00225 ; wn00227 ; wn00231 ; wn00254 ; wn00271 ; wn00390)
open import Examples.Groups.Clifford+CS.Four.Wins.W03 using (wn00469)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01336 ; wn01337 ; wn01338 ; wn01339 ; wn01340 ; wn01341 ; wn01342 ; wn01343 ; wn01344 ; wn01345 ; wn01346 ; wn01347 ; wn01348 ; wn01349 ; wn01350 ; wn01351 ; wn01352 ; wn01353 ; wn01354 ; wn01355 ; wn01356 ; wn01357 ; wn01358)
open import Examples.Groups.Clifford+CS.Four.D.D001 using (lem-CCZ023-T ; lem-CCZ123-CX30 ; lem-CCZ312-CCZ012 ; lem-CS13-passes-T ; lem-N23-T ; lem-comm-CCZ012-CCZ013)
open import Examples.Groups.Clifford+CS.Four.D.D002 using (lem-CS12-passes-T ; lem-comm-CCZ012-CSd03 ; lem-comm-CCZ123-CCZ023 ; lem-comm-CCZ123-CSd02 ; lem-comm-CCZ123-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D003 using (lem-CZ13-passes-T ; lem-comm-CCZ012-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D004 using (lem-comm-CCZ013-CCZ012 ; lem-comm-CCZ013-CS02 ; lem-comm-CCZ013-CS12)
open import Examples.Groups.Clifford+CS.Four.D.D005 using (lem-CCZ023-passes-CX31 ; lem-comm-CCZ023-CCZ012)
open import Examples.Groups.Clifford+CS.Four.D.D006 using (lem-Rk)
open import Examples.Groups.Clifford+CS.Four.D.D007 using (lem-SW13-Rk)
open import Examples.Groups.Clifford+CS.Four.D.D008 using (lem-PUinv ; lem-pass-CS12-vs-CS03 ; lem-pass-CSd13-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D009 using (lem-comm-CCZ012-CS13 ; lem-comm-CCZ012-CSd13 ; lem-comm-CCZ013-CSd12 ; lem-comm-CCZ013-CZ02 ; lem-pass-CS13-vs-CS02 ; lem-pass-CSd02-vs-CS13 ; lem-pass-CSd02-vs-CSd13 ; lem-pass-S2-vs-CS13 ; lem-pass-S2-vs-CSd13 ; lem-pass-Sd2-vs-CS13 ; lem-pass-Sd2-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D010 using (lem-pass-CS12-vs-CSd03 ; lem-pass-CS12-vs-K0 ; lem-pass-CS12-vs-Kd0 ; lem-pass-CS12-vs-TOFF012 ; lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CS30-X3-vs-CS02 ; lem-pass-X3-CS30-X3-vs-CSd02 ; lem-pass-X3-CS30-X3-vs-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D011 using (lem-pass-X3-CK30-X3-vs-CS12 ; lem-pass-X3-CK30-X3-vs-CSd12 ; lem-pass-X3-CK30-X3-vs-TOFF103 ; lem-pass-X3-CKd30-X3-vs-CS12 ; lem-pass-X3-CKd30-X3-vs-CSd12 ; lem-pass-X3-CKd30-X3-vs-TOFF103 ; lem-pass-X3-CS30-X3-vs-CS12 ; lem-pass-X3-CS30-X3-vs-CSd12 ; lem-pass-X3-CS30-X3-vs-TOFF103 ; lem-pass-X3-CSd30-X3-vs-CS12 ; lem-pass-X3-CSd30-X3-vs-CSd12 ; lem-pass-X3-CSd30-X3-vs-TOFF103)

-- T-CZ03-T: 145 steps
lem-T-CZ03-T : ⟪ (Toff012 ∷ CZ03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ03 ∷ []) ⟫ʷ
lem-T-CZ03-T = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (Toff012 ∷ CZ03 ∷ Toff012 ∷ []) (K0 ∷ CCZ012 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) wn00053 ▸
       at 4 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) wn00053 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 3 (CX20 ∷ []) wn01336 ▸ done

  b1 : Chain (K0 ∷ CCZ012 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ CX30 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 0 (CX20 ∷ CX20 ∷ []) wn00002 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (K0 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ CX30 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ CX30 ∷ CCZ012 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b2 = at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K0 ∷ CX30 ∷ CX30 ∷ CCZ012 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b3 = at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CX30 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b4 = at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b5 = at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸ done

  b6 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ Sw12 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b6 = at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 4 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ Sw12 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b7 = at 5 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b8 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b9 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b9 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 4 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b10 = at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b11 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b11 = at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b12 : Chain (K0 ∷ CX30 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw01 ∷ CS02 ∷ CCZ023 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b12 = at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00014 ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸ done

  b13 : Chain (K0 ∷ CX30 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Sw01 ∷ CS02 ∷ CCZ023 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b13 = at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b14 : Chain (K0 ∷ CX30 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ CCZ012 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b14 = at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b15 : Chain (K0 ∷ CX30 ∷ CCZ012 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CX30 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b15 = at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (K0 ∷ CX30 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ012 ∷ K0⁻ ∷ []) (CCZ123 ∷ K0 ∷ CX30 ∷ K0⁻ ∷ [])
  b16 = at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 2 2 (CCZ123 ∷ CCZ012 ∷ []) (sym lem-CCZ312-CCZ012) ▸
       at 3 2 [] wn00032 ▸
       at 2 1 (CCZ123 ∷ []) wn01337 ▸
       at 1 2 (CCZ123 ∷ CX30 ∷ []) (sym lem-CCZ123-CX30) ▸
       at 0 2 (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ)) ▸ done

  b17 : Chain (CCZ123 ∷ K0 ∷ CX30 ∷ K0⁻ ∷ []) (CCZ123 ∷ CZ03 ∷ Sw23 ∷ Sw23 ∷ [])
  b17 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 3 (CZ02 ∷ []) wn01338 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (CCZ123 ∷ CZ03 ∷ Sw23 ∷ Sw23 ∷ []) (CCZ123 ∷ CZ03 ∷ [])
  b18 = at 2 2 [] wn00003 ▸ done

-- E-T: 5 steps
lem-E-T : ⟪ (CCZ123 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-E-T = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ [])
  b0 = at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) wn00053 ▸
       at 0 2 (K0 ∷ CCZ123 ∷ []) (sym (low₁-comm (K) (CCZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ123 ∷ []) (lem-CCZ312-CCZ012) ▸
       at 2 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (low₁-comm ((K • iI)) (CCZ))) ▸
       at 0 3 (Toff012 ∷ []) wn00055 ▸ done

-- T-T13: 111 steps
lem-T-T13 : ⟪ (Toff012 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-T13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Toff012 ∷ Toff013 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) wn00053 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸ done

  b2 : Chain (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ [])
  b3 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) wn00053 ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ [])
  b4 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ [])
  b5 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K0 ∷ CCZ012 ∷ K0⁻ ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) (K0 ∷ CCZ013 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b6 = at 9 2 [] wn00003 ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 6 2 [] wn00003 ▸
       at 2 2 [] wn01339 ▸
       at 1 2 (CCZ013 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CCZ013) ▸ done

  b7 : Chain (K0 ∷ CCZ013 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b7 = at 2 0 (K0⁻ ∷ K0 ∷ []) wn00054 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b8 : Chain (K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b8 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b9 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ Sw23 ∷ CCZ012 ∷ K0⁻ ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b9 = at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (K0 ∷ Sw23 ∷ CCZ012 ∷ K0⁻ ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b10 = at 0 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 1 3 (Toff012 ∷ []) wn00055 ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b11 : Chain (K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b11 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b12 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ [])
  b12 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b13 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff013 ∷ Toff012 ∷ [])
  b13 = at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸
       at 1 3 (Toff012 ∷ []) wn00055 ▸ done

-- N23-PP3: 150 steps
lem-N23-PP3 : ⟪ (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-N23-PP3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CX23 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX23 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ [])
  b0 = at 4 0 (CX23 ∷ CX23 ∷ []) wn00042 ▸
       at 3 0 (CX23 ∷ CX23 ∷ []) wn00042 ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) wn00042 ▸
       at 0 3 (Toff012 ∷ []) (lem-N23-T) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b1 : Chain (Toff012 ∷ CX23 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX23 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CCZ123 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ [])
  b1 = at 3 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 2 3 (CS13 ∷ CS12 ∷ CCZ123 ∷ []) wn01340 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b2 : Chain (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CCZ123 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ [])
  b2 = at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b3 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ [])
  b3 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b4 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ [])
  b4 = at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b5 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CX23 ∷ Toff012 ∷ CX23 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ CX23 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX23 ∷ Sw01 ∷ [])
  b5 = at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 4 3 (Toff012 ∷ []) (lem-N23-T) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b6 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ CX23 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX23 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CS12⁻ ∷ CS13⁻ ∷ Sw01 ∷ [])
  b6 = at 7 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸
       at 6 3 (CCZ123 ∷ CS12⁻ ∷ CS13⁻ ∷ []) wn01341 ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b7 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CS12⁻ ∷ CS13⁻ ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CS12⁻ ∷ CS13⁻ ∷ Sw01 ∷ [])
  b7 = at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b8 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CS12⁻ ∷ CS13⁻ ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ CS13⁻ ∷ Sw01 ∷ [])
  b8 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS12⁻ ∷ CS13⁻ ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ CCZ023 ∷ CS02⁻ ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ [])
  b9 = at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b10 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ Toff012 ∷ CCZ023 ∷ CS02⁻ ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ [])
  b10 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 3 2 (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) (lem-CCZ023-T) ▸
       at 4 2 (CCZ123 ∷ CCZ023 ∷ []) (sym lem-comm-CCZ123-CCZ023) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ [])
  b11 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b12 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ [])
  b12 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00031 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸ done

  b13 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ [])
  b13 = at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b14 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ [])
  b14 = at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ [])
  b15 = at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸ done

  b16 : Chain (Toff012 ∷ CS03 ∷ CS02 ∷ Toff012 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CS02⁻ ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ CS02⁻ ∷ CCZ123 ∷ CS03⁻ ∷ [])
  b16 = at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00033 ▸
       at 5 2 [] wn00031 ▸
       at 2 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) wn00469 ▸
       at 6 2 (CS02⁻ ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CSd02) ▸ done

  b17 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ CS02⁻ ∷ CCZ123 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CCZ123 ∷ [])
  b17 = at 5 2 (CS02⁻ ∷ CCZ012 ∷ []) wn00254 ▸
       at 4 2 (CS02⁻ ∷ CS12 ∷ []) wn00080 ▸
       at 3 2 [] wn01342 ▸
       at 5 2 (CS03⁻ ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CSd03) ▸
       at 4 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd03) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CCZ123 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ [])
  b18 = at 4 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 5 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

-- CS12 passes PP3: 20 steps
lem-CS12-passes-PP3 : ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-passes-PP3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS12 ∷ []) (lem-CS12-passes-T) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 3 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 4 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 7 2 [] wn00003 ▸
       at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS12 ∷ []) (lem-CS12-passes-T) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 5 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ [])
  b2 = at 6 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

-- CS13 passes PP3: 24 steps
lem-CS13-passes-PP3 : ⟪ (CS13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-CS13-passes-PP3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS13 ∷ []) (lem-CS13-passes-T) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (CS02 ∷ CS12 ∷ []) wn00205 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b1 = at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (Toff012 ∷ CS13 ∷ []) (lem-CS13-passes-T) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 2 (CS02⁻ ∷ CS12 ∷ []) wn00080 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

-- CCZ012 passes PP3: 13 steps
lem-CCZ012-passes-PP3 : ⟪ (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-CCZ012-passes-PP3 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) wn01343 ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CZ23 ∷ []) wn00096 ▸
       at 4 2 (CS01 ∷ CZ23 ∷ []) (sym (low-comm (CS) (CZ))) ▸
       at 5 2 (Sw12 ∷ CZ13 ∷ []) wn00097 ▸
       at 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ [])
  b1 = at 8 2 [] wn00003 ▸
       at 2 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS03 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS03) ▸
       at 2 3 (Toff012 ∷ CCZ012 ∷ []) wn01344 ▸
       at 3 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd03) ▸ done

-- CZ13 passes PP3: 24 steps
lem-CZ13-passes-PP3 : ⟪ (CZ13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ []) ⟫ʷ
lem-CZ13-passes-PP3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CZ13 ∷ []) (lem-CZ13-passes-T) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (CS02 ∷ CZ12 ∷ []) wn01345 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CZ13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b1 = at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (Toff012 ∷ CZ13 ∷ []) (lem-CZ13-passes-T) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CZ13 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 2 (CS02⁻ ∷ CZ12 ∷ []) wn01346 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

-- T1-CZ13-T1: 75 steps
lem-T1-CZ13-T1 : ⟪ (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ13 ∷ []) ⟫ʷ
lem-T1-CZ13-T1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) (K1 ∷ CX31 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b0 = at 0 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) wn01347 ▸
       at 4 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) wn01347 ▸
       at 2 3 (CX31 ∷ []) wn01348 ▸
       at 1 0 (CX31 ∷ CX31 ∷ []) wn00111 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CX31 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b1 = at 9 2 [] wn00014 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸ done

  b2 : Chain (K1 ∷ CX31 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b2 = at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CX32 ∷ []) wn00013 ▸
       at 3 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸ done

  b3 : Chain (K1 ∷ CX31 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b3 = at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00017 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K1 ∷ CX31 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b4 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K1 ∷ CX31 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b5 = at 9 2 [] wn00003 ▸
       at 3 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K1 ∷ CX31 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b6 = at 7 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 10 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b7 : Chain (K1 ∷ CX31 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ CX31 ∷ CCZ012 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b7 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (K1 ∷ CX31 ∷ CCZ012 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ CCZ012 ∷ K1⁻ ∷ []) (Sw01 ∷ CCZ123 ∷ K0 ∷ Sw01 ∷ CX31 ∷ K1⁻ ∷ [])
  b8 = at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00014 ▸
       at 3 2 (CCZ012 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CCZ012) ▸
       at 2 2 [] wn00032 ▸
       at 1 2 (CCZ023 ∷ CX31 ∷ []) (sym lem-CCZ023-passes-CX31) ▸
       at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 1 2 (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ)) ▸ done

  b9 : Chain (Sw01 ∷ CCZ123 ∷ K0 ∷ Sw01 ∷ CX31 ∷ K1⁻ ∷ []) (CCZ023 ∷ CZ13 ∷ [])
  b9 = at 2 2 (Sw01 ∷ K1 ∷ []) wn00118 ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CZ13 ∷ []) wn01349 ▸ done

-- ROT-form: 7 steps
lem-ROT-form : ⟪ (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) ⟫ʷ
lem-ROT-form = run b0
  where
  b0 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (K0 ∷ K0⁻ ∷ []) wn00116 ▸
       at 6 0 (K0 ∷ K0⁻ ∷ []) wn00116 ▸
       at 1 6 (CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ []) (lem-Rk) ▸
       at 5 0 (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn01350 ▸
       at 1 0 (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn01350 ▸
       at 4 10 (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) (lem-SW13-Rk) ▸
       at 4 4 (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (sym lem-PUinv) ▸ done

-- pass [CCZ013] [CCZ012]: 1 steps
lem-pass-CCZ013-vs-CCZ012 : ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CCZ012 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CCZ012 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CCZ012) ▸ done

-- pass [CCZ023] [CCZ012]: 1 steps
lem-pass-CCZ023-vs-CCZ012 : ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CCZ012 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ [])
  b0 = at 0 2 (CCZ012 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CCZ012) ▸ done

-- pass [CCZ012] [CS03]: 1 steps
lem-pass-CCZ012-vs-CS03 : ⟪ (CCZ012 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS03 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS03 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS03) ▸ done

-- pass [CCZ013] [CS02]: 1 steps
lem-pass-CCZ013-vs-CS02 : ⟪ (CCZ013 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS02 = run b0
  where
  b0 : Chain (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CS02 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS02) ▸ done

-- pass [CCZ013] [CZ02]: 1 steps
lem-pass-CCZ013-vs-CZ02 : ⟪ (CCZ013 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ02 = run b0
  where
  b0 : Chain (CCZ013 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CZ02 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CZ02) ▸ done

-- pass [CCZ013] [CS12]: 1 steps
lem-pass-CCZ013-vs-CS12 : ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS12 = run b0
  where
  b0 : Chain (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CS12 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS12) ▸ done

-- pass [CCZ013] [CSd12]: 1 steps
lem-pass-CCZ013-vs-CSd12 : ⟪ (CCZ013 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd12 = run b0
  where
  b0 : Chain (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd12) ▸ done

-- pass [CS02] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ [])
  b0 = at 0 2 (Toff102 ∷ CS02 ∷ []) wn01351 ▸
       at 1 2 (CS13 ∷ CS02 ∷ []) (sym lem-pass-CS13-vs-CS02) ▸
       at 2 2 (Toff102 ∷ CS02 ∷ []) wn01351 ▸
       at 3 2 (CS13⁻ ∷ CS02 ∷ []) (sym lem-pass-CSd13-vs-CS02) ▸ done

-- pass [CSd02] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ [])
  b0 = at 0 2 (Toff102 ∷ CS02⁻ ∷ []) wn01352 ▸
       at 1 2 (CS13 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS13) ▸
       at 2 2 (Toff102 ∷ CS02⁻ ∷ []) wn01352 ▸
       at 3 2 (CS13⁻ ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CSd13) ▸ done

-- pass [CCZ012] [CSd03]: 1 steps
lem-pass-CCZ012-vs-CSd03 : ⟪ (CCZ012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd03 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd03) ▸ done

-- pass [CCZ012] [CS13]: 1 steps
lem-pass-CCZ012-vs-CS13 : ⟪ (CCZ012 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS13 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS13) ▸ done

-- pass [CCZ012] [CSd13]: 1 steps
lem-pass-CCZ012-vs-CSd13 : ⟪ (CCZ012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd13 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd13) ▸ done

-- pass [S2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ [])
  b0 = at 0 2 (Toff102 ∷ S2 ∷ []) wn01353 ▸
       at 1 2 (CS13 ∷ S2 ∷ []) (lem-pass-S2-vs-CS13) ▸
       at 2 2 (Toff102 ∷ S2 ∷ []) wn01353 ▸
       at 3 2 (CS13⁻ ∷ S2 ∷ []) (lem-pass-S2-vs-CSd13) ▸ done

-- pass [Sd2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ [])
  b0 = at 0 2 (Toff102 ∷ S2⁻ ∷ []) wn01354 ▸
       at 1 2 (CS13 ∷ S2⁻ ∷ []) (lem-pass-Sd2-vs-CS13) ▸
       at 2 2 (Toff102 ∷ S2⁻ ∷ []) wn01354 ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (lem-pass-Sd2-vs-CSd13) ▸ done

-- pass [CS12] [TOFF012 CS03 TOFF012]: 3 steps
lem-pass-CS12-vs-TOFF012-CS03-TOFF012 : ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-TOFF012-CS03-TOFF012 = run b0
  where
  b0 : Chain (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS12 ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS12 ∷ []) wn00090 ▸
       at 1 2 (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03) ▸
       at 2 2 (Toff012 ∷ CS12 ∷ []) wn00090 ▸ done

-- pass [X3 CKd30 X3] [TOFF012 CS03 TOFF012 CSd03]: 19 steps
lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 7 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 0 (CK20 ∷ CK20⁻ ∷ []) wn01355 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b1 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ Sw23 ∷ CK20⁻ ∷ CK20 ∷ Sw23 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b1 = at 9 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 3 7 (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 2 [] wn00390 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b2 : Chain (X3 ∷ Sw23 ∷ CK20⁻ ∷ CK20 ∷ Sw23 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b2 = at 2 2 [] wn01356 ▸
       at 1 2 [] wn00003 ▸
       at 0 2 [] wn00390 ▸ done

-- pass [CS12] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 6 steps
lem-pass-CS12-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (CS12 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = run b0
  where
  b0 : Chain (CS12 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ [])
  b0 = at 0 2 (K0⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-Kd0) ▸
       at 1 2 (Toff012 ∷ CS12 ∷ []) (lem-pass-CS12-vs-TOFF012) ▸
       at 2 2 (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (lem-pass-CS12-vs-TOFF012) ▸
       at 4 2 (CS03⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd03) ▸
       at 5 2 (K0 ∷ CS12 ∷ []) (lem-pass-CS12-vs-K0) ▸ done

-- pass [CS12] [Kd0 CS03 TOFF012 CSd03 TOFF012 K0]: 6 steps
lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : ⟪ (CS12 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = run b0
  where
  b0 : Chain (CS12 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CS12 ∷ [])
  b0 = at 0 2 (K0⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-Kd0) ▸
       at 1 2 (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03) ▸
       at 2 2 (Toff012 ∷ CS12 ∷ []) (lem-pass-CS12-vs-TOFF012) ▸
       at 3 2 (CS03⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd03) ▸
       at 4 2 (Toff012 ∷ CS12 ∷ []) (lem-pass-CS12-vs-TOFF012) ▸
       at 5 2 (K0 ∷ CS12 ∷ []) (lem-pass-CS12-vs-K0) ▸ done

-- pass [X3 CS30 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF013-CS02-TOFF013-CSd02 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff013 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF013) ▸
       at 1 4 (CS02 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS02) ▸
       at 2 4 (Toff013 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF013) ▸
       at 3 4 (CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CSd02) ▸ done

-- pass [CCZ123] [CSd03]: 1 steps
lem-pass-CCZ123-vs-CSd03 : ⟪ (CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CSd03 = run b0
  where
  b0 : Chain (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CSd03) ▸ done

-- pass [X3 CK30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 0 (CS02 ∷ CS02⁻ ∷ []) wn01357 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 0 (CS02⁻ ∷ CS02 ∷ []) wn00231 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 7 (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 11 2 [] wn01358 ▸
       at 10 2 [] wn00003 ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ Toff012 ∷ [])
  b3 = at 9 2 [] wn00227 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 9 2 [] wn01342 ▸
       at 8 2 [] wn00003 ▸ done

  b4 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b4 = at 7 2 [] wn00227 ▸ done

-- pass [X3 CSd30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF103) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS12) ▸
       at 2 4 (Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF103) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CSd12) ▸ done

-- pass [X3 CKd30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF103) ▸
       at 1 4 (CS12 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS12) ▸
       at 2 4 (Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF103) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CSd12) ▸ done

-- pass [X3 CK30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF103) ▸
       at 1 4 (CS12 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS12) ▸
       at 2 4 (Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF103) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CSd12) ▸ done

-- pass [X3 CS30 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF103) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS12) ▸
       at 2 4 (Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF103) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CSd12) ▸ done
