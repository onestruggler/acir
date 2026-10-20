{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D715 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00029 ; wn00031 ; wn00076 ; wn00140 ; wn00142 ; wn00173 ; wn00175)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00388)
open import Examples.Groups.Clifford+CS.Four.Wins.W14 using (wn00872)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01376 ; wn01377 ; wn01378 ; wn01379 ; wn01380 ; wn01381)
open import Examples.Groups.Clifford+CS.Four.Wins.W28 using (wn01495 ; wn01499)
open import Examples.Groups.Clifford+CS.Four.Wins.W29 using (wn01520 ; wn01521 ; wn01522 ; wn01523 ; wn01524 ; wn01525)
open import Examples.Groups.Clifford+CS.Four.Wins.W43 using (wn02045 ; wn02046)
open import Examples.Groups.Clifford+CS.Four.Wins.W44 using (wn02102 ; wn02103 ; wn02130 ; wn02131 ; wn02132 ; wn02133 ; wn02134 ; wn02135 ; wn02136 ; wn02137 ; wn02138 ; wn02139 ; wn02140 ; wn02141 ; wn02142 ; wn02143)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D510 using (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D513 using (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D515 using (lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 ; lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 ; lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023)
open import Examples.Groups.Clifford+CS.Four.D.D516 using (lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 ; lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 ; lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 ; lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 ; lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203)
open import Examples.Groups.Clifford+CS.Four.D.D517 using (lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 ; lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 ; lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 ; lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103)
open import Examples.Groups.Clifford+CS.Four.D.D539 using (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D541 using (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D597 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 ; lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 ; lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 ; lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 ; lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2)
open import Examples.Groups.Clifford+CS.Four.D.D651 using (lem-S2)
open import Examples.Groups.Clifford+CS.Four.D.D701 using (lem-S2-at0213-ᵖ-1 ; lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D702 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 ; lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 ; lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 ; lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D703 using (lem-S2-at1023-ᵖ-1 ; lem-S2-at1203-ᵖ-1 ; lem-S2-at2013-ᵖ-1 ; lem-S2-at2103-ᵖ-1 ; lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 ; lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 7 (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2) ▸
       at 3 5 (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1) ▸
       at 4 5 (CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13) ▸
       at 5 7 (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2) ▸
       at 8 5 (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1) ▸
       at 9 5 (CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13) ▸ done

-- pass [X2 CSd21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸
       at 1 5 (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn02130 ▸
       at 9 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 3 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 7 11 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn02131 ▸
       at 9 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸ done

-- pass [X2 CK21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01495 ▸
       at 1 5 (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn02132 ▸
       at 15 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 12 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 9 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 3 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 7 17 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn02133 ▸ done

  b1 : Chain (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b1 = at 9 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01495 ▸ done

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 10 (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸ done

-- pass [X3 CS32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = trans (run b0) (run b1)
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ Toff201 ∷ [])
  b0 = at 0 0 (CS23 ∷ CS23⁻ ∷ []) wn01520 ▸
       at 1 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 2 0 (CS23⁻ ∷ CS23 ∷ []) wn01522 ▸
       at 3 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 4 7 (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23) ▸
       at 10 2 [] wn01523 ▸
       at 9 2 [] wn01524 ▸
       at 8 2 [] wn01525 ▸ done

  b1 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b1 = at 7 2 [] wn01524 ▸ done

-- pass [X3 CSd32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = trans (run b0) (run b1)
  where
  b0 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ Toff201 ∷ Toff201 ∷ [])
  b0 = at 0 0 (CS23 ∷ CS23⁻ ∷ []) wn01520 ▸
       at 1 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 2 0 (CS23⁻ ∷ CS23 ∷ []) wn01522 ▸
       at 3 0 (Toff201 ∷ Toff201 ∷ []) wn01521 ▸
       at 4 7 (X3 ∷ CS23⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23) ▸
       at 10 2 [] wn01523 ▸
       at 9 2 [] wn01524 ▸
       at 8 2 [] wn01525 ▸ done

  b1 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ Toff201 ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  b1 = at 7 2 [] wn01524 ▸ done

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = run b0
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 0 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3) ▸
       at 3 5 (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02) ▸
       at 4 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3) ▸
       at 7 5 (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02) ▸ done

-- pass [X3 CS31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ Toff102 ∷ [])
  b0 = at 0 0 (CS13 ∷ CS13⁻ ∷ []) wn01376 ▸
       at 1 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 2 0 (CS13⁻ ∷ CS13 ∷ []) wn01378 ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 4 7 (X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 2 [] wn01379 ▸
       at 9 2 [] wn01380 ▸
       at 8 2 [] wn01381 ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  b1 = at 7 2 [] wn01380 ▸ done

-- pass [X3 CSd30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 57 steps
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b1 = at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn02134 ▸
       at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b2 = at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ S0 ∷ Sw23 ∷ [])
  b3 = at 11 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 2 [] wn00003 ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸ done

  b4 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b4 = at 19 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 18 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 17 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 16 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 15 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b5 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ [])
  b5 = at 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 13 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn02135 ▸ done

  b6 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ [])
  b6 = at 8 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b7 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b7 = at 15 2 [] wn00003 ▸ done

-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 75 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b1 = at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn02136 ▸
       at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b2 = at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b3 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 16 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b4 = at 17 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 19 2 [] wn00003 ▸
       at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b5 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b5 = at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 25 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 24 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 23 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 22 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 21 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸ done

  b6 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b6 = at 20 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 19 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 16 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸ done

  b7 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b7 = at 14 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b8 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b8 = at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 19 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn02137 ▸
       at 8 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b9 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b9 = at 13 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 2 [] wn00003 ▸ done

-- pass [X3 CK30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 75 steps
lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b1 = at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn02138 ▸
       at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b2 = at 5 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b3 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 16 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b4 = at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 19 2 [] wn00003 ▸
       at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b5 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b5 = at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 25 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 24 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 23 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 22 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸ done

  b6 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b6 = at 20 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 19 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 18 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 16 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸ done

  b7 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b7 = at 14 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b8 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b8 = at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 19 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn02139 ▸
       at 8 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b9 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b9 = at 13 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 2 [] wn00003 ▸ done

-- pass [X3 CS30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 57 steps
lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b1 = at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn02140 ▸
       at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ [])
  b2 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ S0 ∷ Sw23 ∷ [])
  b3 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 2 [] wn00003 ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸ done

  b4 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ [])
  b4 = at 19 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 18 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 17 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 16 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b5 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ [])
  b5 = at 12 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 13 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn02141 ▸ done

  b6 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ [])
  b6 = at 8 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b7 : Chain (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b7 = at 15 2 [] wn00003 ▸ done

-- pass [X3 CSd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done

-- pass [X3 CKd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done

-- pass [X3 CS32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = run b0
  where
  b0 : Chain (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  b0 = at 0 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3) ▸
       at 3 5 (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2) ▸
       at 4 5 (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02) ▸
       at 5 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3) ▸
       at 8 5 (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2) ▸
       at 9 5 (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02) ▸ done

-- pass [X3 CK32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lem-S2-at0213-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done

-- pass [X3 CK30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203) ▸
       at 0 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2013-ᵖ-1) ▸ done

-- pass [X3 CS30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203) ▸
       at 0 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2013-ᵖ-1) ▸ done

-- pass [X3 CSd30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203) ▸
       at 0 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2013-ᵖ-1) ▸ done

-- pass [X3 CKd30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ []) (lem-S2-at2013-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203) ▸
       at 0 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2013-ᵖ-1) ▸ done

-- pass [X2 CSd20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸
       at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b1 : Chain (X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] wn00031 ▸
       at 1 5 (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn02102 ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 3 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 11 (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn02103 ▸ done

  b2 : Chain (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ [])
  b2 = at 13 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 12 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 11 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 10 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 10 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸
       at 9 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b3 = at 11 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 12 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 13 2 [] wn00031 ▸ done

-- pass [X2 CK20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 29 steps
lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ Sw01 ∷ CK21 ∷ X2 ∷ Sw01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01495 ▸
       at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b1 : Chain (X3 ∷ X2 ∷ Sw01 ∷ CK21 ∷ X2 ∷ Sw01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  b1 = at 2 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] wn00031 ▸
       at 1 5 (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn02045 ▸
       at 15 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b2 : Chain (X3 ∷ S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ Sw01 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ [])
  b2 = at 3 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 17 (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn02046 ▸
       at 13 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 12 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 11 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 10 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 10 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01495 ▸ done

  b3 : Chain (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ Sw01 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b3 = at 9 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 12 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 13 2 [] wn00031 ▸ done

-- pass [X3 CSd30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1023-ᵖ-1) ▸ done

-- pass [X3 CKd30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1023-ᵖ-1) ▸ done

-- pass [X3 CK30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1023-ᵖ-1) ▸ done

-- pass [X3 CS30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 3 4 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ []) (lem-S2-at1023-ᵖ-1) ▸
       at 0 7 (CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1023-ᵖ-1) ▸ done

-- pass [X1 CKd10 X1] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b0 = at 7 0 (X1 ∷ X1 ∷ []) wn00872 ▸
       at 8 0 (CK10 ∷ CK10⁻ ∷ []) wn02142 ▸
       at 9 0 (X1 ∷ X1 ∷ []) wn00872 ▸
       at 3 7 (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 2 [] wn00388 ▸
       at 1 2 [] wn02143 ▸
       at 0 2 [] wn00388 ▸ done

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 0 14 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 10 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-S2) ▸ done

-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 14 (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

-- pass [X2 CK21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ Toff102 ∷ [])
  b0 = at 0 0 (CS13 ∷ CS13⁻ ∷ []) wn01376 ▸
       at 1 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 2 0 (CS13⁻ ∷ CS13 ∷ []) wn01378 ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 4 7 (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 2 [] wn01379 ▸
       at 9 2 [] wn01380 ▸
       at 8 2 [] wn01381 ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b1 = at 7 2 [] wn01380 ▸ done

-- resp S0 K0 CS01 TOFF023 CSd01 TOFF023 Kd0 Sd0: 1 steps
lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 : ⟪ (S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 = run b0
  where
  b0 : Chain (S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b0 = at 2 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸ done

-- resp S1 K1 CS01 TOFF123 CSd01 TOFF123 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 : ⟪ (S1 ∷ K1 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 = run b0
  where
  b0 : Chain (S1 ∷ K1 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ [])
  b0 = at 2 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done

-- resp S2 K2 CS12 TOFF203 CSd12 TOFF203 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 : ⟪ (S2 ∷ K2 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 = run b0
  where
  b0 : Chain (S2 ∷ K2 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ Toff203 ∷ K2⁻ ∷ S2⁻ ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ [])
  b0 = at 2 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2013-ᵖ-1) ▸ done

-- resp S2 K2 CS02 TOFF213 CSd02 TOFF213 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 : ⟪ (S2 ∷ K2 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 = run b0
  where
  b0 : Chain (S2 ∷ K2 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ K2⁻ ∷ S2⁻ ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ [])
  b0 = at 2 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2103-ᵖ-1) ▸ done

-- resp S1 K1 CS12 TOFF103 CSd12 TOFF103 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 : ⟪ (S1 ∷ K1 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 = run b0
  where
  b0 : Chain (S1 ∷ K1 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ [])
  b0 = at 2 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1023-ᵖ-1) ▸ done
