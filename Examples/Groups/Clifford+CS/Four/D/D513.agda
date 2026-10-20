{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D513 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00196)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00225 ; wn00390)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01352 ; wn01366 ; wn01367 ; wn01368 ; wn01369 ; wn01370 ; wn01371 ; wn01372)
open import Examples.Groups.Clifford+CS.Four.D.D002 using (lem-comm-CCZ123-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D008 using (lem-pass-S0-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D009 using (lem-pass-CS13-vs-S0 ; lem-pass-CSd13-vs-S0)
open import Examples.Groups.Clifford+CS.Four.D.D010 using (lem-pass-CS12-vs-CSd03 ; lem-pass-CSd12-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D011 using (lem-pass-X3-CSd30-X3-vs-CS02 ; lem-pass-X3-CSd30-X3-vs-CSd02 ; lem-pass-X3-CSd30-X3-vs-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D012 using (lem-comm-CCZ012-CCZ123 ; lem-pass-X2-CK20-X2-vs-CS13 ; lem-pass-X2-CK20-X2-vs-CSd13 ; lem-pass-X2-CK20-X2-vs-TOFF102 ; lem-pass-X2-CKd20-X2-vs-CS13 ; lem-pass-X2-CKd20-X2-vs-CSd13 ; lem-pass-X2-CKd20-X2-vs-TOFF102 ; lem-pass-X2-CS20-X2-vs-CS03 ; lem-pass-X2-CS20-X2-vs-CS13 ; lem-pass-X2-CS20-X2-vs-CSd03 ; lem-pass-X2-CS20-X2-vs-CSd13 ; lem-pass-X2-CS20-X2-vs-TOFF012 ; lem-pass-X2-CS20-X2-vs-TOFF102 ; lem-pass-X2-CSd20-X2-vs-CS13 ; lem-pass-X2-CSd20-X2-vs-CSd13 ; lem-pass-X2-CSd20-X2-vs-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D013 using (lem-comm-CCZ023-CS01 ; lem-comm-CCZ023-CSd13 ; lem-pass-S0-vs-CS01 ; lem-pass-S0-vs-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D014 using (lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS31-X3-vs-CS02 ; lem-pass-X3-CS31-X3-vs-CS12 ; lem-pass-X3-CS31-X3-vs-CSd12 ; lem-pass-X3-CS31-X3-vs-TOFF103)
open import Examples.Groups.Clifford+CS.Four.D.D015 using (lem-pass-S0-vs-CS12 ; lem-pass-S0-vs-CSd12 ; lem-pass-X1-CS10-X1-vs-TOFF012 ; lem-pass-X2-CK21-X2-vs-CS03 ; lem-pass-X2-CK21-X2-vs-CSd03 ; lem-pass-X2-CK21-X2-vs-TOFF012 ; lem-pass-X2-CKd21-X2-vs-CS03 ; lem-pass-X2-CKd21-X2-vs-CSd03 ; lem-pass-X2-CKd21-X2-vs-TOFF012 ; lem-pass-X2-CS21-X2-vs-CS03 ; lem-pass-X2-CS21-X2-vs-CS13 ; lem-pass-X2-CS21-X2-vs-CSd03 ; lem-pass-X2-CS21-X2-vs-CSd13 ; lem-pass-X2-CS21-X2-vs-TOFF012 ; lem-pass-X2-CS21-X2-vs-TOFF102 ; lem-pass-X2-CSd20-X2-vs-CS03 ; lem-pass-X2-CSd20-X2-vs-CSd03 ; lem-pass-X2-CSd20-X2-vs-TOFF012 ; lem-pass-X2-CSd21-X2-vs-CS03 ; lem-pass-X2-CSd21-X2-vs-CSd03 ; lem-pass-X2-CSd21-X2-vs-TOFF012 ; lem-pass-X3-CK31-X3-vs-CS02 ; lem-pass-X3-CK31-X3-vs-CSd02 ; lem-pass-X3-CK31-X3-vs-TOFF013 ; lem-pass-X3-CKd31-X3-vs-CS02 ; lem-pass-X3-CKd31-X3-vs-CSd02 ; lem-pass-X3-CKd31-X3-vs-TOFF013 ; lem-pass-X3-CS31-X3-vs-CSd02 ; lem-pass-X3-CS31-X3-vs-TOFF013 ; lem-pass-X3-CSd31-X3-vs-CS02 ; lem-pass-X3-CSd31-X3-vs-CSd02 ; lem-pass-X3-CSd31-X3-vs-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D016 using (lem-pass-X1-CS10-X1-vs-CS03 ; lem-pass-X1-CS10-X1-vs-CSd03 ; lem-pass-X2-CSd21-X2-vs-CS13 ; lem-pass-X2-CSd21-X2-vs-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102 ; lem-pass-X3-CSd31-X3-vs-CS12 ; lem-pass-X3-CSd31-X3-vs-CSd12 ; lem-pass-X3-CSd31-X3-vs-TOFF103)
open import Examples.Groups.Clifford+CS.Four.D.D019 using (lem-pass-X3-CS32-X3-vs-CS12 ; lem-pass-X3-CS32-X3-vs-CSd12 ; lem-pass-X3-CS32-X3-vs-TOFF203)
open import Examples.Groups.Clifford+CS.Four.D.D020 using (lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D021 using (lem-comm-CCZ012-CS23 ; lem-comm-CCZ013-CS23 ; lem-pass-X3-CKd32-X3-vs-CS01 ; lem-pass-X3-CKd32-X3-vs-CSd01 ; lem-pass-X3-CKd32-X3-vs-TOFF023 ; lem-pass-X3-CS32-X3-vs-CS01 ; lem-pass-X3-CS32-X3-vs-CSd01 ; lem-pass-X3-CS32-X3-vs-TOFF023 ; lem-pass-X3-CSd32-X3-vs-CS01 ; lem-pass-X3-CSd32-X3-vs-CS12 ; lem-pass-X3-CSd32-X3-vs-CSd01 ; lem-pass-X3-CSd32-X3-vs-CSd12 ; lem-pass-X3-CSd32-X3-vs-TOFF023 ; lem-pass-X3-CSd32-X3-vs-TOFF203)

-- pass [X3 CSd30 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff013 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF013) ▸
       at 1 4 (CS02 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS02) ▸
       at 2 4 (Toff013 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF013) ▸
       at 3 4 (CS02⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CSd02) ▸ done

-- pass [CCZ012] [CCZ123]: 1 steps
lem-pass-CCZ012-vs-CCZ123 : ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CCZ123 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CCZ123 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CCZ123) ▸ done

-- pass [X2 CS20 X2] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF012) ▸
       at 1 4 (CS03 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03) ▸
       at 2 4 (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF012) ▸
       at 3 4 (CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CSd03) ▸ done

-- pass [X2 CS20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF102) ▸
       at 1 4 (CS13 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS13) ▸
       at 2 4 (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF102) ▸
       at 3 4 (CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CSd13) ▸ done

-- pass [X2 CK20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF102) ▸
       at 1 4 (CS13 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS13) ▸
       at 2 4 (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF102) ▸
       at 3 4 (CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CSd13) ▸ done

-- pass [X2 CKd20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF102) ▸
       at 1 4 (CS13 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CS13) ▸
       at 2 4 (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF102) ▸
       at 3 4 (CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CSd13) ▸ done

-- pass [X2 CSd20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102) ▸
       at 1 4 (CS13 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS13) ▸
       at 2 4 (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102) ▸
       at 3 4 (CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CSd13) ▸ done

-- pass [CCZ123] [CCZ023]: 1 steps
lem-pass-CCZ123-vs-CCZ023 : ⟪ (CCZ123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-CCZ023 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ [])
  b0 = at 0 2 (CCZ023 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ023) ▸ done

-- pass [CCZ023] [CSd13]: 1 steps
lem-pass-CCZ023-vs-CSd13 : ⟪ (CCZ023 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CSd13 = run b0
  where
  b0 : Chain (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CSd13) ▸ done

-- pass [CS03] [S0]: 1 steps
lem-pass-CS03-vs-S0 : ⟪ (CS03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S0 = run b0
  where
  b0 : Chain (CS03 ∷ S0 ∷ []) (S0 ∷ CS03 ∷ [])
  b0 = at 0 2 (S0 ∷ CS03 ∷ []) (sym lem-pass-S0-vs-CS03) ▸ done

-- pass [CCZ023] [CS01]: 1 steps
lem-pass-CCZ023-vs-CS01 : ⟪ (CCZ023 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CS01 = run b0
  where
  b0 : Chain (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ [])
  b0 = at 0 2 (CS01 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CS01) ▸ done

-- pass [X3 CS31 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS13 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff103 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF103) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS12) ▸
       at 2 4 (Toff103 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF103) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CSd12) ▸ done

-- pass [X3 CS31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = run b0
  where
  b0 : Chain (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  b0 = at 0 4 (CS02 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS02) ▸
       at 1 4 (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF013) ▸
       at 2 4 (CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CSd02) ▸
       at 3 4 (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF013) ▸ done

-- pass [X3 CK31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = run b0
  where
  b0 : Chain (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  b0 = at 0 4 (CS02 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS02) ▸
       at 1 4 (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF013) ▸
       at 2 4 (CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CSd02) ▸
       at 3 4 (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF013) ▸ done

-- pass [X3 CKd31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = run b0
  where
  b0 : Chain (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS02) ▸
       at 1 4 (Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-TOFF013) ▸
       at 2 4 (CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CSd02) ▸
       at 3 4 (Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-TOFF013) ▸ done

-- pass [X3 CSd31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = run b0
  where
  b0 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (CS02 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CS02) ▸
       at 1 4 (Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-TOFF013) ▸
       at 2 4 (CS02⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CSd02) ▸
       at 3 4 (Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-TOFF013) ▸ done

-- pass [X2 CSd20 X2] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF012) ▸
       at 1 4 (CS03 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS03) ▸
       at 2 4 (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF012) ▸
       at 3 4 (CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CSd03) ▸ done

-- pass [X2 CS21 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102) ▸
       at 1 4 (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13) ▸
       at 2 4 (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102) ▸
       at 3 4 (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CSd13) ▸ done

-- pass [X2 CS21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (CS03 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS03) ▸
       at 1 4 (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF012) ▸
       at 2 4 (CS03⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CSd03) ▸
       at 3 4 (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF012) ▸ done

-- pass [X2 CK21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b0 = at 0 4 (CS03 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-CS03) ▸
       at 1 4 (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF012) ▸
       at 2 4 (CS03⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-CSd03) ▸
       at 3 4 (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF012) ▸ done

-- pass [X2 CKd21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS03) ▸
       at 1 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012) ▸
       at 2 4 (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CSd03) ▸
       at 3 4 (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF012) ▸ done

-- pass [X2 CSd21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS03) ▸
       at 1 4 (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF012) ▸
       at 2 4 (CS03⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CSd03) ▸
       at 3 4 (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF012) ▸ done

-- pass [CK31] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = run b0
  where
  b0 : Chain (CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ [])
  b0 = at 0 2 (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) wn01366 ▸
       at 1 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 4 (X3 ∷ CK31 ∷ []) wn01367 ▸ done

-- pass [S0] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (S0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S0 ∷ [])
  b0 = at 0 2 (Toff102 ∷ S0 ∷ []) wn01368 ▸
       at 1 2 (CS13 ∷ S0 ∷ []) (sym lem-pass-CS13-vs-S0) ▸
       at 2 2 (Toff102 ∷ S0 ∷ []) wn01368 ▸
       at 3 2 (CS13⁻ ∷ S0 ∷ []) (sym lem-pass-CSd13-vs-S0) ▸ done

-- pass [S0] [TOFF103 CS12 TOFF103 CSd12]: 120 steps
lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (S0 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 7 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (S0 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (K1 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 2 (Toff102 ∷ S0 ∷ []) wn01368 ▸
       at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b4 : Chain (K1 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K1 ∷ ι ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K1 ∷ ι ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ S0 ∷ K1 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b7 = at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS12 ∷ S0 ∷ []) (lem-pass-S0-vs-CS12) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b8 : Chain (Toff103 ∷ CS12 ∷ S0 ∷ K1 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b8 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Toff103 ∷ CS12 ∷ S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ [])
  b9 = at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b10 : Chain (Toff103 ∷ CS12 ∷ S0 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ S0 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b10 = at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Toff103 ∷ CS12 ∷ S0 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ S0 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b11 = at 2 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 3 2 (Toff102 ∷ S0 ∷ []) wn01368 ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b12 : Chain (Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ S0 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b12 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b13 : Chain (Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b13 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b14 : Chain (Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ S0 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ S0 ∷ [])
  b14 = at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (CS12⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd12) ▸ done

-- pass [CSd03] [TOFF103 CS12 TOFF103 CSd12]: 124 steps
lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (CS03⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (run b15)))))))))))))))
  where
  b0 : Chain (CS03⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CS03⁻ ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 7 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS03⁻ ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (Toff102 ∷ CS02⁻ ∷ []) wn01352 ▸
       at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b6 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸ done

  b7 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ CS03⁻ ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b7 = at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CS12 ∷ CS03⁻ ∷ []) (sym lem-pass-CS12-vs-CSd03) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Toff103 ∷ CS12 ∷ CS03⁻ ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b8 = at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b9 : Chain (Toff103 ∷ CS12 ∷ CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ [])
  b9 = at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Toff103 ∷ CS12 ∷ CS03⁻ ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ CS03⁻ ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸ done

  b11 : Chain (Toff103 ∷ CS12 ∷ CS03⁻ ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ [])
  b11 = at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (Toff102 ∷ CS02⁻ ∷ []) wn01352 ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b12 : Chain (Toff103 ∷ CS12 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ [])
  b12 = at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b13 : Chain (Toff103 ∷ CS12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ [])
  b13 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b14 : Chain (Toff103 ∷ CS12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ [])
  b14 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Toff103 ∷ CS12 ∷ Toff103 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS03⁻ ∷ [])
  b15 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (CS12⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd12-vs-CSd03) ▸ done

-- pass [S0] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (S0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 = run b0
  where
  b0 : Chain (S0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ S0 ∷ [])
  b0 = at 0 2 (Toff123 ∷ S0 ∷ []) (low₁-comm (S) (Toff)) ▸
       at 1 2 (CS01 ∷ S0 ∷ []) (lem-pass-S0-vs-CS01) ▸
       at 2 2 (Toff123 ∷ S0 ∷ []) (low₁-comm (S) (Toff)) ▸
       at 3 2 (CS01⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd01) ▸ done

-- pass [X1 CS10 X1] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 4 (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-TOFF012) ▸
       at 1 4 (CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03) ▸
       at 2 4 (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-TOFF012) ▸
       at 3 4 (CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CSd03) ▸ done

-- pass [X3 CKd31 X3] [TOFF102 CS13 TOFF102 CSd13]: 7 steps
lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X3 ∷ CK31⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  b0 = at 7 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 8 0 (CK31 ∷ CK31⁻ ∷ []) wn01369 ▸
       at 9 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 3 7 (X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 2 2 [] wn00390 ▸
       at 1 2 [] wn01370 ▸
       at 0 2 [] wn00390 ▸ done

-- pass [X3 CSd31 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-TOFF103) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CS12) ▸
       at 2 4 (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-TOFF103) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CSd12) ▸ done

-- pass [X2 CSd21 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102) ▸
       at 1 4 (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13) ▸
       at 2 4 (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102) ▸
       at 3 4 (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CSd13) ▸ done

-- pass [X3 CS32 X3] [TOFF203 CS12 TOFF203 CSd12]: 4 steps
lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF203) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS12) ▸
       at 2 4 (Toff203 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF203) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CSd12) ▸ done

-- pass [X3 CKd32 X3] [TOFF201 CS23 TOFF201 CSd23]: 7 steps
lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 7 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 8 0 (CK32 ∷ CK32⁻ ∷ []) wn01371 ▸
       at 9 0 (X3 ∷ X3 ∷ []) wn00225 ▸
       at 3 7 (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (sym lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23) ▸
       at 2 2 [] wn00390 ▸
       at 1 2 [] wn01372 ▸
       at 0 2 [] wn00390 ▸ done

-- pass [X3 CSd32 X3] [TOFF203 CS12 TOFF203 CSd12]: 4 steps
lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff203 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF203) ▸
       at 1 4 (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS12) ▸
       at 2 4 (Toff203 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF203) ▸
       at 3 4 (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CSd12) ▸ done

-- pass [X3 CSd32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = run b0
  where
  b0 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF023) ▸
       at 1 4 (CS01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS01) ▸
       at 2 4 (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF023) ▸
       at 3 4 (CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CSd01) ▸ done

-- pass [X3 CKd32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = run b0
  where
  b0 : Chain (X3 ∷ CK32⁻ ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF023) ▸
       at 1 4 (CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01) ▸
       at 2 4 (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF023) ▸
       at 3 4 (CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CSd01) ▸ done

-- pass [X3 CS32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = run b0
  where
  b0 : Chain (X3 ∷ CS23 ∷ X3 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 0 4 (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF023) ▸
       at 1 4 (CS01 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS01) ▸
       at 2 4 (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF023) ▸
       at 3 4 (CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CSd01) ▸ done

-- pass [CCZ012] [CS23]: 1 steps
lem-pass-CCZ012-vs-CS23 : ⟪ (CCZ012 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS23 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS23 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS23) ▸ done

-- pass [CCZ013] [CS23]: 1 steps
lem-pass-CCZ013-vs-CS23 : ⟪ (CCZ013 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS23 = run b0
  where
  b0 : Chain (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ [])
  b0 = at 0 2 (CS23 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS23) ▸ done
