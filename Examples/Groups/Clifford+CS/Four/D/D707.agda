{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD707 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D707 (W : Ws) (Sᴰ : SD707) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 851
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 870
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1926
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 1928
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 5 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1930
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 6 Sᴰ
  lem-hyb-sym-23-at1320 : St 2015
  lem-hyb-sym-23-at1320 = pickᴰ 7 Sᴰ

private
  q1 : Eqn
  q1 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S0 ∷ CK01 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) (lem-hyb-sym-23-at1320)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (CK01 ∷ Sw23 ∷ []) (Sw23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ []) (wn 1201 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q9 : Eqn
  q9 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 1202 W)

-- respell hyb CS13 CS13 CK31 CS13 CX32 CS12 CS12 CS12  -> CS01 CS01 CK01 CS01 CX03 CS13 CS13 CS13 : 235 steps
lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ []) ⟫ʷ
lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S0 ∷ CK01 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ [])
  (rw 0 q1 ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   re 16 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q3 ∷
   rw 14 q3 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 9 q6 ∷
   rw 8 q4 ∷
   rw 7 q3 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 10 q2 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 9 q8 ∷
   rw 12 q2 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 13 q2 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 14 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 18 q2 ∷
   re 16 3 (CX03 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q2 ∷
   re 19 3 (CK31 ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 21 q5 ∷
   rw 78 q2 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 71 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   rw 70 q9 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 66 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   rw 65 q3 ∷
   rw 64 q3 ∷
   rw 63 q3 ∷
   rw 62 q3 ∷
   rw 61 q3 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   rw 47 q3 ∷
   rw 46 q3 ∷
   rw 45 q3 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
   rw 41 q3 ∷
   rw 40 q3 ∷
   rw 39 q3 ∷
   rw 38 q3 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   re 33 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 32 q3 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw 29 q3 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q6 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw 22 q3 ∷
   rw 23 q10 ∷
   rw 24 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 25 q8 ∷
   rw 28 q2 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CX03 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 38 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 39 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 40 q2 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 41 q2 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 42 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 43 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 44 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 45 q2 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 46 q2 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 47 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 48 q2 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 49 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 50 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 51 q2 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 52 q2 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 53 q2 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 52 q8 ∷
   rw 53 q8 ∷
   rw 54 q8 ∷
   rw 55 q8 ∷
   rw 58 q2 ∷
   re 56 3 (CK31 ∷ []) ∷
   rw 59 q2 ∷
   re 57 3 (CS13 ∷ []) ∷
   rw 60 q2 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 61 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   rw 62 q2 ∷
   re 60 3 (CS13 ∷ []) ∷
   rw 63 q2 ∷
   re 61 3 (CS13 ∷ []) ∷
   rw 64 q2 ∷
   re 62 3 (CS13 ∷ []) ∷
   rw 65 q2 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 66 q2 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CS13 ∷ []) ∷
   rw 68 q2 ∷
   re 66 3 (CX03 ∷ []) ∷
   rw⁻ 67 q3 ∷
   rw⁻ 68 q3 ∷
   rw⁻ 69 q3 ∷
   rw⁻ 70 q6 ∷
   rw⁻ 71 q4 ∷
   rw⁻ 72 q3 ∷
   rw⁻ 73 q3 ∷
   rw⁻ 74 q3 ∷
   rw⁻ 75 q3 ∷
   rw⁻ 76 q3 ∷
   rw⁻ 77 q3 ∷
   rw 78 q5 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q12 : Eqn
  q12 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q14 : Eqn
  q14 = eqn (X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2072 W)
  q15 : Eqn
  q15 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q16 : Eqn
  q16 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q17 : Eqn
  q17 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q18 : Eqn
  q18 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q19 : Eqn
  q19 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q20 : Eqn
  q20 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2073 W)

-- pass [X3 CK30 X3] [K0 S0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 Sd0 Kd0]: 75 steps
lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 = derive (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 7 q2 ∷
   rw 6 q11 ∷
   rw 5 q6 ∷
   rw 4 q6 ∷
   rw 3 q12 ∷
   rw 2 q13 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q13 ∷
   rw 1 q14 ∷
   rw⁻ 0 q12 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q11 ∷
   rw 4 q15 ∷
   rw 7 q2 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q15 ∷
   rw 10 q2 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q15 ∷
   rw 10 q15 ∷
   rw 13 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q15 ∷
   rw 13 q15 ∷
   rw 16 q2 ∷
   re 14 3 (CK30⁻ ∷ []) ∷
   rw 15 q15 ∷
   rw 16 q15 ∷
   rw 19 q2 ∷
   re 17 3 (CS03⁻ ∷ []) ∷
   rw 18 q15 ∷
   rw 19 q5 ∷
   rw 16 q16 ∷
   rw 13 q17 ∷
   rw 10 q18 ∷
   rw 7 q17 ∷
   rw 4 q16 ∷
   rw 27 q2 ∷
   rw 26 q11 ∷
   rw 25 q19 ∷
   rw 24 q19 ∷
   rw 23 q12 ∷
   rw 22 q13 ∷
   re 21 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   rw 20 q13 ∷
   rw 19 q13 ∷
   re 18 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   rw 17 q13 ∷
   rw 16 q13 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q13 ∷
   rw 13 q13 ∷
   re 12 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw 11 q13 ∷
   rw 10 q13 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q13 ∷
   rw 9 q20 ∷
   rw⁻ 8 q12 ∷
   rw⁻ 9 q19 ∷
   rw⁻ 10 q19 ∷
   rw⁻ 11 q11 ∷
   rw 12 q15 ∷
   rw 15 q2 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 14 q15 ∷
   rw 15 q5 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2074 W)
  q22 : Eqn
  q22 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
  q23 : Eqn
  q23 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
  q24 : Eqn
  q24 = eqn (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
  q25 : Eqn
  q25 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2075 W)

-- pass [X2 CK20 X2] [S0 Kd0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 K0 Sd0]: 5 steps
lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0 = derive (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 0 q21 ∷
   rw 10 q22 ∷
   rw 7 q23 ∷
   rw 4 q24 ∷
   rw 8 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2076 W)
  q27 : Eqn
  q27 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2077 W)

-- pass [X2 CKd20 X2] [S0 S0 Kd0 S0 Kd0 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 K0 Sd0 K0 Sd0 Sd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 0 q26 ∷
   rw 18 q22 ∷
   rw 15 q23 ∷
   rw 12 q24 ∷
   rw 9 q24 ∷
   rw 6 q23 ∷
   rw 10 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2078 W)
  q29 : Eqn
  q29 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q30 : Eqn
  q30 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2079 W)

-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 Kd0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 K0 Sd0 K0 S0]: 79 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 8 q2 ∷
   rw 7 q11 ∷
   rw 6 q11 ∷
   rw 5 q6 ∷
   rw 4 q11 ∷
   rw 3 q19 ∷
   rw 2 q13 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q13 ∷
   rw 1 q28 ∷
   rw⁻ 0 q19 ∷
   rw⁻ 1 q11 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 4 q11 ∷
   rw 5 q15 ∷
   rw 8 q2 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q15 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q15 ∷
   rw 11 q15 ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q15 ∷
   rw 14 q15 ∷
   rw 17 q2 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q15 ∷
   rw 17 q15 ∷
   rw 20 q2 ∷
   re 18 3 (CS03⁻ ∷ []) ∷
   rw 19 q15 ∷
   rw 20 q5 ∷
   rw 17 q16 ∷
   rw 14 q29 ∷
   rw 11 q18 ∷
   rw 8 q18 ∷
   rw 5 q29 ∷
   rw 29 q2 ∷
   rw 28 q6 ∷
   rw 27 q12 ∷
   rw 26 q19 ∷
   rw 25 q12 ∷
   rw 24 q12 ∷
   rw 23 q13 ∷
   re 22 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   rw 21 q13 ∷
   rw 20 q13 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q13 ∷
   rw 17 q13 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q13 ∷
   rw 14 q13 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q13 ∷
   rw 11 q13 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q13 ∷
   rw 10 q30 ∷
   rw⁻ 9 q12 ∷
   rw⁻ 10 q12 ∷
   rw⁻ 11 q19 ∷
   rw⁻ 12 q12 ∷
   rw⁻ 13 q6 ∷
   rw 14 q15 ∷
   rw 17 q2 ∷
   re 15 3 (CK30⁻ ∷ []) ∷
   rw 16 q15 ∷
   rw 17 q5 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2080 W)
  q32 : Eqn
  q32 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2081 W)

-- pass [X2 CKd20 X2] [K0 S0 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 Sd0 Kd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 0 q31 ∷
   rw 16 q24 ∷
   rw 13 q23 ∷
   rw 10 q22 ∷
   rw 7 q23 ∷
   rw 4 q24 ∷
   rw 8 q32 ∷ []) Eq.refl
