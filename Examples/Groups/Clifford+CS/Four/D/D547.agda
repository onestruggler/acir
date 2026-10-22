{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD547 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D547 (W : Ws) (Sᴰ : SD547) where

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
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1 : St 921
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q3 : Eqn
  q3 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (wn 1567 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q10 : Eqn
  q10 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q11 : Eqn
  q11 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q12 : Eqn
  q12 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q13 : Eqn
  q13 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1)
  q14 : Eqn
  q14 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X2 ∷ CX21 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) (wn 1568 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF013 X3]: 237 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 31 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 33 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 35 q1 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q5 ∷
   rw 38 q6 ∷
   rw 37 q5 ∷
   rw 36 q3 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 34 q4 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 32 q4 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 30 q3 ∷
   rw 31 q7 ∷
   re 31 8 (Toff012 ∷ []) ∷
   rw 29 q2 ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 32 q1 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 31 q9 ∷
   rw⁻ 32 q10 ∷
   rw⁻ 33 q11 ∷
   rw⁻ 34 q10 ∷
   rw⁻ 35 q10 ∷
   rw 36 q9 ∷
   rw 39 q1 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw 38 q9 ∷
   rw⁻ 39 q10 ∷
   rw⁻ 40 q10 ∷
   rw⁻ 41 q10 ∷
   rw⁻ 42 q10 ∷
   rw⁻ 43 q10 ∷
   rw⁻ 44 q10 ∷
   rw⁻ 45 q12 ∷
   rw⁻ 46 q11 ∷
   rw⁻ 47 q10 ∷
   rw⁻ 48 q10 ∷
   rw⁻ 49 q10 ∷
   rw 50 q9 ∷
   rw 53 q1 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 52 q9 ∷
   rw 53 q9 ∷
   rw 56 q1 ∷
   re 54 3 (CS03⁻ ∷ []) ∷
   rw 57 q1 ∷
   re 55 3 (CK30⁻ ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CS03⁻ ∷ []) ∷
   rw 59 q1 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 58 q9 ∷
   rw 59 q9 ∷
   rw 62 q1 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 63 q9 ∷
   rw⁻ 64 q10 ∷
   rw⁻ 65 q11 ∷
   rw⁻ 66 q10 ∷
   rw⁻ 67 q10 ∷
   rw 68 q9 ∷
   rw 71 q1 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 70 q9 ∷
   rw⁻ 71 q10 ∷
   rw⁻ 72 q10 ∷
   rw⁻ 73 q10 ∷
   rw⁻ 74 q10 ∷
   rw⁻ 75 q10 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 77 q12 ∷
   rw⁻ 78 q11 ∷
   rw⁻ 79 q10 ∷
   rw⁻ 80 q10 ∷
   rw⁻ 81 q10 ∷
   rw 82 q9 ∷
   rw 85 q1 ∷
   re 83 3 (CX31 ∷ []) ∷
   rw 84 q9 ∷
   rw 85 q9 ∷
   rw 88 q1 ∷
   re 86 3 (CS03⁻ ∷ []) ∷
   rw 89 q1 ∷
   re 87 3 (CK30⁻ ∷ []) ∷
   rw 90 q1 ∷
   re 88 3 (CS03⁻ ∷ []) ∷
   rw 91 q1 ∷
   re 89 3 (CS03⁻ ∷ []) ∷
   rw 90 q9 ∷
   rw 91 q9 ∷
   rw 94 q1 ∷
   re 92 3 (CS03⁻ ∷ []) ∷
   rw 95 q1 ∷
   re 93 3 (CS03⁻ ∷ []) ∷
   rw 96 q1 ∷
   re 94 3 (CS03⁻ ∷ []) ∷
   rw 95 q9 ∷
   rw 96 q6 ∷
   rw 0 q13 ∷
   rw 67 q1 ∷
   rw 66 q2 ∷
   re 65 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q6 ∷
   re 64 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q6 ∷
   re 63 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q6 ∷
   rw 62 q2 ∷
   rw 61 q2 ∷
   re 60 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q6 ∷
   re 59 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q6 ∷
   re 58 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q6 ∷
   re 57 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q6 ∷
   rw 56 q2 ∷
   rw 55 q2 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q6 ∷
   rw 53 q2 ∷
   rw 52 q10 ∷
   rw 51 q10 ∷
   rw 50 q10 ∷
   rw 49 q11 ∷
   rw 48 q12 ∷
   rw 47 q10 ∷
   rw 46 q10 ∷
   rw 45 q10 ∷
   rw 44 q10 ∷
   rw 43 q10 ∷
   rw 42 q10 ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 39 q2 ∷
   rw 38 q10 ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   rw 35 q10 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 27 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 26 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 25 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw 24 q2 ∷
   rw 23 q2 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 21 q2 ∷
   rw 20 q10 ∷
   rw 19 q10 ∷
   rw 18 q10 ∷
   rw 17 q11 ∷
   rw 16 q12 ∷
   rw 15 q10 ∷
   rw 14 q10 ∷
   rw 13 q10 ∷
   rw 12 q10 ∷
   rw 11 q10 ∷
   rw 10 q10 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q2 ∷
   rw 6 q10 ∷
   rw 5 q10 ∷
   rw 4 q11 ∷
   rw 3 q10 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q2 ∷
   rw 1 q14 ∷
   rw 0 q9 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q9 ∷
   rw 3 q6 ∷ []) Eq.refl
