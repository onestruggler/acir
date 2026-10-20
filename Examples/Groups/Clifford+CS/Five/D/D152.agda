{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D152 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-I-at02132031 ; lem-F4-I-S2-at02132031 ; lem-F4-I-S3-at02132031 ; lem-F4-K3-I-at02132031 ; lem-F4-K3-S2-at02132031 ; lem-F4-K3-S3-at02132031 ; lem-F4-S2-I-at02132031 ; lem-F4-S2-S2-at02132031 ; lem-F4-S2-S3-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-I-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-CS2-S3-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D075 using (lem-deb-AD-split-a-at02132031 ; lem-deb-AD-split-b-at02132031)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S2-at02132031 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S2-at02132031 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I-at02132031 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-I-at02132031 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-I-at02132031 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S3-at02132031 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S3-at02132031 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) (lem-deb-AD-split-a-at02132031 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (lem-deb-AD-split-b-at02132031 c4)

-- deb-AD @02132031 part1: 138 steps
lem-deb-AD-at02132031-part1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS14 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-AD-at02132031-part1 c4 = derive (CK41 ∷ CS14 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS14 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 72 (q1 c4) ∷
   rw 69 (q2 c4) ∷
   rw 66 (q1 c4) ∷
   rw 63 (q2 c4) ∷
   rw 94 (q2 c4) ∷
   rw 91 (q2 c4) ∷
   rw 88 (q3 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q4 c4) ∷
   rw 76 (q2 c4) ∷
   rw 73 (q1 c4) ∷
   rw 70 (q2 c4) ∷
   rw 67 (q1 c4) ∷
   rw 64 (q2 c4) ∷
   rw 95 (q5 c4) ∷
   rw 92 (q5 c4) ∷
   rw 89 (q6 c4) ∷
   rw 86 (q7 c4) ∷
   rw 83 (q7 c4) ∷
   rw 80 (q7 c4) ∷
   rw 77 (q5 c4) ∷
   rw 74 (q8 c4) ∷
   rw 71 (q5 c4) ∷
   rw 68 (q8 c4) ∷
   rw 65 (q5 c4) ∷
   rw 96 (q2 c4) ∷
   rw 93 (q2 c4) ∷
   rw 90 (q3 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q4 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q2 c4) ∷
   rw 75 (q1 c4) ∷
   rw 72 (q2 c4) ∷
   rw 69 (q1 c4) ∷
   rw 66 (q2 c4) ∷
   rw 97 (q9 c4) ∷
   rw 94 (q9 c4) ∷
   rw 91 (q10 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q11 c4) ∷
   rw 82 (q11 c4) ∷
   rw 79 (q9 c4) ∷
   rw 76 (q12 c4) ∷
   rw 73 (q9 c4) ∷
   rw 70 (q12 c4) ∷
   rw 67 (q9 c4) ∷
   rw 98 (q9 c4) ∷
   rw 95 (q9 c4) ∷
   rw 92 (q10 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q11 c4) ∷
   rw 83 (q11 c4) ∷
   rw 80 (q9 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q9 c4) ∷
   rw 71 (q12 c4) ∷
   rw 68 (q9 c4) ∷
   rw 99 (q9 c4) ∷
   rw 96 (q9 c4) ∷
   rw 93 (q10 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q11 c4) ∷
   rw 84 (q11 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q12 c4) ∷
   rw 75 (q9 c4) ∷
   rw 72 (q12 c4) ∷
   rw 69 (q9 c4) ∷
   rw 100 (q9 c4) ∷
   rw 97 (q9 c4) ∷
   rw 94 (q10 c4) ∷
   rw 91 (q11 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q11 c4) ∷
   rw 82 (q9 c4) ∷
   rw 79 (q12 c4) ∷
   rw 76 (q9 c4) ∷
   rw 73 (q12 c4) ∷
   rw 70 (q9 c4) ∷
   rw 101 (q9 c4) ∷
   rw 98 (q9 c4) ∷
   rw 95 (q10 c4) ∷
   rw 92 (q11 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q11 c4) ∷
   rw 83 (q9 c4) ∷
   rw 80 (q12 c4) ∷
   rw 77 (q9 c4) ∷
   rw 74 (q12 c4) ∷
   rw 71 (q9 c4) ∷
   rw 102 (q9 c4) ∷
   rw 99 (q9 c4) ∷
   rw 96 (q10 c4) ∷
   rw 93 (q11 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q11 c4) ∷
   rw 84 (q9 c4) ∷
   rw 81 (q12 c4) ∷
   rw 78 (q9 c4) ∷
   rw 75 (q12 c4) ∷
   rw 72 (q9 c4) ∷
   rw 103 (q9 c4) ∷
   rw 100 (q9 c4) ∷
   rw 97 (q10 c4) ∷
   rw 94 (q11 c4) ∷
   rw 91 (q11 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q9 c4) ∷
   rw 82 (q12 c4) ∷
   rw 79 (q9 c4) ∷
   rw 76 (q12 c4) ∷
   rw 73 (q9 c4) ∷
   rw 104 (q9 c4) ∷
   rw 101 (q9 c4) ∷
   rw 98 (q10 c4) ∷
   rw 95 (q11 c4) ∷
   rw 92 (q11 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q9 c4) ∷
   rw 83 (q12 c4) ∷
   rw 80 (q9 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q9 c4) ∷
   rw 105 (q9 c4) ∷
   rw 102 (q9 c4) ∷
   rw 99 (q10 c4) ∷
   rw 96 (q11 c4) ∷
   rw 93 (q11 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q9 c4) ∷
   rw 84 (q12 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q12 c4) ∷
   rw 75 (q9 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 28 (q14 c4) ∷ []) Eq.refl
