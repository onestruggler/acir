{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD049 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D049 (Sᴰ : SD049) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 1 Sᴰ
  lem-F4-I-S2 : Ws → St 1595
  lem-F4-I-S2 = pickᴰ 2 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 3 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 4 Sᴰ
  lem-F4-K3-S2 : Ws → St 1619
  lem-F4-K3-S2 = pickᴰ 5 Sᴰ
  lem-F4-S2-I : Ws → St 1597
  lem-F4-S2-I = pickᴰ 6 Sᴰ
  lem-F4-S2-K3 : Ws → St 1598
  lem-F4-S2-K3 = pickᴰ 7 Sᴰ
  lem-F4-S2-S2 : Ws → St 1599
  lem-F4-S2-S2 = pickᴰ 8 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 9 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1606
  lem-F4-CS2-S2 = pickᴰ 10 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 11 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1607
  lem-F4-S2-CS2 = pickᴰ 12 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 15 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 16 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1590 (lem-F5-23 c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1419 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1418 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1607 (lem-F4-S2-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1598 (lem-F4-S2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1599 (lem-F4-S2-S2 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 1411 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1595 (lem-F4-I-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1411 (lem-F4-I-K3 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1597 (lem-F4-S2-I c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1606 (lem-F4-CS2-S2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1576 (lem-F4-CS2-I c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1619 (lem-F4-K3-S2 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1618 (lem-F4-K3-I c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1386 (lem-F4-I-I c4)

-- deb-CKS-split-a: 276 steps
lem-deb-CKS-split-a : Ws → ⟪ (ℓ "乢丞乢丞乢世世世一世乢乢乢乢丞乢丞乢世世世一世") ⟫ʷ ≈ ⟪ (ℓ "並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並並侬並並侬並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並侬亊侬亊侬乩乩乩丢乩侬侬侬侬亊侬亊侬乩乩乩丢乩") ⟫ʷ
lem-deb-CKS-split-a c4 = derive (ℓ "乢丞乢丞乢世世世一世乢乢乢乢丞乢丞乢世世世一世") (ℓ "並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並並侬並並侬並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並侬亊侬亊侬乩乩乩丢乩侬侬侬侬亊侬亊侬乩乩乩丢乩")
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 35 (q15 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw⁻ 32 (q10 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw⁻ 30 (q9 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw⁻ 28 (q9 c4) ∷
   rw⁻ 27 (q8 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q16 c4) ∷
   rw⁻ 38 (q17 c4) ∷
   rw⁻ 37 (q16 c4) ∷
   rw⁻ 36 (q16 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 42 (q16 c4) ∷
   rw⁻ 41 (q17 c4) ∷
   rw⁻ 40 (q16 c4) ∷
   rw⁻ 39 (q16 c4) ∷
   rw⁻ 38 (q16 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 47 (q5 c4) ∷
   rw⁻ 46 (q5 c4) ∷
   rw⁻ 45 (q16 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw⁻ 43 (q16 c4) ∷
   rw⁻ 42 (q16 c4) ∷
   rw⁻ 41 (q16 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw⁻ 50 (q5 c4) ∷
   rw⁻ 49 (q5 c4) ∷
   rw⁻ 48 (q16 c4) ∷
   rw⁻ 47 (q17 c4) ∷
   rw⁻ 46 (q16 c4) ∷
   rw⁻ 45 (q16 c4) ∷
   rw⁻ 44 (q16 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 42 (q4 c4) ∷
   rw⁻ 41 (q5 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw 56 (q2 c4) ∷
   rw⁻ 55 (q3 c4) ∷
   rw⁻ 54 (q3 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 51 (q18 c4) ∷
   rw⁻ 50 (q19 c4) ∷
   rw⁻ 49 (q18 c4) ∷
   rw⁻ 48 (q18 c4) ∷
   rw⁻ 47 (q18 c4) ∷
   rw⁻ 46 (q3 c4) ∷
   rw⁻ 45 (q6 c4) ∷
   rw⁻ 44 (q3 c4) ∷
   rw⁻ 43 (q6 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw⁻ 60 (q1 c4) ∷
   rw⁻ 59 (q4 c4) ∷
   rw⁻ 58 (q5 c4) ∷
   rw⁻ 57 (q5 c4) ∷
   rw⁻ 56 (q5 c4) ∷
   rw⁻ 55 (q5 c4) ∷
   rw⁻ 54 (q16 c4) ∷
   rw⁻ 53 (q17 c4) ∷
   rw⁻ 52 (q16 c4) ∷
   rw⁻ 51 (q16 c4) ∷
   rw⁻ 50 (q16 c4) ∷
   rw⁻ 49 (q5 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 47 (q5 c4) ∷
   rw⁻ 46 (q4 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw 64 (q2 c4) ∷
   rw⁻ 63 (q3 c4) ∷
   rw⁻ 62 (q6 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw⁻ 60 (q3 c4) ∷
   rw⁻ 59 (q3 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 57 (q18 c4) ∷
   rw⁻ 56 (q19 c4) ∷
   rw⁻ 55 (q18 c4) ∷
   rw⁻ 54 (q18 c4) ∷
   rw⁻ 53 (q18 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 51 (q6 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw⁻ 49 (q6 c4) ∷
   rw⁻ 48 (q3 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 66 (q5 c4) ∷
   rw⁻ 65 (q4 c4) ∷
   rw⁻ 64 (q5 c4) ∷
   rw⁻ 63 (q5 c4) ∷
   rw⁻ 62 (q5 c4) ∷
   rw⁻ 61 (q5 c4) ∷
   rw⁻ 60 (q16 c4) ∷
   rw⁻ 59 (q17 c4) ∷
   rw⁻ 58 (q16 c4) ∷
   rw⁻ 57 (q16 c4) ∷
   rw⁻ 56 (q16 c4) ∷
   rw⁻ 55 (q5 c4) ∷
   rw⁻ 54 (q4 c4) ∷
   rw⁻ 53 (q5 c4) ∷
   rw⁻ 52 (q4 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw 72 (q7 c4) ∷
   rw⁻ 71 (q8 c4) ∷
   rw⁻ 70 (q9 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 68 (q9 c4) ∷
   rw⁻ 67 (q8 c4) ∷
   rw⁻ 66 (q8 c4) ∷
   rw⁻ 65 (q8 c4) ∷
   rw⁻ 64 (q8 c4) ∷
   rw⁻ 63 (q10 c4) ∷
   rw⁻ 62 (q15 c4) ∷
   rw⁻ 61 (q10 c4) ∷
   rw⁻ 60 (q10 c4) ∷
   rw⁻ 59 (q10 c4) ∷
   rw⁻ 58 (q8 c4) ∷
   rw⁻ 57 (q9 c4) ∷
   rw⁻ 56 (q8 c4) ∷
   rw⁻ 55 (q9 c4) ∷
   rw⁻ 54 (q8 c4) ∷
   rw 76 (q7 c4) ∷
   rw⁻ 75 (q10 c4) ∷
   rw⁻ 74 (q8 c4) ∷
   rw⁻ 73 (q9 c4) ∷
   rw⁻ 72 (q8 c4) ∷
   rw⁻ 71 (q9 c4) ∷
   rw⁻ 70 (q8 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 68 (q8 c4) ∷
   rw⁻ 67 (q8 c4) ∷
   rw⁻ 66 (q10 c4) ∷
   rw⁻ 65 (q15 c4) ∷
   rw⁻ 64 (q10 c4) ∷
   rw⁻ 63 (q10 c4) ∷
   rw⁻ 62 (q10 c4) ∷
   rw⁻ 61 (q8 c4) ∷
   rw⁻ 60 (q9 c4) ∷
   rw⁻ 59 (q8 c4) ∷
   rw⁻ 58 (q9 c4) ∷
   rw⁻ 57 (q8 c4) ∷
   rw 80 (q7 c4) ∷
   rw⁻ 79 (q10 c4) ∷
   rw⁻ 78 (q10 c4) ∷
   rw⁻ 77 (q8 c4) ∷
   rw⁻ 76 (q9 c4) ∷
   rw⁻ 75 (q8 c4) ∷
   rw⁻ 74 (q9 c4) ∷
   rw⁻ 73 (q8 c4) ∷
   rw⁻ 72 (q8 c4) ∷
   rw⁻ 71 (q8 c4) ∷
   rw⁻ 70 (q8 c4) ∷
   rw⁻ 69 (q10 c4) ∷
   rw⁻ 68 (q15 c4) ∷
   rw⁻ 67 (q10 c4) ∷
   rw⁻ 66 (q10 c4) ∷
   rw⁻ 65 (q10 c4) ∷
   rw⁻ 64 (q8 c4) ∷
   rw⁻ 63 (q9 c4) ∷
   rw⁻ 62 (q8 c4) ∷
   rw⁻ 61 (q9 c4) ∷
   rw⁻ 60 (q8 c4) ∷
   rw⁻ 84 (q11 c4) ∷
   rw⁻ 83 (q12 c4) ∷
   rw⁻ 82 (q12 c4) ∷
   rw⁻ 81 (q12 c4) ∷
   rw⁻ 80 (q13 c4) ∷
   rw⁻ 79 (q14 c4) ∷
   rw⁻ 78 (q13 c4) ∷
   rw⁻ 77 (q14 c4) ∷
   rw⁻ 76 (q13 c4) ∷
   rw⁻ 75 (q13 c4) ∷
   rw⁻ 74 (q13 c4) ∷
   rw⁻ 73 (q13 c4) ∷
   rw⁻ 72 (q12 c4) ∷
   rw⁻ 71 (q20 c4) ∷
   rw⁻ 70 (q12 c4) ∷
   rw⁻ 69 (q12 c4) ∷
   rw⁻ 68 (q12 c4) ∷
   rw⁻ 67 (q13 c4) ∷
   rw⁻ 66 (q14 c4) ∷
   rw⁻ 65 (q13 c4) ∷
   rw⁻ 64 (q14 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw 88 (q7 c4) ∷
   rw⁻ 87 (q15 c4) ∷
   rw⁻ 86 (q10 c4) ∷
   rw⁻ 85 (q10 c4) ∷
   rw⁻ 84 (q10 c4) ∷
   rw⁻ 83 (q8 c4) ∷
   rw⁻ 82 (q9 c4) ∷
   rw⁻ 81 (q8 c4) ∷
   rw⁻ 80 (q9 c4) ∷
   rw⁻ 79 (q8 c4) ∷
   rw⁻ 78 (q8 c4) ∷
   rw⁻ 77 (q8 c4) ∷
   rw⁻ 76 (q8 c4) ∷
   rw⁻ 75 (q10 c4) ∷
   rw⁻ 74 (q15 c4) ∷
   rw⁻ 73 (q10 c4) ∷
   rw⁻ 72 (q10 c4) ∷
   rw⁻ 71 (q10 c4) ∷
   rw⁻ 70 (q8 c4) ∷
   rw⁻ 69 (q9 c4) ∷
   rw⁻ 68 (q8 c4) ∷
   rw⁻ 67 (q9 c4) ∷
   rw⁻ 66 (q8 c4) ∷ []) Eq.refl
