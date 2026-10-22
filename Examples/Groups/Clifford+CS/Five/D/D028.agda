{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD028 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D028 (Sᴰ : SD028) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ034-CX12 : Ws → St 1285
  lem-comm-CCZ034-CX12 = pickᴰ 0 Sᴰ
  lem-sym-ab-at03122031 : Ws → St 1073
  lem-sym-ab-at03122031 = pickᴰ 1 Sᴰ
  lem-box-tQ-at3443 : Ws → St 264
  lem-box-tQ-at3443 = pickᴰ 2 Sᴰ
  lem-sym-bc-at031031 : Ws → St 1146
  lem-sym-bc-at031031 = pickᴰ 3 Sᴰ
  lem-Xb-box-at243243 : Ws → St 1253
  lem-Xb-box-at243243 = pickᴰ 4 Sᴰ
  lem-box-perm-1324-at243243 : Ws → St 1256
  lem-box-perm-1324-at243243 = pickᴰ 5 Sᴰ
  lem-box-perm-1324-at3443 : Ws → St 1354
  lem-box-perm-1324-at3443 = pickᴰ 6 Sᴰ
  lem-pairs-at03243240 : Ws → St 1355
  lem-pairs-at03243240 = pickᴰ 7 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 181 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1354 (lem-box-perm-1324-at3443 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1253 (lem-Xb-box-at243243 c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1172 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X))
  q6 : Ws → Eqn
  q6 c4 = wlE 729 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1256 (lem-box-perm-1324-at243243 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 264 (lem-box-tQ-at3443 c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 207 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 314 c4
  q11 : Ws → Eqn
  q11 c4 = sE 1285 (lem-comm-CCZ034-CX12 c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 313 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 312 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 979 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 980 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 981 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 982 c4
  q18 : Ws → Eqn
  q18 c4 = wlE 464 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff012 ∷ S4 ∷ []) (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑))
  q22 : Ws → Eqn
  q22 c4 = wlE 1173 (lit c4)

-- CKc-box @3443: 61 steps
lem-CKc-box-at3443 : Ws → ⟪ (Bx0-1243 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ []) ⟫ʷ
lem-CKc-box-at3443 c4 = derive (Bx0-1243 ∷ CK43 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 1 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw 5 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw 11 (q16 c4) ∷
   rw 13 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q12 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q14 c4) ∷
   rw 6 (q15 c4) ∷
   rw 9 (q16 c4) ∷
   rw 11 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q12 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q13 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q7 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = sE 1355 (lem-pairs-at03243240 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1073 (lem-sym-ab-at03122031 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1146 (lem-sym-bc-at031031 c4)

-- box-perm-4132 @03243240: 3 steps
lem-box-perm-4132-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4132-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷ []) Eq.refl
