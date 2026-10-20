{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-BOX⟨0·312⟩-sw3-R ; lem-comm-push-BOX⟨0·31⟩-sw3-R ; lem-comm-push-BOX⟨0·41⟩-sw3-L ; lem-comm-push-BOX⟨0·42⟩-sw2-R ; lem-comm-push-BOX⟨0·43⟩-sw2-L ; lem-comm-push-BOX⟨4·02⟩-sw2-R ; lem-comm-push-BOX⟨4·03⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-push-CCZ014-sw2-L ; lem-comm-push-CCZ024-sw0-L ; lem-comm-push-CCZ034-sw0-L ; lem-comm-push-CCZ034-sw1-L ; lem-comm-push-TOFF023-sw3-L ; lem-comm-push-TOFF024-sw0-L ; lem-comm-push-TOFF024-sw3-L ; lem-comm-push-TOFF034-sw0-L ; lem-comm-push-TOFF034-sw1-L ; lem-comm-push-TOFF204-sw0-L ; lem-comm-push-TOFF304-sw0-L ; lem-comm-push-TOFF304-sw1-L ; lem-comm-push-TOFF401-sw2-L ; lem-comm-push-TOFF402-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-push-BOX⟨0·123⟩-sw0-L ; lem-comm-push-BOX⟨0·213⟩-sw1-L ; lem-comm-push-BOX⟨1·023⟩-sw2-L ; lem-comm-push-BOX⟨1·032⟩-sw1-L ; lem-comm-push-BOX⟨1·032⟩-sw2-R ; lem-comm-push-BOX⟨2·031⟩-sw1-R ; lem-comm-push-CCZ014-sw0-L ; lem-comm-push-CCZ014-sw2-R ; lem-comm-push-CCZ023-sw3-L ; lem-comm-push-CCZ024-sw3-L ; lem-comm-push-TOFF014-sw2-L ; lem-comm-push-TOFF014-sw2-R ; lem-comm-push-TOFF104-sw0-L ; lem-comm-push-TOFF104-sw2-L ; lem-comm-push-TOFF203-sw3-L ; lem-comm-push-TOFF204-sw3-L ; lem-comm-push-TOFF302-sw3-L ; lem-comm-push-TOFF402-sw3-L ; lem-comm-push-TOFF403-sw0-L ; lem-comm-push-TOFF403-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-push-BOX⟨0·123⟩-sw1-R ; lem-comm-push-BOX⟨1·023⟩-sw0-R ; lem-comm-push-BOX⟨2·031⟩-sw2-R ; lem-comm-push-BOX⟨2·4103⟩-sw1-L ; lem-comm-push-BOX⟨3·021⟩-sw2-L ; lem-comm-push-BOX⟨4·012⟩-sw1-L ; lem-comm-push-BOX⟨4·021⟩-sw1-R ; lem-comm-push-CCZ014-sw0-R ; lem-comm-push-CCZ023-sw3-R ; lem-comm-push-CCZ034-sw1-R ; lem-comm-push-CCZ034-sw3-R ; lem-comm-push-CCZ124-sw0-L ; lem-comm-push-TOFF014-sw0-R ; lem-comm-push-TOFF034-sw1-R ; lem-comm-push-TOFF302-sw3-R ; lem-comm-push-TOFF401-sw0-L ; lem-comm-push-TOFF412-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-push-BOX⟨0·213⟩-sw2-R ; lem-comm-push-BOX⟨0·413⟩-sw1-R ; lem-comm-push-BOX⟨1·4203⟩-sw1-R ; lem-comm-push-BOX⟨1·430⟩-sw1-R ; lem-comm-push-BOX⟨2·031⟩-sw0-R ; lem-comm-push-BOX⟨2·130⟩-sw1-R ; lem-comm-push-BOX⟨2·1430⟩-sw2-R ; lem-comm-push-BOX⟨2·430⟩-sw0-R ; lem-comm-push-BOX⟨3·1420⟩-sw3-R ; lem-comm-push-BOX⟨4·1320⟩-sw2-R ; lem-comm-push-CCZ024-sw0-R ; lem-comm-push-CCZ124-sw0-R ; lem-comm-push-TOFF024-sw0-R ; lem-comm-push-TOFF024-sw3-R ; lem-comm-push-TOFF304-sw3-R ; lem-comm-push-TOFF401-sw0-R ; lem-comm-push-TOFF401-sw2-R ; lem-comm-push-TOFF402-sw0-R ; lem-comm-push-TOFF412-sw0-R)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (CCZ034 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CCZ034 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4)

-- resp CCZ034 at 2: 4 steps
lem-resp-CCZ034-at-2 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-2 c4 = derive (CCZ034 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷ []) Eq.refl

-- resp CCZ034 at 1: 2 steps
lem-resp-CCZ034-at-1 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-1 c4 = derive (CCZ034 ∷ []) (Sw01 ∷ CCZ134 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (Toff034 ∷ Sw01 ∷ []) (Sw01 ∷ Toff134 ∷ []) (lem-comm-push-TOFF034-sw0-L c4)

-- resp TOFF034 at 1: 2 steps
lem-resp-TOFF034-at-1 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-1 c4 = derive (Toff034 ∷ []) (Sw01 ∷ Toff134 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q5 c4) ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = eqn (Toff034 ∷ Sw12 ∷ []) (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4)

-- resp TOFF034 at 2: 4 steps
lem-resp-TOFF034-at-2 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-2 c4 = derive (Toff034 ∷ []) (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q6 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (CCZ024 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4)

-- resp CCZ014 at 2: 5 steps
lem-resp-CCZ014-at-2 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-2 c4 = derive (CCZ014 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q7 c4) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (Toff204 ∷ Sw01 ∷ []) (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4)

-- resp TOFF204 at 1: 2 steps
lem-resp-TOFF204-at-1 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-1 c4 = derive (Toff204 ∷ []) (Sw01 ∷ Toff214 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

-- resp CCZ024 at 1: 2 steps
lem-resp-CCZ024-at-1 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-1 c4 = derive (CCZ024 ∷ []) (Sw01 ∷ CCZ124 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 c4)

-- resp CCZ024 at 3: 7 steps
lem-resp-CCZ024-at-3 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-3 c4 = derive (CCZ024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (CCZ034 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = eqn (CCZ014 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4)

-- resp CCZ014 at 3: 7 steps
lem-resp-CCZ014-at-3 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-3 c4 = derive (CCZ014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = eqn (Toff024 ∷ Sw01 ∷ []) (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4)

-- resp TOFF014 at 2: 5 steps
lem-resp-TOFF014-at-2 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-2 c4 = derive (Toff014 ∷ []) (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff024 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

-- resp TOFF024 at 1: 2 steps
lem-resp-TOFF024-at-1 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-1 c4 = derive (Toff024 ∷ []) (Sw01 ∷ Toff124 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q11 c4) ∷ []) Eq.refl

-- resp TOFF024 at 3: 7 steps
lem-resp-TOFF024-at-3 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-3 c4 = derive (Toff024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Toff034 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (Toff401 ∷ Sw23 ∷ []) (Sw23 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw2-L c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Toff402 ∷ Sw01 ∷ []) (Sw01 ∷ Toff412 ∷ []) (lem-comm-push-TOFF402-sw0-L c4)

-- resp TOFF401 at 3: 7 steps
lem-resp-TOFF401-at-3 : WsL → ⟪ (Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF401-at-3 c4 = derive (Toff401 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff402 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q13 c4) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (Toff304 ∷ Sw12 ∷ []) (Sw12 ∷ Toff304 ∷ []) (lem-comm-push-TOFF304-sw1-L c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (Toff304 ∷ Sw01 ∷ []) (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4)

-- resp TOFF304 at 2: 4 steps
lem-resp-TOFF304-at-2 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-2 c4 = derive (Toff304 ∷ []) (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q14 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (Toff023 ∷ Sw34 ∷ []) (Sw34 ∷ Toff024 ∷ []) (lem-comm-push-TOFF023-sw3-L c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl 29 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl 9 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q21 : WsL → Eqn
  q21 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl 12 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl 28 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Toff024 ∷ Sw34 ∷ []) (Sw34 ∷ Toff023 ∷ []) (lem-comm-push-TOFF024-sw3-L c4)

-- comm TOFF023 CSd14: 23 steps
lem-comm-TOFF023-CSd14 : WsL → ⟪ (Toff023 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CSd14 c4 = derive (Toff023 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff023 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff034 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CS24⁻ ∷ []) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff034 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Toff403 ∷ Sw12 ∷ []) (Sw12 ∷ Toff403 ∷ []) (lem-comm-push-TOFF403-sw1-L c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Toff403 ∷ Sw01 ∷ []) (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4)

-- resp TOFF402 at 3: 7 steps
lem-resp-TOFF402-at-3 : WsL → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-3 c4 = derive (Toff402 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Toff403 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

-- resp TOFF304 at 1: 2 steps
lem-resp-TOFF304-at-1 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff314 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-1 c4 = derive (Toff304 ∷ []) (Sw01 ∷ Toff314 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q15 c4) ∷ []) Eq.refl

-- resp TOFF401 at 2: 5 steps
lem-resp-TOFF401-at-2 : WsL → ⟪ (Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF401-at-2 c4 = derive (Toff401 ∷ []) (Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff402 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q13 c4) ∷ []) Eq.refl

-- resp TOFF204 at 3: 7 steps
lem-resp-TOFF204-at-3 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-3 c4 = derive (Toff204 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (Toff304 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q14 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q15 c4) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (Toff014 ∷ Sw23 ∷ []) (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4)

-- resp TOFF014 at 3: 7 steps
lem-resp-TOFF014-at-3 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-3 c4 = derive (Toff014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q26 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff024 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

-- resp TOFF403 at 2: 4 steps
lem-resp-TOFF403-at-2 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-2 c4 = derive (Toff403 ∷ []) (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q24 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

-- resp TOFF104 at 2: 5 steps
lem-resp-TOFF104-at-2 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-2 c4 = derive (Toff104 ∷ []) (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (Toff204 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q8 c4) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Toff104 ∷ Sw23 ∷ []) (Sw23 ∷ Toff104 ∷ []) (lem-comm-push-TOFF104-sw2-L c4)

-- resp TOFF104 at 3: 7 steps
lem-resp-TOFF104-at-3 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-3 c4 = derive (Toff104 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff204 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

-- resp TOFF402 at 1: 2 steps
lem-resp-TOFF402-at-1 : WsL → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-1 c4 = derive (Toff402 ∷ []) (Sw01 ∷ Toff412 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

-- resp TOFF403 at 1: 2 steps
lem-resp-TOFF403-at-1 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-1 c4 = derive (Toff403 ∷ []) (Sw01 ∷ Toff413 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q25 c4) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (Toff203 ∷ Sw34 ∷ []) (Sw34 ∷ Toff204 ∷ []) (lem-comm-push-TOFF203-sw3-L c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Toff102 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))
  q30 : WsL → Eqn
  q30 c4 = eqn (Toff204 ∷ Sw34 ∷ []) (Sw34 ∷ Toff203 ∷ []) (lem-comm-push-TOFF204-sw3-L c4)

-- comm TOFF203 CSd14: 23 steps
lem-comm-TOFF203-CSd14 : WsL → ⟪ (Toff203 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CSd14 c4 = derive (Toff203 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff203 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff304 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CS24⁻ ∷ []) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff304 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q30 c4) ∷
   re 0 5 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ023-sw3-L c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ []) (wl 94 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) (wl 91 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (CCZ012 ∷ CK43 ∷ []) (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀))
  q35 : WsL → Eqn
  q35 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ []) (wl 95 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4)

-- comm CCZ023 CK41: 23 steps
lem-comm-CCZ023-CK41 : WsL → ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CK41 c4 = derive (CCZ023 ∷ CK41 ∷ []) (CK41 ∷ CCZ023 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q31 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CCZ034 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CK42 ∷ []) ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (CCZ034 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (CK41 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))

-- comm TOFF023 CK41: 23 steps
lem-comm-TOFF023-CK41 : WsL → ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CK41 c4 = derive (Toff023 ∷ CK41 ∷ []) (CK41 ∷ Toff023 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff034 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CK42 ∷ []) ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q38 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff034 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (CK41 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wl 22 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl 21 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Toff012 ∷ CX34 ∷ []) (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁))
  q42 : WsL → Eqn
  q42 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl 20 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wl 19 c4)

-- comm TOFF023 CX14: 23 steps
lem-comm-TOFF023-CX14 : WsL → ⟪ (Toff023 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CX14 c4 = derive (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff034 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CX13 ∷ []) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CX24 ∷ []) ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff034 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (CX14 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))
  q47 : WsL → Eqn
  q47 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 c4)

-- comm TOFF023 CS14: 23 steps
lem-comm-TOFF023-CS14 : WsL → ⟪ (Toff023 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CS14 c4 = derive (Toff023 ∷ CS14 ∷ []) (CS14 ∷ Toff023 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff034 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 9 (q44 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CS24 ∷ []) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 6 (q46 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff034 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (CS14 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Toff102 ∷ CK43 ∷ []) (CK43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))

-- comm TOFF203 CK41: 23 steps
lem-comm-TOFF203-CK41 : WsL → ⟪ (Toff203 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CK41 c4 = derive (Toff203 ∷ CK41 ∷ []) (CK41 ∷ Toff203 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff304 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CK42 ∷ []) ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff304 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q30 c4) ∷
   re 0 5 (CK41 ∷ []) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (Toff302 ∷ Sw34 ∷ []) (Sw34 ∷ Toff402 ∷ []) (lem-comm-push-TOFF302-sw3-L c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Toff201 ∷ CX34 ∷ []) (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁))
  q52 : WsL → Eqn
  q52 c4 = eqn (Toff402 ∷ Sw34 ∷ []) (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4)

-- comm TOFF302 CX14: 23 steps
lem-comm-TOFF302-CX14 : WsL → ⟪ (Toff302 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CX14 c4 = derive (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff403 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CX13 ∷ []) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CX24 ∷ []) ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q51 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff403 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (CX14 ∷ []) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS))

-- comm TOFF302 CS14: 23 steps
lem-comm-TOFF302-CS14 : WsL → ⟪ (Toff302 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CS14 c4 = derive (Toff302 ∷ CS14 ∷ []) (CS14 ∷ Toff302 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff403 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 9 (q44 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CS24 ∷ []) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff403 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (CS14 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))

-- comm TOFF302 CSd14: 23 steps
lem-comm-TOFF302-CSd14 : WsL → ⟪ (Toff302 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CSd14 c4 = derive (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff403 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CS24⁻ ∷ []) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff403 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))

-- comm CCZ023 CX14: 23 steps
lem-comm-CCZ023-CX14 : WsL → ⟪ (CCZ023 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CX14 c4 = derive (CCZ023 ∷ CX14 ∷ []) (CX14 ∷ CCZ023 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q31 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (CCZ034 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CX13 ∷ []) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CX24 ∷ []) ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q55 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (CCZ034 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (CX14 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (Toff201 ∷ CK43 ∷ []) (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀))

-- comm TOFF302 CK41: 23 steps
lem-comm-TOFF302-CK41 : WsL → ⟪ (Toff302 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CK41 c4 = derive (Toff302 ∷ CK41 ∷ []) (CK41 ∷ Toff302 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (Toff403 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (CK42 ∷ []) ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 3 9 (Toff403 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (CK41 ∷ []) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (Bx0-213 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-123 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw1-L c4)

-- comm push BOX(2;0413) sw1 L: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw1-L : WsL → ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw1-L c4 = derive (Bx2-0413 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-0423 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw 5 (q57 c4) ∷
   re 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 3 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 2 (q57 c4) ∷
   re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 1 6 (Bx1-0423 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (Bx0-123 ∷ Sw01 ∷ []) (Sw01 ∷ Bx1-023 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw0-L c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (CCZ014 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Toff104 ∷ Sw01 ∷ []) (Sw01 ∷ Toff014 ∷ []) (lem-comm-push-TOFF104-sw0-L c4)

-- comm push BOX(1;0423) sw0 L: 8 steps
lem-comm-push-BOX⟨1·0423⟩-sw0-L : WsL → ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw0-L c4 = derive (Bx1-0423 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-1423 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) ∷
   rw 5 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw 3 (q60 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q60 c4) ∷
   rw 0 (q59 c4) ∷
   re 1 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Bx1-023 ∷ Sw23 ∷ []) (Sw23 ∷ Bx1-032 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw2-L c4)

-- comm push BOX(0;1423) sw2 L: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw2-L : WsL → ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw2-L c4 = derive (Bx0-1423 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-1432 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw 5 (q61 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q61 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q10 c4) ∷
   re 1 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Bx1-032 ∷ Sw12 ∷ []) (Sw12 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw1-L c4)

-- comm push BOX(0;1432) sw1 L: 12 steps
lem-comm-push-BOX⟨0·1432⟩-sw1-L : WsL → ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw1-L c4 = derive (Bx0-1432 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-2431 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 5 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff024 ∷ []) ∷
   rw 2 (q62 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff024 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 1 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Bx2-031 ∷ []) (Bx1-032 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw1-R c4)

-- comm push BOX(0;2431) sw1 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw1-R c4 = derive (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 2 (q63 c4) ∷
   re 4 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q63 c4) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw23 ∷ Bx1-032 ∷ []) (Bx1-023 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw2-R c4)

-- comm push BOX(0;1432) sw2 R: 8 steps
lem-comm-push-BOX⟨0·1432⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q66 c4) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-comm-push-TOFF014-sw0-R c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ Bx1-023 ∷ []) (Bx0-123 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw0-R c4)

-- comm push BOX(0;1423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw0-R c4 = derive (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q67 c4) ∷
   rw 5 (q69 c4) ∷
   re 0 6 (Bx1-0423 ∷ []) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw12 ∷ Bx0-123 ∷ []) (Bx0-213 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw1-R c4)

-- comm push BOX(1;0423) sw1 R: 12 steps
lem-comm-push-BOX⟨1·0423⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw1-R c4 = derive (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (Toff204 ∷ []) ∷
   rw 2 (q70 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (Toff204 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CCZ024 ∷ []) ∷
   rw 5 (q70 c4) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw01 ∷ Bx2-43 ∷ []) (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))
  q72 : WsL → Eqn
  q72 c4 = eqn (CCZ124 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Toff412 ∷ Sw01 ∷ []) (Sw01 ∷ Toff402 ∷ []) (lem-comm-push-TOFF412-sw0-L c4)

-- comm push BOX(4;213) sw0 L: 8 steps
lem-comm-push-BOX⟨4·213⟩-sw0-L : WsL → ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·213⟩-sw0-L c4 = derive (Bx4-213 ∷ Sw01 ∷ []) (Sw01 ∷ Bx4-203 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 5 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 1 (q73 c4) ∷
   rw 0 (q72 c4) ∷
   re 1 6 (Bx4-203 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw12 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q76 : WsL → Eqn
  q76 c4 = eqn (Bx2-4103 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-4203 ∷ []) (lem-comm-push-BOX⟨2·4103⟩-sw1-L c4)

-- comm push SBOX(2;4;10;3) sw1 L: 9 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L : WsL → ⟪ (Sb2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L c4 = derive (Sb2-4-10-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-4-20-3 ∷ [])
  (re 0 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) ∷
   rw⁻ 4 (q74 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (Toff302 ∷ []) ∷
   rw⁻ 2 (q75 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (Toff302 ∷ []) ∷
   rw 0 (q76 c4) ∷
   re 1 5 (Sb1-4-20-3 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw01 ∷ Bx1-43 ∷ []) (Bx1-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))
  q78 : WsL → Eqn
  q78 c4 = eqn (Toff401 ∷ Sw01 ∷ []) (Sw01 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw0-L c4)

-- comm push BOX(4;103) sw0 L: 8 steps
lem-comm-push-BOX⟨4·103⟩-sw0-L : WsL → ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw0-L c4 = derive (Bx4-103 ∷ Sw01 ∷ []) (Sw01 ∷ Bx4-013 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) ∷
   rw⁻ 5 (q77 c4) ∷
   rw 4 (q59 c4) ∷
   rw 3 (q78 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q59 c4) ∷
   re 1 6 (Bx4-013 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Bx0-43 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-42 ∷ []) (lem-comm-push-BOX⟨0·43⟩-sw2-L c4)

-- comm push BOX(4;013) sw2 L: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw2-L : WsL → ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw2-L c4 = derive (Bx4-013 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-012 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw 5 (q79 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q12 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q12 c4) ∷
   rw 0 (q10 c4) ∷
   re 1 6 (Bx4-012 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Bx4-012 ∷ Sw12 ∷ []) (Sw12 ∷ Bx4-021 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw1-L c4)

-- comm push BOX(0;4312) sw1 L: 8 steps
lem-comm-push-BOX⟨0·4312⟩-sw1-L : WsL → ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw1-L c4 = derive (Bx0-4312 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-4321 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   rw 5 (q80 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q6 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q2 c4) ∷
   re 1 6 (Bx0-4321 ∷ []) ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (Bx0-41 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-31 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw3-L c4)

-- comm push BOX(4;021) sw3 L: 8 steps
lem-comm-push-BOX⟨4·021⟩-sw3-L : WsL → ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw3-L c4 = derive (Bx4-021 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-021 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   rw 5 (q81 c4) ∷
   rw 4 (q37 c4) ∷
   rw 3 (q52 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q52 c4) ∷
   rw 0 (q37 c4) ∷
   re 1 6 (Bx3-021 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Bx3-021 ∷ Sw23 ∷ []) (Sw23 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw2-L c4)

-- comm push BOX(0;3421) sw2 L: 12 steps
lem-comm-push-BOX⟨0·3421⟩-sw2-L : WsL → ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·3421⟩-sw2-L c4 = derive (Bx0-3421 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-2431 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   rw 5 (q82 c4) ∷
   re 4 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   rw 6 (q9 c4) ∷
   re 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 5 (q9 c4) ∷
   rw 2 (q82 c4) ∷
   re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 3 (q9 c4) ∷
   re 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   rw 2 (q9 c4) ∷
   re 1 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw2-R c4)

-- comm push BOX(0;2431) sw2 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-2431 ∷ []) (Bx0-3421 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw⁻ 2 (q9 c4) ∷
   re 0 3 (CCZ034 ∷ []) ∷
   rw⁻ 3 (q9 c4) ∷
   re 1 3 (Toff034 ∷ []) ∷
   rw 2 (q83 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (Toff034 ∷ []) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CCZ034 ∷ []) ∷
   rw 5 (q83 c4) ∷
   re 0 6 (Bx0-3421 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-comm-push-CCZ023-sw3-R c4)
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ []) (lem-comm-push-TOFF302-sw3-R c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw34 ∷ Bx0-31 ∷ []) (Bx0-41 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw3-R c4)

-- comm push BOX(3;021) sw3 R: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw3-R c4 = derive (Sw34 ∷ Bx3-021 ∷ []) (Bx4-021 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   re 0 6 (Bx4-021 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-comm-push-CCZ034-sw1-R c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Bx4-021 ∷ []) (Bx4-012 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw1-R c4)

-- comm push BOX(0;4321) sw1 R: 8 steps
lem-comm-push-BOX⟨0·4321⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4321⟩-sw1-R c4 = derive (Sw12 ∷ Bx0-4321 ∷ []) (Bx0-4312 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) ∷
   rw 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw 4 (q87 c4) ∷
   rw 5 (q89 c4) ∷
   re 0 6 (Bx0-4312 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ []) (lem-comm-push-TOFF401-sw2-R c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw2-R c4)

-- comm push BOX(4;012) sw2 R: 8 steps
lem-comm-push-BOX⟨4·012⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw2-R c4 = derive (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw 3 (q90 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q91 c4) ∷
   re 0 6 (Bx4-013 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw01 ∷ Bx0-43 ∷ []) (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- comm push BOX(4;013) sw0 R: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw0-R c4 = derive (Sw01 ∷ Bx4-013 ∷ []) (Bx4-103 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q67 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx4-103 ∷ []) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw12 ∷ Bx1-4203 ∷ []) (Bx2-4103 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·4203⟩-sw1-R c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw12 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- comm push SBOX(1;4;20;3) sw1 R: 9 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R c4 = derive (Sw12 ∷ Sb1-4-20-3 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) ∷
   rw 0 (q94 c4) ∷
   re 2 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 2 (q95 c4) ∷
   re 4 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q96 c4) ∷
   re 0 5 (Sb2-4-10-3 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-comm-push-TOFF402-sw0-R c4)

-- comm push BOX(4;203) sw0 R: 8 steps
lem-comm-push-BOX⟨4·203⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw0-R c4 = derive (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q98 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx4-213 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw0-R c4)

-- comm push BOX(0;2431) sw0 R: 8 steps
lem-comm-push-BOX⟨0·2431⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw0-R c4 = derive (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q100 c4) ∷
   re 0 6 (Bx1-2430 ∷ []) ∷ []) Eq.refl

private
  q101 : WsL → Eqn
  q101 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl 122 c4)
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl 123 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw12 ∷ Bx2-130 ∷ []) (Bx1-230 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·130⟩-sw1-R c4)

-- comm push BOX(1;2430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·2430⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·2430⟩-sw1-R c4 = derive (Sw12 ∷ Bx1-2430 ∷ []) (Bx2-1430 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) ∷
   rw⁻ 0 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 5 (q103 c4) ∷
   re 0 6 (Bx2-1430 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw23 ∷ Bx2-1430 ∷ []) (Bx3-1420 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·1430⟩-sw2-R c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (Sb2-1-0-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb2-1-0-3 ∷ []) (c₂ (CS) (Swap))
  q106 : WsL → Eqn
  q106 c4 = eqn (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- comm push SBOX(2;1;43;0) sw2 R: 9 steps
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4 = derive (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) ∷
   rw 0 (q104 c4) ∷
   re 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   re 4 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   re 0 5 (Sb3-1-42-0 ∷ []) ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw34 ∷ Bx3-1420 ∷ []) (Bx4-1320 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨3·1420⟩-sw3-R c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (lem-comm-push-TOFF024-sw3-R c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (Sb3-1-0-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb3-1-0-2 ∷ []) (c₂ (CS) (Swap ↑))
  q110 : WsL → Eqn
  q110 c4 = eqn (Sb⁻3-1-0-2 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻3-1-0-2 ∷ []) (c₂ (CS • CS • CS) (Swap ↑))

-- comm push SBOX(3;1;42;0) sw3 R: 7 steps
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-32-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4 = derive (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ [])
  (re 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   rw 0 (q107 c4) ∷
   rw 1 (q108 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 3 (q108 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   re 0 5 (Sb4-1-32-0 ∷ []) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ Bx4-1320 ∷ []) (Bx4-1230 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·1320⟩-sw2-R c4)
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl 143 c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sb4-1-0-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb4-1-0-2 ∷ []) (c₂ (CS) (Swap))
  q114 : WsL → Eqn
  q114 c4 = eqn (Sb⁻4-1-0-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻4-1-0-2 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- comm push SBOX(4;1;32;0) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-1-32-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4 = derive (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 3 (q112 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   re 0 5 (Sb4-1-23-0 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl 144 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·430⟩-sw1-R c4)

-- comm push BOX(4;1230) sw1 R: 8 steps
lem-comm-push-BOX⟨4·1230⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·1230⟩-sw1-R c4 = derive (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   rw⁻ 0 (q101 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 3 (q115 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 5 (q116 c4) ∷
   re 0 6 (Bx4-2130 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-comm-push-TOFF412-sw0-R c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw01 ∷ Bx2-430 ∷ []) (Bx2-431 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·430⟩-sw0-R c4)

-- comm push BOX(4;2130) sw0 R: 8 steps
lem-comm-push-BOX⟨4·2130⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·2130⟩-sw0-R c4 = derive (Sw01 ∷ Bx4-2130 ∷ []) (Bx4-2031 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw 4 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (Bx4-2031 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw23 ∷ Bx0-213 ∷ []) (Bx0-312 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw2-R c4)

-- comm push BOX(2;0413) sw2 R: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw2-R c4 = derive (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw⁻ 2 (q9 c4) ∷
   re 0 3 (CCZ034 ∷ []) ∷
   rw⁻ 3 (q9 c4) ∷
   re 1 3 (Toff304 ∷ []) ∷
   rw 2 (q120 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (Toff304 ∷ []) ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (CCZ034 ∷ []) ∷
   rw 5 (q120 c4) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw34 ∷ Toff304 ∷ []) (Toff403 ∷ Sw34 ∷ []) (lem-comm-push-TOFF304-sw3-R c4)
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw34 ∷ Bx0-312 ∷ []) (Bx0-412 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·312⟩-sw3-R c4)

-- comm push BOX(3;0412) sw3 R: 8 steps
lem-comm-push-BOX⟨3·0412⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·0412⟩-sw3-R c4 = derive (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   rw 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q121 c4) ∷
   rw 5 (q123 c4) ∷
   re 0 6 (Bx4-0312 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·02⟩-sw2-R c4)

-- comm push BOX(0;412) sw2 R: 8 steps
lem-comm-push-BOX⟨0·412⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·412⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q124 c4) ∷
   re 0 6 (Bx0-413 ∷ []) ∷ []) Eq.refl

private
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw12 ∷ Bx0-413 ∷ []) (Bx0-423 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·413⟩-sw1-R c4)

-- comm push BOX(4;0213) sw1 R: 12 steps
lem-comm-push-BOX⟨4·0213⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·0213⟩-sw1-R c4 = derive (Sw12 ∷ Bx4-0213 ∷ []) (Bx4-0123 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 0 (q1 c4) ∷
   re 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 2 (q125 c4) ∷
   re 4 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 3 (q1 c4) ∷
   re 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q125 c4) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw0-R c4)

-- comm push BOX(0;423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·423⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·423⟩-sw0-R c4 = derive (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q126 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q126 c4) ∷
   re 0 6 (Bx1-423 ∷ []) ∷ []) Eq.refl
