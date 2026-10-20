{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D012 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0379 ; wl0382 ; wl0383 ; wl0384 ; wl0385 ; wl0393 ; wl0402 ; wl0404 ; wl0409 ; wl0410 ; wl0411 ; wl0412 ; wl0413 ; wl0414 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0424 ; wl0425 ; wl0426 ; wl0427 ; wl0428 ; wl0429 ; wl0430 ; wl0431 ; wl0432 ; wl0446 ; wp0130 ; wp0142 ; wp0143 ; wp0144 ; wp0146 ; wp0147 ; wp0148 ; wp0149 ; wp0150 ; wp0151 ; wp0152)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at0210243143 ; lem-sym23-at0210213443 ; lem-sym23-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 ; lem-beta-T-at0210213443 ; lem-sym23-at02102441 ; lem-sym34-at0210243143)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X1 ∷ X1 ∷ []) [] (wl0379 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS01⁻ ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS01⁻ ∷ []) (wl0425 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ CS01⁻ ∷ []) (wp0146 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS01⁻ ∷ []) (wp0147 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0426 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS01⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS01⁻ ∷ []) (wl0427 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (S1 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ S1 ∷ []) (wl0382 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (S1 ∷ X1 ∷ Toff204 ∷ X1 ∷ []) (X1 ∷ Toff204 ∷ X1 ∷ S1 ∷ []) (wp0130 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (S1 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ S1 ∷ []) (wl0383 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (S1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ S1 ∷ []) (wl0385 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (S1 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ S1 ∷ []) (wl0384 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X1 ∷ ι⁻ ∷ []) (ι⁻ ∷ X1 ∷ []) (zc⁻)
  q15 : Ws → Eqn
  q15 c4 = eqn (Sb⁻2-0-41-3 ∷ ι⁻ ∷ []) (ι⁻ ∷ Sb⁻2-0-41-3 ∷ []) (zc⁻)
  q16 : Ws → Eqn
  q16 c4 = eqn (CK10⁻ ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ []) (wl0424 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CK10⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CK10⁻ ∷ []) (wl0446 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K0⁻ ∷ X1 ∷ []) (X1 ∷ K0⁻ ∷ []) (c₁ (K • iI) (X))
  q21 : Ws → Eqn
  q21 c4 = eqn (K0⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (CCZ ↑))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0393 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS01⁻ ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS01⁻ ∷ []) (wp0148 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS01⁻ ∷ X1 ∷ CX43 ∷ X1 ∷ []) (X1 ∷ CX43 ∷ X1 ∷ CS01⁻ ∷ []) (wl0428 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23⁻ ∷ X1 ∷ []) (X1 ∷ CS23⁻ ∷ X1 ∷ CS01⁻ ∷ []) (wl0429 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01⁻ ∷ X1 ∷ CS23 ∷ X1 ∷ []) (X1 ∷ CS23 ∷ X1 ∷ CS01⁻ ∷ []) (wl0430 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff201 ∷ X1 ∷ []) (X1 ∷ Toff201 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wl0431 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0149 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ []) (wp0150 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS03 ∷ Toff314 ∷ CS03⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0151 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff314 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff314 ∷ []) (wp0152 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff201 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ Toff201 ∷ []) (wl0432 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (X1 ∷ CCZ234 ∷ []) (CCZ234 ∷ X1 ∷ []) (c₂ (X ↑) (CCZ))
  q35 : Ws → Eqn
  q35 c4 = eqn (CK10⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10⁻ ∷ []) (c₂ (S ↑ • CK₁₀) (CCZ))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ []) (wl0419 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (K3 ∷ X1 ∷ []) (X1 ∷ K3 ∷ []) (wl0418 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0404 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS13 ∷ X1 ∷ CCZ123 ∷ X1 ∷ []) (X1 ∷ CCZ123 ∷ X1 ∷ CS13 ∷ []) (wl0414 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CS13 ∷ X1 ∷ K2⁻ ∷ X1 ∷ []) (X1 ∷ K2⁻ ∷ X1 ∷ CS13 ∷ []) (wl0413 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CS13 ∷ X1 ∷ CS02 ∷ X1 ∷ []) (X1 ∷ CS02 ∷ X1 ∷ CS13 ∷ []) (wl0412 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS13 ∷ X1 ∷ CX04 ∷ X1 ∷ []) (X1 ∷ CX04 ∷ X1 ∷ CS13 ∷ []) (wp0144 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CS13 ∷ X1 ∷ CS24⁻ ∷ X1 ∷ []) (X1 ∷ CS24⁻ ∷ X1 ∷ CS13 ∷ []) (wl0411 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS13 ∷ X1 ∷ CS24 ∷ X1 ∷ []) (X1 ∷ CS24 ∷ X1 ∷ CS13 ∷ []) (wl0410 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CS13 ∷ X1 ∷ K2 ∷ X1 ∷ []) (X1 ∷ K2 ∷ X1 ∷ CS13 ∷ []) (wl0409 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS13 ∷ X1 ∷ Toff314 ∷ X1 ∷ []) (X1 ∷ Toff314 ∷ X1 ∷ CS13 ∷ []) (wl0415 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS13 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ []) (wl0417 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS13 ∷ X1 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CS03 ∷ X1 ∷ CS13 ∷ []) (wl0416 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)

-- F1 CS-K0 [rhs shape] part6: 367 steps
lem-F1-CS-K0-rhs-shape-part6 : Ws → ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0-rhs-shape-part6 c4 = derive (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx⁻2-0413 ∷ X1 ∷ CS01⁻ ∷ S1 ∷ ι⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ X1 ∷ S1 ∷ X1 ∷ X1 ∷ CS14⁻ ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ Sb2-0-41-3 ∷ X1 ∷ S1 ∷ CS14⁻ ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ CK10 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ Sb⁻2-0-41-3 ∷ CK10⁻ ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sb2-0-3-1 ∷ K3 ∷ CS13 ∷ X1 ∷ Sb2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Sb⁻2-0-3-1 ∷ X1 ∷ X1 ∷ Toff314 ∷ X1 ∷ X1 ∷ Bx2-0341 ∷ X1 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K3⁻ ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ Sb⁻2-0-41-3 ∷ X1 ∷ X1 ∷ CS14 ∷ X1 ∷ CS14 ∷ S1⁻ ∷ X1 ∷ S1⁻ ∷ X1 ∷ S4⁻ ∷ Sb2-0-41-3 ∷ [])
  (re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 45 (q1 c4) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   re 44 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 44 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw 56 (q2 c4) ∷
   rw 56 (q3 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 60 (q1 c4) ∷
   rw⁻ 63 (q1 c4) ∷
   rw⁻ 64 (q4 c4) ∷
   rw⁻ 61 (q5 c4) ∷
   rw⁻ 58 (q4 c4) ∷
   rw⁻ 55 (q5 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw⁻ 57 (q3 c4) ∷
   rw⁻ 57 (q2 c4) ∷
   rw⁻ 52 (q6 c4) ∷
   re 50 1 (CS03⁻ ∷ []) ∷
   rw⁻ 49 (q7 c4) ∷
   re 51 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 46 (q6 c4) ∷
   re 44 1 (CS03 ∷ []) ∷
   rw⁻ 43 (q8 c4) ∷
   re 45 1 (Sb2-0-3-1 ∷ []) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   re 45 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 45 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw 57 (q2 c4) ∷
   rw 57 (q3 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 65 (q9 c4) ∷
   rw⁻ 62 (q10 c4) ∷
   rw⁻ 59 (q9 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw⁻ 58 (q2 c4) ∷
   rw⁻ 53 (q11 c4) ∷
   re 51 1 (CS03⁻ ∷ []) ∷
   rw⁻ 50 (q12 c4) ∷
   re 52 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 47 (q11 c4) ∷
   re 45 1 (CS03 ∷ []) ∷
   rw⁻ 44 (q13 c4) ∷
   re 46 1 (Sb2-0-3-1 ∷ []) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   re 46 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 47 (q14 c4) ∷
   rw 46 (q15 c4) ∷
   rw 45 (q14 c4) ∷
   rw⁻ 39 (q16 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw 36 (q16 c4) ∷
   re 34 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 35 (q1 c4) ∷
   rw⁻ 38 (q1 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw⁻ 44 (q1 c4) ∷
   rw 46 (q2 c4) ∷
   rw 46 (q3 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw⁻ 54 (q4 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw 48 (q1 c4) ∷
   rw 49 (q1 c4) ∷
   rw 50 (q1 c4) ∷
   rw⁻ 47 (q3 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   rw⁻ 42 (q6 c4) ∷
   re 40 1 (CS03⁻ ∷ []) ∷
   rw⁻ 39 (q7 c4) ∷
   re 41 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 36 (q6 c4) ∷
   re 34 1 (CS03 ∷ []) ∷
   rw⁻ 33 (q8 c4) ∷
   re 35 1 (Sb2-0-3-1 ∷ []) ∷
   rw 36 (q1 c4) ∷
   rw 37 (q1 c4) ∷
   rw 38 (q1 c4) ∷
   rw 39 (q1 c4) ∷
   re 35 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 35 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw 47 (q2 c4) ∷
   rw 47 (q18 c4) ∷
   rw 47 (q19 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 57 (q20 c4) ∷
   rw⁻ 56 (q21 c4) ∷
   rw⁻ 55 (q20 c4) ∷
   rw 57 (q22 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 64 (q1 c4) ∷
   rw⁻ 67 (q1 c4) ∷
   rw⁻ 68 (q23 c4) ∷
   rw⁻ 65 (q24 c4) ∷
   rw⁻ 62 (q25 c4) ∷
   rw⁻ 59 (q24 c4) ∷
   rw⁻ 56 (q26 c4) ∷
   rw 59 (q1 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw⁻ 58 (q22 c4) ∷
   rw⁻ 59 (q20 c4) ∷
   rw⁻ 58 (q21 c4) ∷
   rw⁻ 57 (q20 c4) ∷
   rw⁻ 52 (q27 c4) ∷
   rw⁻ 51 (q20 c4) ∷
   rw⁻ 50 (q21 c4) ∷
   rw⁻ 49 (q20 c4) ∷
   rw 51 (q22 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 61 (q1 c4) ∷
   rw⁻ 62 (q23 c4) ∷
   rw⁻ 59 (q24 c4) ∷
   rw⁻ 56 (q25 c4) ∷
   rw⁻ 53 (q24 c4) ∷
   rw⁻ 50 (q26 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw 56 (q1 c4) ∷
   rw⁻ 52 (q22 c4) ∷
   rw⁻ 53 (q20 c4) ∷
   rw⁻ 52 (q21 c4) ∷
   rw⁻ 51 (q20 c4) ∷
   rw⁻ 46 (q27 c4) ∷
   rw 51 (q1 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw⁻ 50 (q19 c4) ∷
   rw 50 (q28 c4) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 43 (q29 c4) ∷
   re 35 1 (CS03 ∷ []) ∷
   re 41 1 (CS03⁻ ∷ []) ∷
   rw⁻ 34 (q30 c4) ∷
   re 38 1 (Sb2-0-3-1 ∷ []) ∷
   re 44 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw 39 (q1 c4) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   re 38 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 38 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 39 (q1 c4) ∷
   rw⁻ 42 (q1 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw 50 (q2 c4) ∷
   rw 50 (q3 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw⁻ 58 (q4 c4) ∷
   rw⁻ 55 (q5 c4) ∷
   rw⁻ 52 (q4 c4) ∷
   rw⁻ 49 (q5 c4) ∷
   rw 52 (q1 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw⁻ 51 (q3 c4) ∷
   rw⁻ 51 (q2 c4) ∷
   rw⁻ 46 (q6 c4) ∷
   re 44 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q7 c4) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 40 (q6 c4) ∷
   re 38 1 (CS03 ∷ []) ∷
   rw⁻ 37 (q8 c4) ∷
   re 39 1 (Sb2-0-3-1 ∷ []) ∷
   rw 40 (q1 c4) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw 43 (q1 c4) ∷
   re 39 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 39 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw⁻ 46 (q1 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw 51 (q2 c4) ∷
   rw 51 (q3 c4) ∷
   rw⁻ 52 (q1 c4) ∷
   rw⁻ 55 (q1 c4) ∷
   rw⁻ 58 (q1 c4) ∷
   rw⁻ 59 (q9 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 53 (q9 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw 53 (q1 c4) ∷
   rw 54 (q1 c4) ∷
   rw 55 (q1 c4) ∷
   rw⁻ 52 (q3 c4) ∷
   rw⁻ 52 (q2 c4) ∷
   rw⁻ 47 (q11 c4) ∷
   re 45 1 (CS03⁻ ∷ []) ∷
   rw⁻ 44 (q12 c4) ∷
   re 46 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 41 (q11 c4) ∷
   re 39 1 (CS03 ∷ []) ∷
   rw⁻ 38 (q13 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw 41 (q1 c4) ∷
   rw 42 (q1 c4) ∷
   rw 43 (q1 c4) ∷
   rw 44 (q1 c4) ∷
   re 40 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 41 (q14 c4) ∷
   rw 40 (q15 c4) ∷
   rw 39 (q14 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   re 46 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 46 1 (CS03 ∷ []) ∷
   re 48 1 (CS03⁻ ∷ []) ∷
   rw⁻ 43 (q31 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ []) ∷
   re 45 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 46 (q32 c4) ∷
   rw 50 (q2 c4) ∷
   rw 50 (q18 c4) ∷
   rw 50 (q19 c4) ∷
   rw⁻ 47 (q33 c4) ∷
   rw 50 (q34 c4) ∷
   rw 49 (q35 c4) ∷
   rw 48 (q34 c4) ∷
   rw⁻ 49 (q33 c4) ∷
   rw 52 (q34 c4) ∷
   rw 51 (q35 c4) ∷
   rw 50 (q34 c4) ∷
   rw⁻ 47 (q19 c4) ∷
   rw 47 (q28 c4) ∷
   rw⁻ 47 (q2 c4) ∷
   re 43 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 42 (q36 c4) ∷
   re 42 1 (Sb2-0-3-1 ∷ []) ∷
   rw 41 (q37 c4) ∷
   re 41 1 (CS03 ∷ []) ∷
   rw⁻ 40 (q36 c4) ∷
   re 40 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 44 (q38 c4) ∷
   rw⁻ 43 (q39 c4) ∷
   rw 42 (q40 c4) ∷
   rw⁻ 41 (q39 c4) ∷
   rw 45 (q41 c4) ∷
   re 43 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 44 (q1 c4) ∷
   rw⁻ 47 (q1 c4) ∷
   rw⁻ 50 (q1 c4) ∷
   rw⁻ 53 (q1 c4) ∷
   rw 55 (q2 c4) ∷
   rw 55 (q3 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 63 (q42 c4) ∷
   rw⁻ 61 (q43 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 66 (q44 c4) ∷
   rw 64 (q45 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 71 (q1 c4) ∷
   rw⁻ 74 (q1 c4) ∷
   rw⁻ 75 (q46 c4) ∷
   rw⁻ 72 (q47 c4) ∷
   rw⁻ 69 (q48 c4) ∷
   rw⁻ 66 (q47 c4) ∷
   rw⁻ 63 (q49 c4) ∷
   rw 66 (q1 c4) ∷
   rw 67 (q1 c4) ∷
   rw 68 (q1 c4) ∷
   rw 69 (q1 c4) ∷
   rw⁻ 65 (q45 c4) ∷
   rw⁻ 60 (q50 c4) ∷
   rw 63 (q1 c4) ∷
   rw 64 (q1 c4) ∷
   rw 62 (q43 c4) ∷
   rw⁻ 57 (q42 c4) ∷
   rw⁻ 55 (q43 c4) ∷
   rw⁻ 56 (q1 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 60 (q44 c4) ∷
   rw 58 (q45 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw⁻ 62 (q1 c4) ∷
   rw⁻ 65 (q1 c4) ∷
   rw⁻ 68 (q1 c4) ∷
   rw⁻ 69 (q46 c4) ∷
   rw⁻ 66 (q47 c4) ∷
   rw⁻ 63 (q48 c4) ∷
   rw⁻ 60 (q47 c4) ∷
   rw⁻ 57 (q49 c4) ∷
   rw 60 (q1 c4) ∷
   rw 61 (q1 c4) ∷
   rw 62 (q1 c4) ∷
   rw 63 (q1 c4) ∷
   rw⁻ 59 (q45 c4) ∷
   rw⁻ 54 (q50 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 56 (q43 c4) ∷
   rw 57 (q1 c4) ∷
   rw 58 (q1 c4) ∷
   rw 59 (q1 c4) ∷
   rw⁻ 56 (q3 c4) ∷
   rw⁻ 56 (q2 c4) ∷
   rw⁻ 51 (q51 c4) ∷
   re 49 1 (CS03⁻ ∷ []) ∷
   rw⁻ 48 (q52 c4) ∷
   re 50 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 45 (q51 c4) ∷
   re 43 1 (CS03 ∷ []) ∷
   rw⁻ 42 (q53 c4) ∷
   re 44 1 (Sb2-0-3-1 ∷ []) ∷
   rw 45 (q1 c4) ∷
   rw 46 (q1 c4) ∷
   rw 47 (q1 c4) ∷
   rw 48 (q1 c4) ∷
   re 44 5 (Sb⁻2-0-41-3 ∷ []) ∷
   re 44 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw⁻ 45 (q1 c4) ∷
   rw⁻ 48 (q1 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw⁻ 54 (q1 c4) ∷
   rw 56 (q2 c4) ∷
   rw 56 (q54 c4) ∷
   rw 56 (q55 c4) ∷ []) Eq.refl
