{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D182 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0227 ; wl0283 ; wl0341 ; wl0402 ; wl0550 ; wl0602 ; wl0661 ; wl0833 ; wl0834 ; wl0844 ; wl0848 ; wl0849 ; wl0850 ; wl0851 ; wl0852 ; wl0853 ; wl0854 ; wl0855 ; wl0856 ; wl0857 ; wl0858 ; wl0859 ; wl0860 ; wl0861 ; wl0862 ; wp0142 ; wp0143 ; wp0352 ; wp0411 ; wp0415 ; wp0432 ; wp0440 ; wp0441 ; wp0442 ; wp0443 ; wp0444 ; wp0445 ; wp0446 ; wp0447 ; wp0448)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at12213443 ; lem-sym23-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-beta-T-at12213443 ; lem-beta-T-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F0-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D181 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 ; lem-beta-T-at01122440)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp0142 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0143 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl0550 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ CS12⁻ ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wl0853 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wl0854 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at122441 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (X ↑))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ []) (wl0844 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0833 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (wp0352 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS24 ∷ X4 ∷ CX31 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ X4 ∷ CS24 ∷ []) (wl0834 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS24 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS24 ∷ []) (wp0432 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS24 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24 ∷ []) (wp0411 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ []) (c₃ ((K • iI) ↑ ↑) (X ↑))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ013 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ013 ∷ []) (wl0855 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (K2 ∷ CS24 ∷ K2⁻ ∷ X4 ∷ Toff024 ∷ X4 ∷ []) (X4 ∷ Toff024 ∷ X4 ∷ K2 ∷ CS24 ∷ K2⁻ ∷ []) (wp0441 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wp0442 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ []) (X4 ∷ Toff034 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wp0443 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx1-2430 ∷ []) (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (lem-beta-T-at01122440 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CX04 ∷ []) (wp0444 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl0856 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS24⁻ ∷ X4 ∷ CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ X4 ∷ CS24⁻ ∷ []) (wl0857 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (X4 ∷ CX30 ∷ X4 ∷ CS24⁻ ∷ []) (wp0445 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) (wp0446 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CS24⁻ ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS24⁻ ∷ []) (wp0415 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (X ↑))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) (wl0858 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) (X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) (wp0447 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (wl0661 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sb0-2-43-1 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-2-43-1 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at122441 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl0402 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0227 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (K3⁻ ∷ K3 ∷ []) [] (wl0859 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0860 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0861 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wl0862 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2413 ∷ []) (lem-sym34-at122441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at12213443 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) (wp0448 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (c₄ (K ↑ ↑ ↑) (X))
  q45 : Ws → Eqn
  q45 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q46 : Ws → Eqn
  q46 c4 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wl0341 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS34 ∷ X4 ∷ K0⁻ ∷ X4 ∷ []) (X4 ∷ K0⁻ ∷ X4 ∷ CS34 ∷ []) (wl0848 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0602 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS34 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34 ∷ []) (wp0440 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS34 ∷ X4 ∷ CX21 ∷ X4 ∷ []) (X4 ∷ CX21 ∷ X4 ∷ CS34 ∷ []) (wl0849 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS34 ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS34 ∷ []) (wl0850 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS34 ∷ X4 ∷ CS01 ∷ X4 ∷ []) (X4 ∷ CS01 ∷ X4 ∷ CS34 ∷ []) (wl0851 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS34 ∷ X4 ∷ K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ X4 ∷ CS34 ∷ []) (wl0852 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (K3⁻ ∷ X4 ∷ []) (X4 ∷ K3⁻ ∷ []) (c₄ ((K • iI) ↑ ↑ ↑) (X))
  q55 : Ws → Eqn
  q55 c4 = eqn (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (K • iI))
  q56 : Ws → Eqn
  q56 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4)

-- F4 CS23^0|CS01^1 part0: 500 steps
lem-F4-CS23ᵖ0∣CS01ᵖ1-part0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS01ᵖ1-part0 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ Bx0-2431 ∷ X4 ∷ X4 ∷ Toff134 ∷ X4 ∷ X4 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 13 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q6 c4) ∷
   re 10 1 (Sb0-2-1-3 ∷ []) ∷
   re 16 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 11 (q11 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 22 (q12 c4) ∷
   rw⁻ 19 (q13 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q5 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw 12 (q17 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw⁻ 0 (q18 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw 4 (q19 c4) ∷
   re 4 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   re 10 1 (CS02 ∷ []) ∷
   re 16 1 (CS02⁻ ∷ []) ∷
   rw⁻ 9 (q20 c4) ∷
   re 22 1 (Sb1-2-0-3 ∷ []) ∷
   re 28 1 (Sb⁻1-2-0-3 ∷ []) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw 15 (q17 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 25 (q26 c4) ∷
   rw⁻ 22 (q27 c4) ∷
   rw⁻ 19 (q26 c4) ∷
   rw⁻ 16 (q28 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 18 (q24 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 18 (q17 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw 21 (q17 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 24 (q29 c4) ∷
   rw 23 (q30 c4) ∷
   rw⁻ 22 (q29 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw 24 (q17 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 9 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 11 (q24 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 19 (q26 c4) ∷
   rw⁻ 16 (q27 c4) ∷
   rw⁻ 13 (q26 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q5 c4) ∷
   rw⁻ 12 (q24 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw 12 (q17 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw 15 (q17 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw 17 (q30 c4) ∷
   rw⁻ 16 (q29 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 18 (q17 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   re 16 5 (Sb1-2-43-0 ∷ []) ∷
   rw⁻ 16 (q19 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   re 9 1 (CS12 ∷ []) ∷
   re 15 1 (CS12⁻ ∷ []) ∷
   rw⁻ 8 (q6 c4) ∷
   re 12 1 (Sb0-2-1-3 ∷ []) ∷
   re 18 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 13 (q11 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 14 (q11 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw 14 (q17 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 8 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw 6 (q19 c4) ∷
   re 6 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   re 12 1 (CS02 ∷ []) ∷
   re 18 1 (CS02⁻ ∷ []) ∷
   rw⁻ 11 (q20 c4) ∷
   re 24 1 (Sb1-2-0-3 ∷ []) ∷
   re 30 1 (Sb⁻1-2-0-3 ∷ []) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw 17 (q17 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw 19 (q24 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 30 (q25 c4) ∷
   rw⁻ 27 (q26 c4) ∷
   rw⁻ 24 (q27 c4) ∷
   rw⁻ 21 (q26 c4) ∷
   rw⁻ 18 (q28 c4) ∷
   rw 21 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw 23 (q5 c4) ∷
   rw 24 (q5 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 20 (q17 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw⁻ 20 (q9 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw 23 (q17 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw⁻ 23 (q9 c4) ∷
   rw⁻ 26 (q29 c4) ∷
   rw 25 (q30 c4) ∷
   rw⁻ 24 (q29 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q17 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 13 (q24 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw⁻ 21 (q26 c4) ∷
   rw⁻ 18 (q27 c4) ∷
   rw⁻ 15 (q26 c4) ∷
   rw⁻ 12 (q28 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw 14 (q17 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw 17 (q17 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 20 (q29 c4) ∷
   rw 19 (q30 c4) ∷
   rw⁻ 18 (q29 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 20 (q17 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw⁻ 18 (q22 c4) ∷
   rw 19 (q5 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   re 18 5 (Sb1-2-43-0 ∷ []) ∷
   rw⁻ 18 (q19 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q4 c4) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw⁻ 12 (q36 c4) ∷
   rw⁻ 15 (q36 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw⁻ 13 (q37 c4) ∷
   re 17 1 (Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 10 (q38 c4) ∷
   re 8 1 (CS12 ∷ []) ∷
   rw⁻ 7 (q39 c4) ∷
   re 11 1 (Sb0-2-1-3 ∷ []) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 2 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   rw⁻ 9 (q44 c4) ∷
   rw 8 (q45 c4) ∷
   rw⁻ 7 (q44 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 14 (q47 c4) ∷
   rw 12 (q48 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw⁻ 23 (q49 c4) ∷
   rw⁻ 20 (q50 c4) ∷
   rw⁻ 17 (q51 c4) ∷
   rw⁻ 14 (q50 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw⁻ 13 (q48 c4) ∷
   rw⁻ 8 (q53 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw 10 (q46 c4) ∷
   rw⁻ 11 (q54 c4) ∷
   rw 10 (q55 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw⁻ 1 (q44 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 8 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 17 (q49 c4) ∷
   rw⁻ 14 (q50 c4) ∷
   rw⁻ 11 (q51 c4) ∷
   rw⁻ 8 (q50 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 7 (q48 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q5 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 5 (q54 c4) ∷
   rw 4 (q55 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   rw 5 (q56 c4) ∷
   rw 5 (q57 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q5 c4) ∷
   re 5 5 (Sb0-2-43-1 ∷ []) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷ []) Eq.refl
