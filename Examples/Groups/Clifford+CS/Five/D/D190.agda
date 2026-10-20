{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D190 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-570a2ddc)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-I-at02132031 ; lem-F4-I-K2-at02132031 ; lem-F4-I-S3-at02132031 ; lem-F4-K2-I-at02132031 ; lem-F4-K2-K2-at02132031 ; lem-F4-K2-S3-at02132031 ; lem-F4-S3-I-at02132031 ; lem-F4-S3-K2-at02132031 ; lem-F4-S3-S3-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-K2-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-CS2-S3-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-K2-CS2-at02132031 ; lem-F4-S3-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-S2-SBOX⟨0·2·43·1⟩-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.Five.D.D147 using (lem-deb-P-hi-eps-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-push-CK40-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CK40-sw1-R ; lem-comm-push-CK41-sw0-R ; lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl 99 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-TR2-570a2ddc c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) [] (lem-deb-P-hi-eps-at02132031 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-CS2-at02132031 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-CS2-at02132031 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K2-at02132031 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2-at02132031 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-K2-at02132031 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-K2-at02132031 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3-at02132031 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-S3-at02132031 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-S3-at02132031 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I-at02132031 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S3-I-at02132031 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K2-I-at02132031 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)

-- deb-P-hi @02132031 part0: 368 steps
lem-deb-P-hi-at02132031-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-P-hi-at02132031-part0 c4 = derive (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
  (rw⁻ 3 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 5 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q13 c4) ∷
   rw 9 (q13 c4) ∷
   rw 10 (q13 c4) ∷
   rw 11 (q13 c4) ∷
   rw 12 (q13 c4) ∷
   rw⁻ 13 (q11 c4) ∷
   rw 14 (q13 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw 18 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw 20 (q15 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw⁻ 28 (q16 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw⁻ 30 (q16 c4) ∷
   rw 31 (q13 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw 33 (q13 c4) ∷
   rw⁻ 34 (q11 c4) ∷
   rw 35 (q13 c4) ∷
   rw 36 (q14 c4) ∷
   rw 37 (q14 c4) ∷
   rw 38 (q14 c4) ∷
   rw 39 (q15 c4) ∷
   rw 40 (q13 c4) ∷
   rw 41 (q13 c4) ∷
   rw⁻ 42 (q16 c4) ∷
   rw⁻ 43 (q16 c4) ∷
   rw⁻ 44 (q16 c4) ∷
   rw 45 (q1 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q17 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q17 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q17 c4) ∷
   rw⁻ 12 (q9 c4) ∷
   rw 13 (q17 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 15 (q17 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw⁻ 18 (q18 c4) ∷
   rw 19 (q19 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw 30 (q17 c4) ∷
   rw⁻ 31 (q9 c4) ∷
   rw 32 (q17 c4) ∷
   rw⁻ 33 (q9 c4) ∷
   rw 34 (q17 c4) ∷
   rw⁻ 35 (q18 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw⁻ 37 (q18 c4) ∷
   rw 38 (q19 c4) ∷
   rw 39 (q17 c4) ∷
   rw 40 (q17 c4) ∷
   rw⁻ 41 (q20 c4) ∷
   rw⁻ 42 (q20 c4) ∷
   rw⁻ 43 (q20 c4) ∷
   rw 44 (q7 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q22 c4) ∷
   rw 6 (q22 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q22 c4) ∷
   rw 9 (q22 c4) ∷
   rw 10 (q22 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q21 c4) ∷
   rw 14 (q22 c4) ∷
   rw 15 (q23 c4) ∷
   rw 16 (q23 c4) ∷
   rw 17 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw 19 (q23 c4) ∷
   rw 20 (q25 c4) ∷
   rw 21 (q25 c4) ∷
   rw 22 (q25 c4) ∷
   rw 23 (q25 c4) ∷
   rw 24 (q25 c4) ∷
   rw 25 (q25 c4) ∷
   rw 26 (q25 c4) ∷
   rw 27 (q25 c4) ∷
   rw 28 (q25 c4) ∷
   rw 29 (q22 c4) ∷
   rw 30 (q21 c4) ∷
   rw 31 (q22 c4) ∷
   rw 32 (q21 c4) ∷
   rw 33 (q22 c4) ∷
   rw 34 (q23 c4) ∷
   rw 35 (q23 c4) ∷
   rw 36 (q23 c4) ∷
   rw 37 (q24 c4) ∷
   rw 38 (q22 c4) ∷
   rw 39 (q22 c4) ∷
   rw 40 (q25 c4) ∷
   rw 41 (q25 c4) ∷
   rw 42 (q25 c4) ∷
   rw 43 (q4 c4) ∷
   rw 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q27 c4) ∷
   rw 6 (q27 c4) ∷
   rw 7 (q27 c4) ∷
   rw 8 (q27 c4) ∷
   rw 9 (q27 c4) ∷
   rw 10 (q26 c4) ∷
   rw 11 (q27 c4) ∷
   rw 12 (q26 c4) ∷
   rw 13 (q27 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw 17 (q15 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw 19 (q28 c4) ∷
   rw 20 (q28 c4) ∷
   rw 21 (q28 c4) ∷
   rw 22 (q28 c4) ∷
   rw 23 (q28 c4) ∷
   rw 24 (q28 c4) ∷
   rw 25 (q28 c4) ∷
   rw 26 (q28 c4) ∷
   rw 27 (q28 c4) ∷
   rw 28 (q27 c4) ∷
   rw 29 (q26 c4) ∷
   rw 30 (q27 c4) ∷
   rw 31 (q26 c4) ∷
   rw 32 (q27 c4) ∷
   rw⁻ 33 (q16 c4) ∷
   rw⁻ 34 (q16 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw 36 (q15 c4) ∷
   rw 37 (q27 c4) ∷
   rw 38 (q27 c4) ∷
   rw 39 (q28 c4) ∷
   rw 40 (q28 c4) ∷
   rw 41 (q28 c4) ∷
   rw 42 (q1 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 80 (q31 c4) ∷
   rw 77 (q31 c4) ∷
   rw 74 (q32 c4) ∷
   rw 71 (q33 c4) ∷
   rw 68 (q33 c4) ∷
   rw 65 (q33 c4) ∷
   rw 62 (q31 c4) ∷
   rw 59 (q34 c4) ∷
   rw 56 (q31 c4) ∷
   rw 53 (q34 c4) ∷
   rw 50 (q31 c4) ∷
   rw 81 (q31 c4) ∷
   rw 78 (q31 c4) ∷
   rw 75 (q32 c4) ∷
   rw 72 (q33 c4) ∷
   rw 69 (q33 c4) ∷
   rw 66 (q33 c4) ∷
   rw 63 (q31 c4) ∷
   rw 60 (q34 c4) ∷
   rw 57 (q31 c4) ∷
   rw 54 (q34 c4) ∷
   rw 51 (q31 c4) ∷
   rw 82 (q31 c4) ∷
   rw 79 (q31 c4) ∷
   rw 76 (q32 c4) ∷
   rw 73 (q33 c4) ∷
   rw 70 (q33 c4) ∷
   rw 67 (q33 c4) ∷
   rw 64 (q31 c4) ∷
   rw 61 (q34 c4) ∷
   rw 58 (q31 c4) ∷
   rw 55 (q34 c4) ∷
   rw 52 (q31 c4) ∷
   rw 83 (q31 c4) ∷
   rw 80 (q31 c4) ∷
   rw 77 (q32 c4) ∷
   rw 74 (q33 c4) ∷
   rw 71 (q33 c4) ∷
   rw 68 (q33 c4) ∷
   rw 65 (q31 c4) ∷
   rw 62 (q34 c4) ∷
   rw 59 (q31 c4) ∷
   rw 56 (q34 c4) ∷
   rw 53 (q31 c4) ∷
   rw 84 (q31 c4) ∷
   rw 81 (q31 c4) ∷
   rw 78 (q32 c4) ∷
   rw 75 (q33 c4) ∷
   rw 72 (q33 c4) ∷
   rw 69 (q33 c4) ∷
   rw 66 (q31 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q31 c4) ∷
   rw 57 (q34 c4) ∷
   rw 54 (q31 c4) ∷
   rw 85 (q31 c4) ∷
   rw 82 (q31 c4) ∷
   rw 79 (q32 c4) ∷
   rw 76 (q33 c4) ∷
   rw 73 (q33 c4) ∷
   rw 70 (q33 c4) ∷
   rw 67 (q31 c4) ∷
   rw 64 (q34 c4) ∷
   rw 61 (q31 c4) ∷
   rw 58 (q34 c4) ∷
   rw 55 (q31 c4) ∷
   rw 86 (q31 c4) ∷
   rw 83 (q31 c4) ∷
   rw 80 (q32 c4) ∷
   rw 77 (q33 c4) ∷
   rw 74 (q33 c4) ∷
   rw 71 (q33 c4) ∷
   rw 68 (q31 c4) ∷
   rw 65 (q34 c4) ∷
   rw 62 (q31 c4) ∷
   rw 59 (q34 c4) ∷
   rw 56 (q31 c4) ∷
   rw 87 (q35 c4) ∷
   rw 84 (q35 c4) ∷
   rw 81 (q36 c4) ∷
   rw 78 (q37 c4) ∷
   rw 75 (q37 c4) ∷
   rw 72 (q37 c4) ∷
   rw 69 (q35 c4) ∷
   rw 66 (q38 c4) ∷
   rw 63 (q35 c4) ∷
   rw 60 (q38 c4) ∷
   rw 57 (q35 c4) ∷
   rw 88 (q31 c4) ∷
   rw 85 (q31 c4) ∷
   rw 82 (q32 c4) ∷
   rw 79 (q33 c4) ∷
   rw 76 (q33 c4) ∷
   rw 73 (q33 c4) ∷
   rw 70 (q31 c4) ∷
   rw 67 (q34 c4) ∷
   rw 64 (q31 c4) ∷
   rw 61 (q34 c4) ∷
   rw 58 (q31 c4) ∷
   rw 89 (q35 c4) ∷
   rw 86 (q35 c4) ∷
   rw 83 (q36 c4) ∷
   rw 80 (q37 c4) ∷
   rw 77 (q37 c4) ∷
   rw 74 (q37 c4) ∷
   rw 71 (q35 c4) ∷
   rw 68 (q38 c4) ∷
   rw 65 (q35 c4) ∷
   rw 62 (q38 c4) ∷
   rw 59 (q35 c4) ∷
   rw 90 (q31 c4) ∷
   rw 87 (q31 c4) ∷
   rw 84 (q32 c4) ∷
   rw 81 (q33 c4) ∷
   rw 78 (q33 c4) ∷
   rw 75 (q33 c4) ∷
   rw 72 (q31 c4) ∷
   rw 69 (q34 c4) ∷
   rw 66 (q31 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q31 c4) ∷
   rw 91 (q39 c4) ∷
   rw 88 (q39 c4) ∷
   rw 85 (q40 c4) ∷
   rw 82 (q41 c4) ∷
   rw 79 (q41 c4) ∷
   rw 76 (q41 c4) ∷
   rw 73 (q39 c4) ∷
   rw 70 (q42 c4) ∷
   rw 67 (q39 c4) ∷
   rw 64 (q42 c4) ∷
   rw 61 (q39 c4) ∷
   rw 92 (q39 c4) ∷
   rw 89 (q39 c4) ∷
   rw 86 (q40 c4) ∷
   rw 83 (q41 c4) ∷
   rw 80 (q41 c4) ∷
   rw 77 (q41 c4) ∷
   rw 74 (q39 c4) ∷
   rw 71 (q42 c4) ∷
   rw 68 (q39 c4) ∷
   rw 65 (q42 c4) ∷
   rw 62 (q39 c4) ∷
   rw 93 (q39 c4) ∷
   rw 90 (q39 c4) ∷
   rw 87 (q40 c4) ∷
   rw 84 (q41 c4) ∷
   rw 81 (q41 c4) ∷
   rw 78 (q41 c4) ∷
   rw 75 (q39 c4) ∷
   rw 72 (q42 c4) ∷
   rw 69 (q39 c4) ∷
   rw 66 (q42 c4) ∷
   rw 63 (q39 c4) ∷
   rw 94 (q43 c4) ∷
   rw 91 (q43 c4) ∷
   rw 88 (q44 c4) ∷
   rw 85 (q45 c4) ∷
   rw 82 (q45 c4) ∷
   rw 79 (q45 c4) ∷
   rw 76 (q43 c4) ∷
   rw 73 (q46 c4) ∷
   rw 70 (q43 c4) ∷
   rw 67 (q46 c4) ∷
   rw 64 (q43 c4) ∷
   rw 95 (q39 c4) ∷
   rw 92 (q39 c4) ∷
   rw 89 (q40 c4) ∷
   rw 86 (q41 c4) ∷
   rw 83 (q41 c4) ∷
   rw 80 (q41 c4) ∷
   rw 77 (q39 c4) ∷
   rw 74 (q42 c4) ∷
   rw 71 (q39 c4) ∷
   rw 68 (q42 c4) ∷
   rw 65 (q39 c4) ∷
   rw 96 (q47 c4) ∷ []) Eq.refl
