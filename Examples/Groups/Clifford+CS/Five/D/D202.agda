{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D202 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-d2b6eba7)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K3-at02132031 ; lem-F4-I-S2-at02132031 ; lem-F4-K3-K3-at02132031 ; lem-F4-K3-S2-at02132031 ; lem-F4-S2-K3-at02132031 ; lem-F4-S2-S2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-S2-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-S2-SBOX⟨0·2·43·1⟩-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F4-CS2-K3-at02132031 ; lem-F4-K3-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.Five.D.D151 using (lem-deb-AD-eps-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L ; lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-push-CK40-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q15 : Ws → Eqn
  q15 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl 99 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q22 : Ws → Eqn
  q22 c4 = eqn (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (CK43 ∷ CS34 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-TR2-d2b6eba7 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q28 : Ws → Eqn
  q28 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) [] (lem-deb-AD-eps-at02132031 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-CS2-at02132031 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-CS2-at02132031 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at02132031 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at02132031 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-K3-at02132031 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-K3-at02132031 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S2-at02132031 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S2-at02132031 c4)

-- deb-AD @02132031 part0: 442 steps
lem-deb-AD-at02132031-part0 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS14 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-AD-at02132031-part0 c4 = derive (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ CS14 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw⁻ 30 (q1 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw 28 (q3 c4) ∷
   rw 27 (q4 c4) ∷
   rw 26 (q4 c4) ∷
   rw 25 (q3 c4) ∷
   rw 24 (q5 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw 22 (q3 c4) ∷
   rw 21 (q4 c4) ∷
   rw 20 (q4 c4) ∷
   rw 19 (q3 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw 17 (q3 c4) ∷
   rw 16 (q4 c4) ∷
   rw 15 (q4 c4) ∷
   rw 14 (q3 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw 12 (q4 c4) ∷
   rw 11 (q4 c4) ∷
   rw 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q4 c4) ∷
   rw 0 (q3 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 30 (q8 c4) ∷
   rw 29 (q9 c4) ∷
   rw 28 (q10 c4) ∷
   rw 27 (q10 c4) ∷
   rw 26 (q9 c4) ∷
   rw 25 (q11 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 21 (q10 c4) ∷
   rw 20 (q9 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw 18 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 16 (q10 c4) ∷
   rw 15 (q9 c4) ∷
   rw⁻ 14 (q8 c4) ∷
   rw 13 (q10 c4) ∷
   rw 12 (q10 c4) ∷
   rw 11 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw 8 (q11 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw 2 (q10 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw 30 (q15 c4) ∷
   rw 29 (q16 c4) ∷
   rw 28 (q16 c4) ∷
   rw 27 (q15 c4) ∷
   rw 26 (q17 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw 24 (q15 c4) ∷
   rw 23 (q16 c4) ∷
   rw 22 (q16 c4) ∷
   rw 21 (q15 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   rw 19 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw 17 (q16 c4) ∷
   rw 16 (q15 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw 14 (q16 c4) ∷
   rw 13 (q16 c4) ∷
   rw 12 (q16 c4) ∷
   rw 11 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw 3 (q16 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 33 (q1 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw 31 (q6 c4) ∷
   rw 30 (q19 c4) ∷
   rw 29 (q19 c4) ∷
   rw 28 (q6 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw 25 (q6 c4) ∷
   rw 24 (q19 c4) ∷
   rw 23 (q19 c4) ∷
   rw 22 (q6 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw 20 (q6 c4) ∷
   rw 19 (q19 c4) ∷
   rw 18 (q19 c4) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw 15 (q19 c4) ∷
   rw 14 (q19 c4) ∷
   rw 13 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw 6 (q6 c4) ∷
   rw 5 (q19 c4) ∷
   rw 4 (q19 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q22 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   rw 6 (q24 c4) ∷
   rw 7 (q24 c4) ∷
   rw 8 (q24 c4) ∷
   rw 9 (q24 c4) ∷
   rw 10 (q24 c4) ∷
   rw 11 (q24 c4) ∷
   rw 12 (q24 c4) ∷
   rw 13 (q24 c4) ∷
   rw 14 (q21 c4) ∷
   rw 15 (q24 c4) ∷
   rw 16 (q21 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q2 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw 23 (q23 c4) ∷
   rw 24 (q23 c4) ∷
   rw 25 (q23 c4) ∷
   rw 26 (q23 c4) ∷
   rw 27 (q23 c4) ∷
   rw 28 (q23 c4) ∷
   rw 29 (q23 c4) ∷
   rw 30 (q23 c4) ∷
   rw 31 (q23 c4) ∷
   rw 32 (q24 c4) ∷
   rw 33 (q21 c4) ∷
   rw 34 (q24 c4) ∷
   rw 35 (q21 c4) ∷
   rw 36 (q24 c4) ∷
   rw⁻ 37 (q19 c4) ∷
   rw⁻ 38 (q19 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw 40 (q2 c4) ∷
   rw 41 (q24 c4) ∷
   rw 42 (q24 c4) ∷
   rw 43 (q23 c4) ∷
   rw 44 (q23 c4) ∷
   rw 45 (q23 c4) ∷
   rw 46 (q1 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   rw 5 (q26 c4) ∷
   rw 6 (q26 c4) ∷
   rw 7 (q26 c4) ∷
   rw 8 (q26 c4) ∷
   rw 9 (q26 c4) ∷
   rw 10 (q26 c4) ∷
   rw 11 (q26 c4) ∷
   rw 12 (q26 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw 14 (q26 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 16 (q26 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 20 (q14 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw⁻ 26 (q25 c4) ∷
   rw⁻ 27 (q25 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 29 (q25 c4) ∷
   rw⁻ 30 (q25 c4) ∷
   rw 31 (q26 c4) ∷
   rw⁻ 32 (q18 c4) ∷
   rw 33 (q26 c4) ∷
   rw⁻ 34 (q18 c4) ∷
   rw 35 (q26 c4) ∷
   rw⁻ 36 (q16 c4) ∷
   rw⁻ 37 (q16 c4) ∷
   rw⁻ 38 (q16 c4) ∷
   rw 39 (q14 c4) ∷
   rw 40 (q26 c4) ∷
   rw 41 (q26 c4) ∷
   rw⁻ 42 (q25 c4) ∷
   rw⁻ 43 (q25 c4) ∷
   rw⁻ 44 (q25 c4) ∷
   rw 45 (q13 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q28 c4) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q28 c4) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q28 c4) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q28 c4) ∷
   rw 12 (q12 c4) ∷
   rw 13 (q28 c4) ∷
   rw 14 (q12 c4) ∷
   rw 15 (q28 c4) ∷
   rw 16 (q29 c4) ∷
   rw 17 (q29 c4) ∷
   rw 18 (q29 c4) ∷
   rw 19 (q8 c4) ∷
   rw 20 (q29 c4) ∷
   rw 21 (q27 c4) ∷
   rw 22 (q27 c4) ∷
   rw 23 (q27 c4) ∷
   rw 24 (q27 c4) ∷
   rw 25 (q27 c4) ∷
   rw 26 (q27 c4) ∷
   rw 27 (q27 c4) ∷
   rw 28 (q27 c4) ∷
   rw 29 (q27 c4) ∷
   rw 30 (q28 c4) ∷
   rw 31 (q12 c4) ∷
   rw 32 (q28 c4) ∷
   rw 33 (q12 c4) ∷
   rw 34 (q28 c4) ∷
   rw 35 (q29 c4) ∷
   rw 36 (q29 c4) ∷
   rw 37 (q29 c4) ∷
   rw 38 (q8 c4) ∷
   rw 39 (q28 c4) ∷
   rw 40 (q28 c4) ∷
   rw 41 (q27 c4) ∷
   rw 42 (q27 c4) ∷
   rw 43 (q27 c4) ∷
   rw 44 (q7 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q30 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 12 (q30 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw 14 (q30 c4) ∷
   rw 15 (q31 c4) ∷
   rw 16 (q31 c4) ∷
   rw 17 (q31 c4) ∷
   rw 18 (q2 c4) ∷
   rw 19 (q31 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw 29 (q30 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw 31 (q30 c4) ∷
   rw⁻ 32 (q6 c4) ∷
   rw 33 (q30 c4) ∷
   rw 34 (q31 c4) ∷
   rw 35 (q31 c4) ∷
   rw 36 (q31 c4) ∷
   rw 37 (q2 c4) ∷
   rw 38 (q30 c4) ∷
   rw 39 (q30 c4) ∷
   rw⁻ 40 (q19 c4) ∷
   rw⁻ 41 (q19 c4) ∷
   rw⁻ 42 (q19 c4) ∷
   rw 43 (q1 c4) ∷
   rw 2 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 81 (q34 c4) ∷
   rw 78 (q34 c4) ∷
   rw 75 (q35 c4) ∷
   rw 72 (q36 c4) ∷
   rw 69 (q36 c4) ∷
   rw 66 (q36 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q37 c4) ∷
   rw 57 (q34 c4) ∷
   rw 54 (q37 c4) ∷
   rw 51 (q34 c4) ∷
   rw 82 (q34 c4) ∷
   rw 79 (q34 c4) ∷
   rw 76 (q35 c4) ∷
   rw 73 (q36 c4) ∷
   rw 70 (q36 c4) ∷
   rw 67 (q36 c4) ∷
   rw 64 (q34 c4) ∷
   rw 61 (q37 c4) ∷
   rw 58 (q34 c4) ∷
   rw 55 (q37 c4) ∷
   rw 52 (q34 c4) ∷
   rw 83 (q34 c4) ∷
   rw 80 (q34 c4) ∷
   rw 77 (q35 c4) ∷
   rw 74 (q36 c4) ∷
   rw 71 (q36 c4) ∷
   rw 68 (q36 c4) ∷
   rw 65 (q34 c4) ∷
   rw 62 (q37 c4) ∷
   rw 59 (q34 c4) ∷
   rw 56 (q37 c4) ∷
   rw 53 (q34 c4) ∷
   rw 84 (q34 c4) ∷
   rw 81 (q34 c4) ∷
   rw 78 (q35 c4) ∷
   rw 75 (q36 c4) ∷
   rw 72 (q36 c4) ∷
   rw 69 (q36 c4) ∷
   rw 66 (q34 c4) ∷
   rw 63 (q37 c4) ∷
   rw 60 (q34 c4) ∷
   rw 57 (q37 c4) ∷
   rw 54 (q34 c4) ∷
   rw 85 (q34 c4) ∷
   rw 82 (q34 c4) ∷
   rw 79 (q35 c4) ∷
   rw 76 (q36 c4) ∷
   rw 73 (q36 c4) ∷
   rw 70 (q36 c4) ∷
   rw 67 (q34 c4) ∷
   rw 64 (q37 c4) ∷
   rw 61 (q34 c4) ∷
   rw 58 (q37 c4) ∷
   rw 55 (q34 c4) ∷
   rw 86 (q34 c4) ∷
   rw 83 (q34 c4) ∷
   rw 80 (q35 c4) ∷
   rw 77 (q36 c4) ∷
   rw 74 (q36 c4) ∷
   rw 71 (q36 c4) ∷
   rw 68 (q34 c4) ∷
   rw 65 (q37 c4) ∷
   rw 62 (q34 c4) ∷
   rw 59 (q37 c4) ∷
   rw 56 (q34 c4) ∷
   rw 87 (q34 c4) ∷
   rw 84 (q34 c4) ∷
   rw 81 (q35 c4) ∷
   rw 78 (q36 c4) ∷
   rw 75 (q36 c4) ∷
   rw 72 (q36 c4) ∷
   rw 69 (q34 c4) ∷
   rw 66 (q37 c4) ∷
   rw 63 (q34 c4) ∷
   rw 60 (q37 c4) ∷
   rw 57 (q34 c4) ∷
   rw 88 (q38 c4) ∷
   rw 85 (q38 c4) ∷
   rw 82 (q39 c4) ∷
   rw 79 (q40 c4) ∷
   rw 76 (q40 c4) ∷
   rw 73 (q40 c4) ∷
   rw 70 (q38 c4) ∷
   rw 67 (q41 c4) ∷
   rw 64 (q38 c4) ∷
   rw 61 (q41 c4) ∷
   rw 58 (q38 c4) ∷
   rw 89 (q34 c4) ∷
   rw 86 (q34 c4) ∷
   rw 83 (q35 c4) ∷
   rw 80 (q36 c4) ∷
   rw 77 (q36 c4) ∷
   rw 74 (q36 c4) ∷
   rw 71 (q34 c4) ∷
   rw 68 (q37 c4) ∷
   rw 65 (q34 c4) ∷
   rw 62 (q37 c4) ∷
   rw 59 (q34 c4) ∷
   rw 90 (q38 c4) ∷
   rw 87 (q38 c4) ∷
   rw 84 (q39 c4) ∷
   rw 81 (q40 c4) ∷
   rw 78 (q40 c4) ∷
   rw 75 (q40 c4) ∷
   rw 72 (q38 c4) ∷
   rw 69 (q41 c4) ∷
   rw 66 (q38 c4) ∷
   rw 63 (q41 c4) ∷
   rw 60 (q38 c4) ∷
   rw 91 (q34 c4) ∷
   rw 88 (q34 c4) ∷
   rw 85 (q35 c4) ∷
   rw 82 (q36 c4) ∷
   rw 79 (q36 c4) ∷
   rw 76 (q36 c4) ∷
   rw 73 (q34 c4) ∷
   rw 70 (q37 c4) ∷
   rw 67 (q34 c4) ∷
   rw 64 (q37 c4) ∷
   rw 61 (q34 c4) ∷
   rw 92 (q42 c4) ∷
   rw 89 (q42 c4) ∷
   rw 86 (q43 c4) ∷
   rw 83 (q44 c4) ∷
   rw 80 (q44 c4) ∷
   rw 77 (q44 c4) ∷
   rw 74 (q42 c4) ∷
   rw 71 (q45 c4) ∷
   rw 68 (q42 c4) ∷
   rw 65 (q45 c4) ∷
   rw 62 (q42 c4) ∷
   rw 93 (q42 c4) ∷
   rw 90 (q42 c4) ∷
   rw 87 (q43 c4) ∷
   rw 84 (q44 c4) ∷
   rw 81 (q44 c4) ∷
   rw 78 (q44 c4) ∷
   rw 75 (q42 c4) ∷ []) Eq.refl
