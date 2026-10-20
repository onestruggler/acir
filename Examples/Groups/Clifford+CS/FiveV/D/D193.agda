{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D193 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.TR2 using (lem-TR2-6ab04641)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-F4-I-I-at02132031 ; lem-F4-I-K3-at02132031 ; lem-F4-I-S2-at02132031 ; lem-F4-K3-I-at02132031 ; lem-F4-K3-K3-at02132031 ; lem-F4-K3-S2-at02132031 ; lem-F4-S2-I-at02132031 ; lem-F4-S2-K3-at02132031 ; lem-F4-S2-S2-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-CS2-S3-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-S2-CS2-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.FiveV.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D032 using (lem-S2-SBOX⟨0·2·43·1⟩-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.FiveV.D.D047 using (lem-F4-CS2-K3-at02132031 ; lem-F4-K3-CS2-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.FiveV.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.FiveV.D.D147 using (lem-deb-P-lo-eps-at02132031)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.FiveV.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ Sw12 ∷ []) (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl 87 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb1-0-42-3 ∷ Sw01 ∷ []) (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))
  q7 : Ws → Eqn
  q7 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Sb0-1-42-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl 90 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Sb0-1-43-2 ∷ Sw12 ∷ []) (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw12 ∷ CK43 ∷ []) (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (lem-TR2-6ab04641 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw12 ∷ S4 ∷ []) (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ S4 ∷ []) (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw01 ∷ S4 ∷ []) (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) [] (lem-deb-P-lo-eps-at02132031 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-CS2-at02132031 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-CS2-at02132031 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at02132031 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at02132031 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-K3-at02132031 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-K3-at02132031 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S2-at02132031 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-S2-at02132031 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I-at02132031 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-I-at02132031 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-I-at02132031 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S3-at02132031 c4)

-- deb-P-lo @02132031 part0: 368 steps
lem-deb-P-lo-at02132031-part0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-lo-at02132031-part0 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CCZ014 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw⁻ 3 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q13 c4) ∷
   rw 9 (q13 c4) ∷
   rw 10 (q13 c4) ∷
   rw 11 (q13 c4) ∷
   rw 12 (q13 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q13 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q13 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw 20 (q15 c4) ∷
   rw⁻ 21 (q14 c4) ∷
   rw 22 (q16 c4) ∷
   rw 23 (q16 c4) ∷
   rw 24 (q16 c4) ∷
   rw 25 (q16 c4) ∷
   rw 26 (q16 c4) ∷
   rw 27 (q16 c4) ∷
   rw 28 (q16 c4) ∷
   rw 29 (q16 c4) ∷
   rw 30 (q16 c4) ∷
   rw 31 (q13 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q13 c4) ∷
   rw 34 (q11 c4) ∷
   rw 35 (q13 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw⁻ 37 (q14 c4) ∷
   rw⁻ 38 (q14 c4) ∷
   rw 39 (q15 c4) ∷
   rw 40 (q13 c4) ∷
   rw 41 (q13 c4) ∷
   rw 42 (q16 c4) ∷
   rw 43 (q16 c4) ∷
   rw 44 (q16 c4) ∷
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
   rw 1 (q6 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q21 c4) ∷
   rw 7 (q21 c4) ∷
   rw 8 (q21 c4) ∷
   rw 9 (q21 c4) ∷
   rw 10 (q21 c4) ∷
   rw 11 (q6 c4) ∷
   rw 12 (q21 c4) ∷
   rw 13 (q6 c4) ∷
   rw 14 (q21 c4) ∷
   rw 15 (q22 c4) ∷
   rw 16 (q22 c4) ∷
   rw 17 (q22 c4) ∷
   rw 18 (q23 c4) ∷
   rw 19 (q22 c4) ∷
   rw 20 (q24 c4) ∷
   rw 21 (q24 c4) ∷
   rw 22 (q24 c4) ∷
   rw 23 (q24 c4) ∷
   rw 24 (q24 c4) ∷
   rw 25 (q24 c4) ∷
   rw 26 (q24 c4) ∷
   rw 27 (q24 c4) ∷
   rw 28 (q24 c4) ∷
   rw 29 (q21 c4) ∷
   rw 30 (q6 c4) ∷
   rw 31 (q21 c4) ∷
   rw 32 (q6 c4) ∷
   rw 33 (q21 c4) ∷
   rw 34 (q22 c4) ∷
   rw 35 (q22 c4) ∷
   rw 36 (q22 c4) ∷
   rw 37 (q23 c4) ∷
   rw 38 (q21 c4) ∷
   rw 39 (q21 c4) ∷
   rw 40 (q24 c4) ∷
   rw 41 (q24 c4) ∷
   rw 42 (q24 c4) ∷
   rw 43 (q4 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q25 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q25 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q25 c4) ∷
   rw 9 (q25 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 11 (q25 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw 13 (q25 c4) ∷
   rw 14 (q26 c4) ∷
   rw 15 (q26 c4) ∷
   rw 16 (q26 c4) ∷
   rw 17 (q15 c4) ∷
   rw 18 (q26 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   rw⁻ 21 (q14 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw⁻ 23 (q14 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 26 (q14 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw 28 (q25 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 30 (q25 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw 32 (q25 c4) ∷
   rw 33 (q26 c4) ∷
   rw 34 (q26 c4) ∷
   rw 35 (q26 c4) ∷
   rw 36 (q15 c4) ∷
   rw 37 (q25 c4) ∷
   rw 38 (q25 c4) ∷
   rw⁻ 39 (q14 c4) ∷
   rw⁻ 40 (q14 c4) ∷
   rw⁻ 41 (q14 c4) ∷
   rw 42 (q1 c4) ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 80 (q29 c4) ∷
   rw 77 (q29 c4) ∷
   rw 74 (q30 c4) ∷
   rw 71 (q31 c4) ∷
   rw 68 (q31 c4) ∷
   rw 65 (q31 c4) ∷
   rw 62 (q29 c4) ∷
   rw 59 (q32 c4) ∷
   rw 56 (q29 c4) ∷
   rw 53 (q32 c4) ∷
   rw 50 (q29 c4) ∷
   rw 81 (q29 c4) ∷
   rw 78 (q29 c4) ∷
   rw 75 (q30 c4) ∷
   rw 72 (q31 c4) ∷
   rw 69 (q31 c4) ∷
   rw 66 (q31 c4) ∷
   rw 63 (q29 c4) ∷
   rw 60 (q32 c4) ∷
   rw 57 (q29 c4) ∷
   rw 54 (q32 c4) ∷
   rw 51 (q29 c4) ∷
   rw 82 (q29 c4) ∷
   rw 79 (q29 c4) ∷
   rw 76 (q30 c4) ∷
   rw 73 (q31 c4) ∷
   rw 70 (q31 c4) ∷
   rw 67 (q31 c4) ∷
   rw 64 (q29 c4) ∷
   rw 61 (q32 c4) ∷
   rw 58 (q29 c4) ∷
   rw 55 (q32 c4) ∷
   rw 52 (q29 c4) ∷
   rw 83 (q29 c4) ∷
   rw 80 (q29 c4) ∷
   rw 77 (q30 c4) ∷
   rw 74 (q31 c4) ∷
   rw 71 (q31 c4) ∷
   rw 68 (q31 c4) ∷
   rw 65 (q29 c4) ∷
   rw 62 (q32 c4) ∷
   rw 59 (q29 c4) ∷
   rw 56 (q32 c4) ∷
   rw 53 (q29 c4) ∷
   rw 84 (q29 c4) ∷
   rw 81 (q29 c4) ∷
   rw 78 (q30 c4) ∷
   rw 75 (q31 c4) ∷
   rw 72 (q31 c4) ∷
   rw 69 (q31 c4) ∷
   rw 66 (q29 c4) ∷
   rw 63 (q32 c4) ∷
   rw 60 (q29 c4) ∷
   rw 57 (q32 c4) ∷
   rw 54 (q29 c4) ∷
   rw 85 (q29 c4) ∷
   rw 82 (q29 c4) ∷
   rw 79 (q30 c4) ∷
   rw 76 (q31 c4) ∷
   rw 73 (q31 c4) ∷
   rw 70 (q31 c4) ∷
   rw 67 (q29 c4) ∷
   rw 64 (q32 c4) ∷
   rw 61 (q29 c4) ∷
   rw 58 (q32 c4) ∷
   rw 55 (q29 c4) ∷
   rw 86 (q29 c4) ∷
   rw 83 (q29 c4) ∷
   rw 80 (q30 c4) ∷
   rw 77 (q31 c4) ∷
   rw 74 (q31 c4) ∷
   rw 71 (q31 c4) ∷
   rw 68 (q29 c4) ∷
   rw 65 (q32 c4) ∷
   rw 62 (q29 c4) ∷
   rw 59 (q32 c4) ∷
   rw 56 (q29 c4) ∷
   rw 87 (q33 c4) ∷
   rw 84 (q33 c4) ∷
   rw 81 (q34 c4) ∷
   rw 78 (q35 c4) ∷
   rw 75 (q35 c4) ∷
   rw 72 (q35 c4) ∷
   rw 69 (q33 c4) ∷
   rw 66 (q36 c4) ∷
   rw 63 (q33 c4) ∷
   rw 60 (q36 c4) ∷
   rw 57 (q33 c4) ∷
   rw 88 (q29 c4) ∷
   rw 85 (q29 c4) ∷
   rw 82 (q30 c4) ∷
   rw 79 (q31 c4) ∷
   rw 76 (q31 c4) ∷
   rw 73 (q31 c4) ∷
   rw 70 (q29 c4) ∷
   rw 67 (q32 c4) ∷
   rw 64 (q29 c4) ∷
   rw 61 (q32 c4) ∷
   rw 58 (q29 c4) ∷
   rw 89 (q33 c4) ∷
   rw 86 (q33 c4) ∷
   rw 83 (q34 c4) ∷
   rw 80 (q35 c4) ∷
   rw 77 (q35 c4) ∷
   rw 74 (q35 c4) ∷
   rw 71 (q33 c4) ∷
   rw 68 (q36 c4) ∷
   rw 65 (q33 c4) ∷
   rw 62 (q36 c4) ∷
   rw 59 (q33 c4) ∷
   rw 90 (q29 c4) ∷
   rw 87 (q29 c4) ∷
   rw 84 (q30 c4) ∷
   rw 81 (q31 c4) ∷
   rw 78 (q31 c4) ∷
   rw 75 (q31 c4) ∷
   rw 72 (q29 c4) ∷
   rw 69 (q32 c4) ∷
   rw 66 (q29 c4) ∷
   rw 63 (q32 c4) ∷
   rw 60 (q29 c4) ∷
   rw 91 (q37 c4) ∷
   rw 88 (q37 c4) ∷
   rw 85 (q38 c4) ∷
   rw 82 (q39 c4) ∷
   rw 79 (q39 c4) ∷
   rw 76 (q39 c4) ∷
   rw 73 (q37 c4) ∷
   rw 70 (q40 c4) ∷
   rw 67 (q37 c4) ∷
   rw 64 (q40 c4) ∷
   rw 61 (q37 c4) ∷
   rw 92 (q37 c4) ∷
   rw 89 (q37 c4) ∷
   rw 86 (q38 c4) ∷
   rw 83 (q39 c4) ∷
   rw 80 (q39 c4) ∷
   rw 77 (q39 c4) ∷
   rw 74 (q37 c4) ∷
   rw 71 (q40 c4) ∷
   rw 68 (q37 c4) ∷
   rw 65 (q40 c4) ∷
   rw 62 (q37 c4) ∷
   rw 93 (q37 c4) ∷
   rw 90 (q37 c4) ∷
   rw 87 (q38 c4) ∷
   rw 84 (q39 c4) ∷
   rw 81 (q39 c4) ∷
   rw 78 (q39 c4) ∷
   rw 75 (q37 c4) ∷
   rw 72 (q40 c4) ∷
   rw 69 (q37 c4) ∷
   rw 66 (q40 c4) ∷
   rw 63 (q37 c4) ∷
   rw 94 (q41 c4) ∷
   rw 91 (q41 c4) ∷
   rw 88 (q42 c4) ∷
   rw 85 (q43 c4) ∷
   rw 82 (q43 c4) ∷
   rw 79 (q43 c4) ∷
   rw 76 (q41 c4) ∷
   rw 73 (q44 c4) ∷
   rw 70 (q41 c4) ∷
   rw 67 (q44 c4) ∷
   rw 64 (q41 c4) ∷
   rw 95 (q37 c4) ∷
   rw 92 (q37 c4) ∷
   rw 89 (q38 c4) ∷
   rw 86 (q39 c4) ∷
   rw 83 (q39 c4) ∷
   rw 80 (q39 c4) ∷
   rw 77 (q37 c4) ∷
   rw 74 (q40 c4) ∷
   rw 71 (q37 c4) ∷
   rw 68 (q40 c4) ∷
   rw 65 (q37 c4) ∷
   rw 96 (q45 c4) ∷ []) Eq.refl
