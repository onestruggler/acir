{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR007 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R007 (Sᴰ : SR007) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-CS04-sw0-L : WsL → St 1620
  lem-comm-push-CS04-sw0-L = pickᴰ 0 Sᴰ
  lem-comm-push-CS04-sw1-R : WsL → St 2005
  lem-comm-push-CS04-sw1-R = pickᴰ 1 Sᴰ
  lem-comm-push-CS04-sw2-R : WsL → St 2350
  lem-comm-push-CS04-sw2-R = pickᴰ 2 Sᴰ
  lem-comm-push-BOX⟨0·13⟩-sw0-R : WsL → St 2374
  lem-comm-push-BOX⟨0·13⟩-sw0-R = pickᴰ 3 Sᴰ
  lem-comm-push-BOX⟨0·21⟩-sw2-R : WsL → St 2375
  lem-comm-push-BOX⟨0·21⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-BOX⟨0·31⟩-sw2-L : WsL → St 2376
  lem-comm-push-BOX⟨0·31⟩-sw2-L = pickᴰ 5 Sᴰ
  lem-comm-push-BOX⟨0·41⟩-sw1-R : WsL → St 2377
  lem-comm-push-BOX⟨0·41⟩-sw1-R = pickᴰ 6 Sᴰ
  lem-comm-push-BOX⟨0·42⟩-sw1-L : WsL → St 2378
  lem-comm-push-BOX⟨0·42⟩-sw1-L = pickᴰ 7 Sᴰ
  lem-comm-push-BOX⟨1·03⟩-sw1-R : WsL → St 2379
  lem-comm-push-BOX⟨1·03⟩-sw1-R = pickᴰ 8 Sᴰ
  lem-comm-push-BOX⟨4·203⟩-sw1-L : WsL → St 2380
  lem-comm-push-BOX⟨4·203⟩-sw1-L = pickᴰ 9 Sᴰ
  lem-comm-push-CS04-sw0-R : WsL → St 2381
  lem-comm-push-CS04-sw0-R = pickᴰ 10 Sᴰ
  lem-comm-push-CS14-sw0-L : WsL → St 1622
  lem-comm-push-CS14-sw0-L = pickᴰ 11 Sᴰ
  lem-comm-push-CS14-sw0-R : WsL → St 2008
  lem-comm-push-CS14-sw0-R = pickᴰ 12 Sᴰ
  lem-comm-push-CSd14-sw0-L : WsL → St 2371
  lem-comm-push-CSd14-sw0-L = pickᴰ 13 Sᴰ
  lem-comm-push-CSd14-sw0-R : WsL → St 2382
  lem-comm-push-CSd14-sw0-R = pickᴰ 14 Sᴰ
  lem-comm-push-CX04-sw1-R : WsL → St 2383
  lem-comm-push-CX04-sw1-R = pickᴰ 15 Sᴰ
  lem-comm-push-CX04-sw2-R : WsL → St 2384
  lem-comm-push-CX04-sw2-R = pickᴰ 16 Sᴰ

private
  q1 : WsL → Eqn
  q1 c4 = wlE 3 c4
  q2 : WsL → Eqn
  q2 c4 = eqn (ℓ "丬乥") (ℓ "乥丬") (c₂ (CX₀₁) (Swap))
  q3 : WsL → Eqn
  q3 c4 = wlE 4 c4
  q4 : WsL → Eqn
  q4 c4 = eqn (ℓ "丬乼") (ℓ "乼丬") (c₂ (CX₀₁) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = sE 2008 (lem-comm-push-CS14-sw0-R c4)
  q6 : WsL → Eqn
  q6 c4 = wlE 115 c4
  q7 : WsL → Eqn
  q7 c4 = sE 2382 (lem-comm-push-CSd14-sw0-R c4)
  q8 : WsL → Eqn
  q8 c4 = sE 2381 (lem-comm-push-CS04-sw0-R c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (ℓ "乄乼") (ℓ "乼乄") (c₂ (CX₁₀) (Swap ↑))
  q10 : WsL → Eqn
  q10 c4 = eqn (ℓ "乄乥") (ℓ "乥乄") (c₂ (CX₁₀) (Swap))
  q11 : WsL → Eqn
  q11 c4 = wlE 108 c4

-- comm push CCZ014 sw0 R: 48 steps
lem-comm-push-CCZ014-sw0-R : WsL → ⟪ (ℓ "丫五") ⟫ʷ ≈ ⟪ (ℓ "五丫") ⟫ʷ
lem-comm-push-CCZ014-sw0-R c4 = derive (ℓ "丫五") (ℓ "五丫")
  (re 1 1 (ℓ "乼亐乼") ∷
   re 2 1 (ℓ "乥二乥") ∷
   re 3 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 (q3 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 2 1 (ℓ "乼丶乼") ∷
   rw 1 (q3 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (ℓ "乼丷乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (ℓ "乼乎乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 3 1 (ℓ "乥丯乥") ∷
   rw 2 (q1 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   re 5 1 (ℓ "乥丰乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   re 7 1 (ℓ "乥乇乥") ∷
   rw 6 (q1 c4) ∷
   rw 2 (q11 c4) ∷
   re 2 5 (ℓ "二") ∷
   re 1 3 (ℓ "亐") ∷
   re 0 3 (ℓ "五") ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (ℓ "丌乥") (ℓ "乥丌") (c₁ (K) (Swap ↑))
  q13 : WsL → Eqn
  q13 c4 = eqn (ℓ "一乥") (ℓ "乥一") (c₁ (iI) (Swap ↑))
  q14 : WsL → Eqn
  q14 c4 = eqn (ℓ "丌乼") (ℓ "乼丌") (c₁ (K) (Swap ↑ ↑))
  q15 : WsL → Eqn
  q15 c4 = eqn (ℓ "一乼") (ℓ "乼一") (c₁ (iI) (Swap ↑ ↑))
  q16 : WsL → Eqn
  q16 c4 = wlE 109 c4
  q17 : WsL → Eqn
  q17 c4 = wlE 25 c4
  q18 : WsL → Eqn
  q18 c4 = eqn (ℓ "丒乼") (ℓ "乼丒") (c₂ (K ↑) (Swap ↑))
  q19 : WsL → Eqn
  q19 c4 = eqn (ℓ "丒乥") (ℓ "乥丒") (c₂ (K ↑) (Swap))
  q20 : WsL → Eqn
  q20 c4 = wlE 116 c4

-- comm push TOFF014 sw0 R: 63 steps
lem-comm-push-TOFF014-sw0-R : WsL → ⟪ (ℓ "丫井") ⟫ʷ ≈ ⟪ (ℓ "亖丫") ⟫ʷ
lem-comm-push-TOFF014-sw0-R c4 = derive (ℓ "丫井") (ℓ "亖丫")
  (re 1 1 (ℓ "乼云乼") ∷
   re 2 1 (ℓ "乥亍乥") ∷
   re 3 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 3 1 (ℓ "乼丶乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   re 5 1 (ℓ "乼丷乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 7 1 (ℓ "乼乎乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   re 4 1 (ℓ "乥丯乥") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (ℓ "乥丰乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 2 (q20 c4) ∷
   re 2 8 (ℓ "于") ∷
   re 1 3 (ℓ "互") ∷
   re 0 3 (ℓ "亖") ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = wlE 103 c4
  q22 : WsL → Eqn
  q22 c4 = wlE 104 c4
  q23 : WsL → Eqn
  q23 c4 = sE 2374 (lem-comm-push-BOX⟨0·13⟩-sw0-R c4)

-- comm push BOX(1;023) sw0 R: 8 steps
lem-comm-push-BOX⟨1·023⟩-sw0-R : WsL → ⟪ (ℓ "丫仃") ⟫ʷ ≈ ⟪ (ℓ "亶丫") ⟫ʷ
lem-comm-push-BOX⟨1·023⟩-sw0-R c4 = derive (ℓ "丫仃") (ℓ "亶丫")
  (re 1 1 (ℓ "二于人于二人") ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (ℓ "亶") ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = wlE 101 c4
  q25 : WsL → Eqn
  q25 c4 = wlE 102 c4
  q26 : WsL → Eqn
  q26 c4 = sE 2379 (lem-comm-push-BOX⟨1·03⟩-sw1-R c4)

-- comm push BOX(0;123) sw1 R: 8 steps
lem-comm-push-BOX⟨0·123⟩-sw1-R : WsL → ⟪ (ℓ "乊亶") ⟫ʷ ≈ ⟪ (ℓ "仉乊") ⟫ʷ
lem-comm-push-BOX⟨0·123⟩-sw1-R c4 = derive (ℓ "乊亶") (ℓ "仉乊")
  (re 1 1 (ℓ "二亍亵亍二亵") ∷
   rw⁻ 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (ℓ "仉") ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "之乼") (ℓ "乼之") (c₃ (CX₀₁ ↑) (Swap))
  q28 : WsL → Eqn
  q28 c4 = sE 1622 (lem-comm-push-CS14-sw0-L c4)
  q29 : WsL → Eqn
  q29 c4 = wlE 117 c4
  q30 : WsL → Eqn
  q30 c4 = eqn (ℓ "丫乪") (ℓ "乪丫") (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (ℓ "丫乩") (ℓ "乩丫") (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q32 : WsL → Eqn
  q32 c4 = wlE 6 c4
  q33 : WsL → Eqn
  q33 c4 = wlE 13 c4
  q34 : WsL → Eqn
  q34 c4 = wlE 14 c4
  q35 : WsL → Eqn
  q35 c4 = sE 2005 (lem-comm-push-CS04-sw1-R c4)

-- comm push CCZ124 sw0 L: 46 steps
lem-comm-push-CCZ124-sw0-L : WsL → ⟪ (ℓ "亨丫") ⟫ʷ ≈ ⟪ (ℓ "丫亜") ⟫ʷ
lem-comm-push-CCZ124-sw0-L c4 = derive (ℓ "亨丫") (ℓ "丫亜")
  (re 0 1 (ℓ "乼交乼") ∷
   re 1 1 (ℓ "乢之乣之乎") ∷
   rw⁻ 2 (q3 c4) ∷
   re 0 3 (ℓ "乩") ∷
   rw⁻ 1 (q27 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乪") ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乕") ∷
   rw 5 (q3 c4) ∷
   rw 4 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q1 c4) ∷
   re 4 5 (ℓ "二") ∷
   re 3 3 (ℓ "亐") ∷
   re 2 3 (ℓ "五") ∷
   re 1 3 (ℓ "亜") ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = wlE 65 c4
  q37 : WsL → Eqn
  q37 c4 = eqn (ℓ "丂乼") (ℓ "乼丂") (c₂ (iI ↑) (Swap ↑))
  q38 : WsL → Eqn
  q38 c4 = wlE 118 c4
  q39 : WsL → Eqn
  q39 c4 = eqn (ℓ "丫两") (ℓ "两丫") (c₂ (Swap) (K ↑ ↑))
  q40 : WsL → Eqn
  q40 c4 = eqn (ℓ "乊两") (ℓ "两乊") (c₃ (Swap ↑) (K ↑))
  q41 : WsL → Eqn
  q41 c4 = wlE 119 c4
  q42 : WsL → Eqn
  q42 c4 = wlE 66 c4
  q43 : WsL → Eqn
  q43 c4 = wlE 67 c4
  q44 : WsL → Eqn
  q44 c4 = eqn (ℓ "丂乥") (ℓ "乥丂") (c₂ (iI ↑) (Swap))
  q45 : WsL → Eqn
  q45 c4 = wlE 120 c4

-- comm push TOFF412 sw0 L: 62 steps
lem-comm-push-TOFF412-sw0-L : WsL → ⟪ (ℓ "享丫") ⟫ʷ ≈ ⟪ (ℓ "丫亟") ⟫ʷ
lem-comm-push-TOFF412-sw0-L c4 = derive (ℓ "享丫") (ℓ "丫亟")
  (re 0 1 (ℓ "乼产乼") ∷
   re 1 1 (ℓ "丞乢之乣之乎丞丂") ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乕") ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw 2 (q29 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q32 c4) ∷
   rw 7 (q35 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   rw⁻ 11 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   re 4 8 (ℓ "亏") ∷
   re 3 3 (ℓ "亓") ∷
   re 2 3 (ℓ "亗") ∷
   re 1 3 (ℓ "亟") ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = sE 2380 (lem-comm-push-BOX⟨4·203⟩-sw1-L c4)
  q47 : WsL → Eqn
  q47 c4 = wlE 122 c4
  q48 : WsL → Eqn
  q48 c4 = wlE 123 c4

-- comm push BOX(2;4103) sw1 L: 8 steps
lem-comm-push-BOX⟨2·4103⟩-sw1-L : WsL → ⟪ (ℓ "佝乊") ⟫ʷ ≈ ⟪ (ℓ "乊伪") ⟫ʷ
lem-comm-push-BOX⟨2·4103⟩-sw1-L c4 = derive (ℓ "佝乊") (ℓ "乊伪")
  (re 0 1 (ℓ "亨亪作亪亨作") ∷
   rw 5 (q46 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q46 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 0 (q47 c4) ∷
   re 1 6 (ℓ "伪") ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = wlE 64 c4
  q50 : WsL → Eqn
  q50 c4 = sE 1620 (lem-comm-push-CS04-sw0-L c4)
  q51 : WsL → Eqn
  q51 c4 = wlE 107 c4
  q52 : WsL → Eqn
  q52 c4 = sE 2371 (lem-comm-push-CSd14-sw0-L c4)
  q53 : WsL → Eqn
  q53 c4 = wlE 124 c4

-- comm push TOFF401 sw0 L: 63 steps
lem-comm-push-TOFF401-sw0-L : WsL → ⟪ (ℓ "亗丫") ⟫ʷ ≈ ⟪ (ℓ "丫亗") ⟫ʷ
lem-comm-push-TOFF401-sw0-L c4 = derive (ℓ "亗丫") (ℓ "丫亗")
  (re 0 1 (ℓ "乼亓乼") ∷
   re 1 1 (ℓ "乥亏乥") ∷
   re 2 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 1 (q49 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q49 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw 3 (q52 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (ℓ "乼丶乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (ℓ "乼丷乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 8 1 (ℓ "乼乎乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (ℓ "乥丯乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   re 7 1 (ℓ "乥丰乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   re 9 1 (ℓ "乥乇乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 3 (q53 c4) ∷
   re 3 8 (ℓ "亏") ∷
   re 2 3 (ℓ "亓") ∷
   re 1 3 (ℓ "亗") ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (ℓ "丌乊") (ℓ "乊丌") (c₁ (K) (Swap))
  q55 : WsL → Eqn
  q55 c4 = wlE 125 c4

-- comm push TOFF124 sw0 L: 62 steps
lem-comm-push-TOFF124-sw0-L : WsL → ⟪ (ℓ "亩丫") ⟫ʷ ≈ ⟪ (ℓ "丫亝") ⟫ʷ
lem-comm-push-TOFF124-sw0-L c4 = derive (ℓ "亩丫") (ℓ "丫亝")
  (re 0 1 (ℓ "乼亥乼") ∷
   re 1 1 (ℓ "丒乢之乣之乎丒丂") ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乕") ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 6 (q16 c4) ∷
   rw 5 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw 2 (q29 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q32 c4) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q44 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   re 4 8 (ℓ "亍") ∷
   re 3 3 (ℓ "云") ∷
   re 2 3 (ℓ "井") ∷
   re 1 3 (ℓ "亝") ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = sE 2378 (lem-comm-push-BOX⟨0·42⟩-sw1-L c4)

-- comm push BOX(4;012) sw1 L: 12 steps
lem-comm-push-BOX⟨4·012⟩-sw1-L : WsL → ⟪ (ℓ "伊乊") ⟫ʷ ≈ ⟪ (ℓ "乊伌") ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw1-L c4 = derive (ℓ "伊乊") (ℓ "乊伌")
  (re 0 1 (ℓ "五亗仿亗五仿") ∷
   rw 5 (q56 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 3 (ℓ "亜") ∷
   rw⁻ 3 (q32 c4) ∷
   re 4 3 (ℓ "亟") ∷
   rw 2 (q56 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   re 2 3 (ℓ "亟") ∷
   rw⁻ 0 (q32 c4) ∷
   re 1 3 (ℓ "亜") ∷
   re 1 6 (ℓ "伌") ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = wlE 5 c4
  q58 : WsL → Eqn
  q58 c4 = wlE 7 c4
  q59 : WsL → Eqn
  q59 c4 = wlE 8 c4
  q60 : WsL → Eqn
  q60 c4 = wlE 9 c4
  q61 : WsL → Eqn
  q61 c4 = sE 2350 (lem-comm-push-CS04-sw2-R c4)
  q62 : WsL → Eqn
  q62 c4 = wlE 128 c4
  q63 : WsL → Eqn
  q63 c4 = wlE 129 c4
  q64 : WsL → Eqn
  q64 c4 = wlE 11 c4
  q65 : WsL → Eqn
  q65 c4 = sE 2384 (lem-comm-push-CX04-sw2-R c4)
  q66 : WsL → Eqn
  q66 c4 = wlE 12 c4
  q67 : WsL → Eqn
  q67 c4 = sE 2383 (lem-comm-push-CX04-sw1-R c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (ℓ "丨乼") (ℓ "乼丨") (c₂ (CS) (Swap ↑))
  q69 : WsL → Eqn
  q69 c4 = eqn (ℓ "丨乥") (ℓ "乥丨") (c₂ (CS) (Swap))
  q70 : WsL → Eqn
  q70 c4 = wlE 130 c4

-- comm push CCZ034 sw3 L: 87 steps
lem-comm-push-CCZ034-sw3-L : WsL → ⟪ (ℓ "亠乼") ⟫ʷ ≈ ⟪ (ℓ "乼亠") ⟫ʷ
lem-comm-push-CCZ034-sw3-L c4 = derive (ℓ "亠乼") (ℓ "乼亠")
  (re 0 1 (ℓ "乥亜乥") ∷
   re 1 1 (ℓ "乊五乊") ∷
   re 2 1 (ℓ "乼亐乼") ∷
   re 3 1 (ℓ "乥二乥") ∷
   re 4 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 1 (q57 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q35 c4) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "为") ∷
   rw⁻ 2 (q60 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "为") ∷
   rw 4 (q61 c4) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乼丶乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 4 3 (ℓ "乁") ∷
   rw 2 (q62 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "乁") ∷
   rw 0 (q63 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 7 1 (ℓ "乥丯乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 6 (q67 c4) ∷
   re 8 1 (ℓ "乊丨乊") ∷
   rw 7 (q32 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   re 6 1 (ℓ "乼为乼") ∷
   rw 5 (q3 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   re 8 1 (ℓ "乼为乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   re 7 1 (ℓ "乥丳乥") ∷
   rw 6 (q1 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   re 9 1 (ℓ "乥丳乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   re 5 5 (ℓ "二") ∷
   re 4 3 (ℓ "亐") ∷
   re 3 3 (ℓ "五") ∷
   re 2 3 (ℓ "亜") ∷
   re 1 3 (ℓ "亠") ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (ℓ "一乊") (ℓ "乊一") (c₁ (iI) (Swap))
  q72 : WsL → Eqn
  q72 c4 = wlE 131 c4

-- comm push TOFF034 sw3 L: 114 steps
lem-comm-push-TOFF034-sw3-L : WsL → ⟪ (ℓ "亡乼") ⟫ʷ ≈ ⟪ (ℓ "乼亡") ⟫ʷ
lem-comm-push-TOFF034-sw3-L c4 = derive (ℓ "亡乼") (ℓ "乼亡")
  (re 0 1 (ℓ "乥亝乥") ∷
   re 1 1 (ℓ "乊井乊") ∷
   re 2 1 (ℓ "乼云乼") ∷
   re 3 1 (ℓ "乥亍乥") ∷
   re 4 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q35 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q61 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q14 c4) ∷
   re 5 1 (ℓ "乼丶乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 5 3 (ℓ "乁") ∷
   rw 3 (q62 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "乁") ∷
   rw 1 (q63 c4) ∷
   rw 0 (q14 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 6 (q65 c4) ∷
   re 8 1 (ℓ "乥丯乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 7 (q67 c4) ∷
   re 9 1 (ℓ "乊丨乊") ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (ℓ "乼乎乼") ∷
   rw 5 (q3 c4) ∷
   re 7 1 (ℓ "乼为乼") ∷
   rw 6 (q3 c4) ∷
   re 8 1 (ℓ "乼乏乼") ∷
   rw 7 (q3 c4) ∷
   re 9 1 (ℓ "乼为乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (ℓ "乥乇乥") ∷
   rw 6 (q1 c4) ∷
   re 8 1 (ℓ "乥丳乥") ∷
   rw 7 (q1 c4) ∷
   re 9 1 (ℓ "乥么乥") ∷
   rw 8 (q1 c4) ∷
   re 10 1 (ℓ "乥丳乥") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   re 5 8 (ℓ "亍") ∷
   re 4 3 (ℓ "云") ∷
   re 3 3 (ℓ "井") ∷
   re 2 3 (ℓ "亝") ∷
   re 1 3 (ℓ "亡") ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = sE 2376 (lem-comm-push-BOX⟨0·31⟩-sw2-L c4)
  q74 : WsL → Eqn
  q74 c4 = wlE 132 c4
  q75 : WsL → Eqn
  q75 c4 = wlE 133 c4

-- comm push BOX(3;021) sw2 L: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw2-L : WsL → ⟪ (ℓ "仵乥") ⟫ʷ ≈ ⟪ (ℓ "乥仝") ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw2-L c4 = derive (ℓ "仵乥") (ℓ "乥仝")
  (re 0 1 (ℓ "亘些仟些亘仟") ∷
   rw 5 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 0 (q74 c4) ∷
   re 1 6 (ℓ "仝") ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = sE 2375 (lem-comm-push-BOX⟨0·21⟩-sw2-R c4)

-- comm push BOX(2;031) sw2 R: 8 steps
lem-comm-push-BOX⟨2·031⟩-sw2-R : WsL → ⟪ (ℓ "乥仝") ⟫ʷ ≈ ⟪ (ℓ "仵乥") ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw2-R c4 = derive (ℓ "乥仝") (ℓ "仵乥")
  (re 1 1 (ℓ "亘亚仇亚亘仇") ∷
   rw⁻ 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 5 (q76 c4) ∷
   re 0 6 (ℓ "仵") ∷ []) Eq.refl

-- comm push CCZ034 sw3 R: 87 steps
lem-comm-push-CCZ034-sw3-R : WsL → ⟪ (ℓ "乼亠") ⟫ʷ ≈ ⟪ (ℓ "亠乼") ⟫ʷ
lem-comm-push-CCZ034-sw3-R c4 = derive (ℓ "乼亠") (ℓ "亠乼")
  (re 1 1 (ℓ "乥亜乥") ∷
   re 2 1 (ℓ "乊五乊") ∷
   re 3 1 (ℓ "乼亐乼") ∷
   re 4 1 (ℓ "乥二乥") ∷
   re 5 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q35 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q61 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乁") ∷
   rw⁻ 2 (q62 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乁") ∷
   re 5 1 (ℓ "乼丶乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 4 (q65 c4) ∷
   re 6 1 (ℓ "乥丯乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q67 c4) ∷
   re 7 1 (ℓ "乊丨乊") ∷
   rw 6 (q32 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q3 c4) ∷
   re 5 1 (ℓ "乼为乼") ∷
   rw 4 (q3 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q3 c4) ∷
   re 7 1 (ℓ "乼为乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q1 c4) ∷
   re 6 1 (ℓ "乥丳乥") ∷
   rw 5 (q1 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q1 c4) ∷
   re 8 1 (ℓ "乥丳乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 4 5 (ℓ "二") ∷
   re 3 3 (ℓ "亐") ∷
   re 2 3 (ℓ "五") ∷
   re 1 3 (ℓ "亜") ∷
   re 0 3 (ℓ "亠") ∷ []) Eq.refl

-- comm push TOFF034 sw3 R: 114 steps
lem-comm-push-TOFF034-sw3-R : WsL → ⟪ (ℓ "乼亡") ⟫ʷ ≈ ⟪ (ℓ "亡乼") ⟫ʷ
lem-comm-push-TOFF034-sw3-R c4 = derive (ℓ "乼亡") (ℓ "亡乼")
  (re 1 1 (ℓ "乥亝乥") ∷
   re 2 1 (ℓ "乊井乊") ∷
   re 3 1 (ℓ "乼云乼") ∷
   re 4 1 (ℓ "乥亍乥") ∷
   re 5 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乎") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "乏") ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 9 3 (ℓ "丶") ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乕") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乖") ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   re 6 3 (ℓ "丳") ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "为") ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "为") ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乁") ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乁") ∷
   re 6 1 (ℓ "乼丶乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 7 1 (ℓ "乥丯乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 6 (q67 c4) ∷
   re 8 1 (ℓ "乊丨乊") ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   re 6 1 (ℓ "乼为乼") ∷
   rw 5 (q3 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   re 8 1 (ℓ "乼为乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   re 7 1 (ℓ "乥丳乥") ∷
   rw 6 (q1 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   re 9 1 (ℓ "乥丳乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 4 8 (ℓ "亍") ∷
   re 3 3 (ℓ "云") ∷
   re 2 3 (ℓ "井") ∷
   re 1 3 (ℓ "亝") ∷
   re 0 3 (ℓ "亡") ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = wlE 47 c4
  q78 : WsL → Eqn
  q78 c4 = wlE 29 c4
  q79 : WsL → Eqn
  q79 c4 = wlE 1 c4
  q80 : WsL → Eqn
  q80 c4 = eqn (ℓ "丳乼") (ℓ "乼丳") (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))

-- comm push CCZ023 sw3 R: 58 steps
lem-comm-push-CCZ023-sw3-R : WsL → ⟪ (ℓ "乼亘") ⟫ʷ ≈ ⟪ (ℓ "亜乼") ⟫ʷ
lem-comm-push-CCZ023-sw3-R c4 = derive (ℓ "乼亘") (ℓ "亜乼")
  (re 1 1 (ℓ "乊亐乊") ∷
   re 2 1 (ℓ "乥二乥") ∷
   re 3 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q78 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q79 c4) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 0 3 (ℓ "乩") ∷
   rw⁻ 1 (q80 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乪") ∷
   rw⁻ 3 (q80 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 0 (q32 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   re 3 1 (ℓ "乊丬乊") ∷
   rw 2 (q32 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q32 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 3 1 (ℓ "乼乎乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 5 1 (ℓ "乼乏乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "乼丶乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (ℓ "乥乇乥") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 6 1 (ℓ "乥么乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (ℓ "乥丯乥") ∷
   rw 7 (q1 c4) ∷
   re 3 5 (ℓ "二") ∷
   re 2 3 (ℓ "亐") ∷
   re 1 3 (ℓ "五") ∷
   re 0 3 (ℓ "亜") ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (ℓ "乊丞") (ℓ "丞乊") (c₃ (Swap ↑) (K))

-- comm push TOFF302 sw3 R: 76 steps
lem-comm-push-TOFF302-sw3-R : WsL → ⟪ (ℓ "乼些") ⟫ʷ ≈ ⟪ (ℓ "亟乼") ⟫ʷ
lem-comm-push-TOFF302-sw3-R c4 = derive (ℓ "乼些") (ℓ "亟乼")
  (re 1 1 (ℓ "乊亓乊") ∷
   re 2 1 (ℓ "乥亏乥") ∷
   re 3 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 2 (q49 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q49 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q1 c4) ∷
   rw 1 (q81 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw⁻ 6 (q79 c4) ∷
   rw 7 (q81 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw⁻ 4 (q80 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 0 (q32 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q40 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   re 3 8 (ℓ "亏") ∷
   re 2 3 (ℓ "亓") ∷
   re 1 3 (ℓ "亗") ∷
   re 0 3 (ℓ "亟") ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (ℓ "乊乹") (ℓ "乹乊") (c₃ (Swap ↑) (CS))
  q83 : WsL → Eqn
  q83 c4 = wlE 10 c4
  q84 : WsL → Eqn
  q84 c4 = eqn (ℓ "乊乺") (ℓ "乺乊") (c₃ (Swap ↑) (CS • CS • CS))

-- comm push CCZ034 sw1 R: 83 steps
lem-comm-push-CCZ034-sw1-R : WsL → ⟪ (ℓ "乊亠") ⟫ʷ ≈ ⟪ (ℓ "亠乊") ⟫ʷ
lem-comm-push-CCZ034-sw1-R c4 = derive (ℓ "乊亠") (ℓ "亠乊")
  (re 1 1 (ℓ "乥亜乥") ∷
   re 2 1 (ℓ "乊五乊") ∷
   re 3 1 (ℓ "乼亐乼") ∷
   re 4 1 (ℓ "乥二乥") ∷
   re 5 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q35 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q61 c4) ∷
   rw 6 (q1 c4) ∷
   rw 0 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   re 3 1 (ℓ "乥丳乥") ∷
   rw 2 (q1 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   re 5 1 (ℓ "乥丳乥") ∷
   rw 4 (q1 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q1 c4) ∷
   re 4 5 (ℓ "二") ∷
   re 3 3 (ℓ "亐") ∷
   re 2 3 (ℓ "五") ∷
   re 1 3 (ℓ "亜") ∷
   re 0 3 (ℓ "亠") ∷ []) Eq.refl

-- comm push TOFF034 sw1 R: 110 steps
lem-comm-push-TOFF034-sw1-R : WsL → ⟪ (ℓ "乊亡") ⟫ʷ ≈ ⟪ (ℓ "亡乊") ⟫ʷ
lem-comm-push-TOFF034-sw1-R c4 = derive (ℓ "乊亡") (ℓ "亡乊")
  (re 1 1 (ℓ "乥亝乥") ∷
   re 2 1 (ℓ "乊井乊") ∷
   re 3 1 (ℓ "乼云乼") ∷
   re 4 1 (ℓ "乥亍乥") ∷
   re 5 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乎") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "乏") ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 9 3 (ℓ "丶") ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乕") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乖") ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   re 6 3 (ℓ "丳") ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "为") ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "为") ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw 1 (q82 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   re 4 1 (ℓ "乥丳乥") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   re 6 1 (ℓ "乥丳乥") ∷
   rw 5 (q1 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q32 c4) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   re 4 8 (ℓ "亍") ∷
   re 3 3 (ℓ "云") ∷
   re 2 3 (ℓ "井") ∷
   re 1 3 (ℓ "亝") ∷
   re 0 3 (ℓ "亡") ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = sE 2377 (lem-comm-push-BOX⟨0·41⟩-sw1-R c4)

-- comm push BOX(4;021) sw1 R: 12 steps
lem-comm-push-BOX⟨4·021⟩-sw1-R : WsL → ⟪ (ℓ "乊伌") ⟫ʷ ≈ ⟪ (ℓ "伊乊") ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw1-R c4 = derive (ℓ "乊伌") (ℓ "伊乊")
  (re 1 1 (ℓ "亜亟价亟亜价") ∷
   re 1 1 (ℓ "乊五乊") ∷
   rw 0 (q32 c4) ∷
   re 2 1 (ℓ "乊亗乊") ∷
   rw 1 (q32 c4) ∷
   rw 2 (q85 c4) ∷
   re 4 1 (ℓ "乊亗乊") ∷
   rw 3 (q32 c4) ∷
   re 5 1 (ℓ "乊五乊") ∷
   rw 4 (q32 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (ℓ "伊") ∷ []) Eq.refl
