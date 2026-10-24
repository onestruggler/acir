{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR006 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R006 (Sᴰ : SR006) where

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
  lem-comm-push-CK40-sw0-L : WsL → St 1877
  lem-comm-push-CK40-sw0-L = pickᴰ 0 Sᴰ
  lem-comm-push-CKd40-sw0-L : WsL → St 2357
  lem-comm-push-CKd40-sw0-L = pickᴰ 1 Sᴰ
  lem-comm-push-CS04-sw0-L : WsL → St 1620
  lem-comm-push-CS04-sw0-L = pickᴰ 2 Sᴰ
  lem-comm-push-CS04-sw1-L : WsL → St 1621
  lem-comm-push-CS04-sw1-L = pickᴰ 3 Sᴰ
  lem-comm-push-CS04-sw1-R : WsL → St 2005
  lem-comm-push-CS04-sw1-R = pickᴰ 4 Sᴰ
  lem-comm-push-CS04-sw2-L : WsL → St 2349
  lem-comm-push-CS04-sw2-L = pickᴰ 5 Sᴰ
  lem-comm-push-CS04-sw2-R : WsL → St 2350
  lem-comm-push-CS04-sw2-R = pickᴰ 6 Sᴰ
  lem-comm-push-CX04-sw0-L : WsL → St 2354
  lem-comm-push-CX04-sw0-L = pickᴰ 7 Sᴰ
  lem-comm-push-CX04-sw1-L : WsL → St 2355
  lem-comm-push-CX04-sw1-L = pickᴰ 8 Sᴰ
  lem-comm-push-CX40-sw0-L : WsL → St 2358
  lem-comm-push-CX40-sw0-L = pickᴰ 9 Sᴰ
  lem-comm-push-CX40-sw1-L : WsL → St 2359
  lem-comm-push-CX40-sw1-L = pickᴰ 10 Sᴰ
  lem-comm-push-CX40-sw2-L : WsL → St 2360
  lem-comm-push-CX40-sw2-L = pickᴰ 11 Sᴰ
  lem-comm-push-CZ04-sw0-L : WsL → St 2356
  lem-comm-push-CZ04-sw0-L = pickᴰ 12 Sᴰ
  lem-comm-push-CZ04-sw1-L : WsL → St 2361
  lem-comm-push-CZ04-sw1-L = pickᴰ 13 Sᴰ
  lem-comm-push-CZ04-sw2-L : WsL → St 2362
  lem-comm-push-CZ04-sw2-L = pickᴰ 14 Sᴰ
  lem-comm-push-CK40-sw1-L : WsL → St 1878
  lem-comm-push-CK40-sw1-L = pickᴰ 15 Sᴰ
  lem-comm-push-CK40-sw2-L : WsL → St 2363
  lem-comm-push-CK40-sw2-L = pickᴰ 16 Sᴰ
  lem-comm-push-SWAP04-sw2-L : WsL → St 2364
  lem-comm-push-SWAP04-sw2-L = pickᴰ 17 Sᴰ
  lem-comm-push-BOX⟨0·12⟩-sw1-L : WsL → St 2365
  lem-comm-push-BOX⟨0·12⟩-sw1-L = pickᴰ 18 Sᴰ
  lem-comm-push-BOX⟨0·12⟩-sw2-R : WsL → St 2366
  lem-comm-push-BOX⟨0·12⟩-sw2-R = pickᴰ 19 Sᴰ
  lem-comm-push-BOX⟨0·13⟩-sw2-L : WsL → St 2367
  lem-comm-push-BOX⟨0·13⟩-sw2-L = pickᴰ 20 Sᴰ
  lem-comm-push-BOX⟨0·21⟩-sw1-R : WsL → St 2368
  lem-comm-push-BOX⟨0·21⟩-sw1-R = pickᴰ 21 Sᴰ
  lem-comm-push-BOX⟨1·03⟩-sw0-L : WsL → St 2369
  lem-comm-push-BOX⟨1·03⟩-sw0-L = pickᴰ 22 Sᴰ
  lem-comm-push-BOX⟨2·03⟩-sw1-L : WsL → St 2370
  lem-comm-push-BOX⟨2·03⟩-sw1-L = pickᴰ 23 Sᴰ
  lem-comm-push-CS14-sw0-L : WsL → St 1622
  lem-comm-push-CS14-sw0-L = pickᴰ 24 Sᴰ
  lem-comm-push-CSd14-sw0-L : WsL → St 2371
  lem-comm-push-CSd14-sw0-L = pickᴰ 25 Sᴰ
  lem-comm-push-CX04-sw2-L : WsL → St 2372
  lem-comm-push-CX04-sw2-L = pickᴰ 26 Sᴰ
  lem-comm-push-SWAP04-sw0-L : WsL → St 2373
  lem-comm-push-SWAP04-sw0-L = pickᴰ 27 Sᴰ

private
  q1 : WsL → Eqn
  q1 c4 = wlE 64 c4
  q2 : WsL → Eqn
  q2 c4 = wlE 3 c4
  q3 : WsL → Eqn
  q3 c4 = eqn (ℓ "丬乥") (ℓ "乥丬") (c₂ (CX₀₁) (Swap))
  q4 : WsL → Eqn
  q4 c4 = eqn (ℓ "一乥") (ℓ "乥一") (c₁ (iI) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = wlE 65 c4
  q6 : WsL → Eqn
  q6 c4 = wlE 4 c4
  q7 : WsL → Eqn
  q7 c4 = eqn (ℓ "丬乼") (ℓ "乼丬") (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (ℓ "一乼") (ℓ "乼一") (c₁ (iI) (Swap ↑ ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (ℓ "乊两") (ℓ "两乊") (c₃ (Swap ↑) (K ↑))
  q10 : WsL → Eqn
  q10 c4 = wlE 5 c4
  q11 : WsL → Eqn
  q11 c4 = wlE 6 c4
  q12 : WsL → Eqn
  q12 c4 = wlE 7 c4
  q13 : WsL → Eqn
  q13 c4 = sE 2005 (lem-comm-push-CS04-sw1-R c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (ℓ "一乊") (ℓ "乊一") (c₁ (iI) (Swap))
  q15 : WsL → Eqn
  q15 c4 = eqn (ℓ "乥两") (ℓ "两乥") (c₄ (Swap ↑ ↑) (K))
  q16 : WsL → Eqn
  q16 c4 = wlE 8 c4
  q17 : WsL → Eqn
  q17 c4 = wlE 9 c4
  q18 : WsL → Eqn
  q18 c4 = sE 2350 (lem-comm-push-CS04-sw2-R c4)
  q19 : WsL → Eqn
  q19 c4 = sE 1621 (lem-comm-push-CS04-sw1-L c4)
  q20 : WsL → Eqn
  q20 c4 = wlE 10 c4
  q21 : WsL → Eqn
  q21 c4 = eqn (ℓ "乊乺") (ℓ "乺乊") (c₃ (Swap ↑) (CS • CS • CS))
  q22 : WsL → Eqn
  q22 c4 = eqn (ℓ "乊乹") (ℓ "乹乊") (c₃ (Swap ↑) (CS))
  q23 : WsL → Eqn
  q23 c4 = wlE 11 c4
  q24 : WsL → Eqn
  q24 c4 = wlE 12 c4
  q25 : WsL → Eqn
  q25 c4 = wlE 13 c4
  q26 : WsL → Eqn
  q26 c4 = wlE 14 c4
  q27 : WsL → Eqn
  q27 c4 = wlE 66 c4
  q28 : WsL → Eqn
  q28 c4 = wlE 67 c4

-- comm push TOFF403 sw1 L: 110 steps
lem-comm-push-TOFF403-sw1-L : WsL → ⟪ (ℓ "亣乊") ⟫ʷ ≈ ⟪ (ℓ "乊亣") ⟫ʷ
lem-comm-push-TOFF403-sw1-L c4 = derive (ℓ "亣乊") (ℓ "乊亣")
  (re 0 1 (ℓ "乥亟乥") ∷
   re 1 1 (ℓ "乊亗乊") ∷
   re 2 1 (ℓ "乼亓乼") ∷
   re 3 1 (ℓ "乥亏乥") ∷
   re 4 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q13 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q11 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q18 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (ℓ "乥丳乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (ℓ "乥丳乥") ∷
   rw 6 (q2 c4) ∷
   rw 7 (q18 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   re 8 1 (ℓ "乊丬乊") ∷
   rw 7 (q11 c4) ∷
   rw 8 (q13 c4) ∷
   rw 9 (q9 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   re 6 1 (ℓ "乼乎乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (ℓ "乼乏乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 10 1 (ℓ "乼丶乼") ∷
   rw 9 (q6 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw⁻ 11 (q8 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   re 7 1 (ℓ "乥乇乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥么乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 11 1 (ℓ "乥丯乥") ∷
   rw 10 (q2 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   re 5 8 (ℓ "亏") ∷
   re 4 3 (ℓ "亓") ∷
   re 3 3 (ℓ "亗") ∷
   re 2 3 (ℓ "亟") ∷
   re 1 3 (ℓ "亣") ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = wlE 25 c4
  q30 : WsL → Eqn
  q30 c4 = eqn (ℓ "丫两") (ℓ "两丫") (c₂ (Swap) (K ↑ ↑))
  q31 : WsL → Eqn
  q31 c4 = sE 1620 (lem-comm-push-CS04-sw0-L c4)
  q32 : WsL → Eqn
  q32 c4 = wlE 16 c4
  q33 : WsL → Eqn
  q33 c4 = eqn (ℓ "丫乺") (ℓ "乺丫") (c₂ (Swap) ((CS • CS • CS) ↑))
  q34 : WsL → Eqn
  q34 c4 = eqn (ℓ "丫乹") (ℓ "乹丫") (c₂ (Swap) (CS ↑))
  q35 : WsL → Eqn
  q35 c4 = wlE 17 c4
  q36 : WsL → Eqn
  q36 c4 = eqn (ℓ "之乼") (ℓ "乼之") (c₃ (CX₀₁ ↑) (Swap))
  q37 : WsL → Eqn
  q37 c4 = wlE 68 c4

-- comm push TOFF403 sw0 L: 86 steps
lem-comm-push-TOFF403-sw0-L : WsL → ⟪ (ℓ "亣丫") ⟫ʷ ≈ ⟪ (ℓ "丫亯") ⟫ʷ
lem-comm-push-TOFF403-sw0-L c4 = derive (ℓ "亣丫") (ℓ "丫亯")
  (re 0 1 (ℓ "乥亟乥") ∷
   re 1 1 (ℓ "乊亗乊") ∷
   re 2 1 (ℓ "乼亓乼") ∷
   re 3 1 (ℓ "乥亏乥") ∷
   re 4 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q13 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q11 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q18 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 2 (q32 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (ℓ "乥之乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (ℓ "乥之乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 7 1 (ℓ "乼乣乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   re 9 1 (ℓ "乼乎乼") ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 3 (q37 c4) ∷
   re 3 8 (ℓ "产") ∷
   re 2 3 (ℓ "享") ∷
   re 1 3 (ℓ "亯") ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (ℓ "丌乥") (ℓ "乥丌") (c₁ (K) (Swap ↑))
  q39 : WsL → Eqn
  q39 c4 = eqn (ℓ "丌乼") (ℓ "乼丌") (c₁ (K) (Swap ↑ ↑))
  q40 : WsL → Eqn
  q40 c4 = sE 2349 (lem-comm-push-CS04-sw2-L c4)
  q41 : WsL → Eqn
  q41 c4 = wlE 48 c4

-- comm push TOFF014 sw2 L: 62 steps
lem-comm-push-TOFF014-sw2-L : WsL → ⟪ (ℓ "井乥") ⟫ʷ ≈ ⟪ (ℓ "乥井") ⟫ʷ
lem-comm-push-TOFF014-sw2-L c4 = derive (ℓ "井乥") (ℓ "乥井")
  (re 0 1 (ℓ "乼云乼") ∷
   re 1 1 (ℓ "乥亍乥") ∷
   re 2 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q38 c4) ∷
   rw 5 (q40 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q41 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q35 c4) ∷
   rw 0 (q38 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (ℓ "亍") ∷
   re 2 3 (ℓ "云") ∷
   re 1 3 (ℓ "井") ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (ℓ "丒乥") (ℓ "乥丒") (c₂ (K ↑) (Swap))
  q43 : WsL → Eqn
  q43 c4 = eqn (ℓ "丒乼") (ℓ "乼丒") (c₂ (K ↑) (Swap ↑))

-- comm push TOFF104 sw2 L: 62 steps
lem-comm-push-TOFF104-sw2-L : WsL → ⟪ (ℓ "亖乥") ⟫ʷ ≈ ⟪ (ℓ "乥亖") ⟫ʷ
lem-comm-push-TOFF104-sw2-L c4 = derive (ℓ "亖乥") (ℓ "乥亖")
  (re 0 1 (ℓ "乼互乼") ∷
   re 1 1 (ℓ "乥于乥") ∷
   re 2 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 (q43 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q42 c4) ∷
   rw 5 (q40 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q41 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q35 c4) ∷
   rw 0 (q42 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (ℓ "于") ∷
   re 2 3 (ℓ "互") ∷
   re 1 3 (ℓ "亖") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = sE 2362 (lem-comm-push-CZ04-sw2-L c4)
  q45 : WsL → Eqn
  q45 c4 = sE 2361 (lem-comm-push-CZ04-sw1-L c4)
  q46 : WsL → Eqn
  q46 c4 = wlE 18 c4
  q47 : WsL → Eqn
  q47 c4 = sE 2356 (lem-comm-push-CZ04-sw0-L c4)

-- resp CZ04 at 3: 6 steps
lem-resp-CZ04-at-3 : WsL → ⟪ (ℓ "丿") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乗丫乊乥") ⟫ʷ
lem-resp-CZ04-at-3 c4 = derive (ℓ "丿") (ℓ "乥乊丫乗丫乊乥")
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q44 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q45 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q47 c4) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = sE 2360 (lem-comm-push-CX40-sw2-L c4)
  q49 : WsL → Eqn
  q49 c4 = sE 2359 (lem-comm-push-CX40-sw1-L c4)
  q50 : WsL → Eqn
  q50 c4 = sE 2358 (lem-comm-push-CX40-sw0-L c4)

-- resp CX40 at 3: 6 steps
lem-resp-CX40-at-3 : WsL → ⟪ (ℓ "亀") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亃丫乊乥") ⟫ʷ
lem-resp-CX40-at-3 c4 = derive (ℓ "亀") (ℓ "乥乊丫亃丫乊乥")
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

-- resp CX40 at 1: 2 steps
lem-resp-CX40-at-1 : WsL → ⟪ (ℓ "亀") ⟫ʷ ≈ ⟪ (ℓ "丫亃丫") ⟫ʷ
lem-resp-CX40-at-1 c4 = derive (ℓ "亀") (ℓ "丫亃丫")
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = sE 1877 (lem-comm-push-CK40-sw0-L c4)

-- resp CK40 at 1: 2 steps
lem-resp-CK40-at-1 : WsL → ⟪ (ℓ "亁") ⟫ʷ ≈ ⟪ (ℓ "丫亄丫") ⟫ʷ
lem-resp-CK40-at-1 c4 = derive (ℓ "亁") (ℓ "丫亄丫")
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = sE 2357 (lem-comm-push-CKd40-sw0-L c4)

-- resp CKd40 at 1: 2 steps
lem-resp-CKd40-at-1 : WsL → ⟪ (ℓ "亂") ⟫ʷ ≈ ⟪ (ℓ "丫亅丫") ⟫ʷ
lem-resp-CKd40-at-1 c4 = derive (ℓ "亂") (ℓ "丫亅丫")
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q52 c4) ∷ []) Eq.refl

-- resp CZ04 at 2: 4 steps
lem-resp-CZ04-at-2 : WsL → ⟪ (ℓ "丿") ⟫ʷ ≈ ⟪ (ℓ "乊丫乗丫乊") ⟫ʷ
lem-resp-CZ04-at-2 c4 = derive (ℓ "丿") (ℓ "乊丫乗丫乊")
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

-- resp CX40 at 2: 4 steps
lem-resp-CX40-at-2 : WsL → ⟪ (ℓ "亀") ⟫ʷ ≈ ⟪ (ℓ "乊丫亃丫乊") ⟫ʷ
lem-resp-CX40-at-2 c4 = derive (ℓ "亀") (ℓ "乊丫亃丫乊")
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q49 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = sE 1878 (lem-comm-push-CK40-sw1-L c4)

-- resp CK40 at 2: 4 steps
lem-resp-CK40-at-2 : WsL → ⟪ (ℓ "亁") ⟫ʷ ≈ ⟪ (ℓ "乊丫亄丫乊") ⟫ʷ
lem-resp-CK40-at-2 c4 = derive (ℓ "亁") (ℓ "乊丫亄丫乊")
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q53 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = sE 2363 (lem-comm-push-CK40-sw2-L c4)

-- resp CK40 at 3: 6 steps
lem-resp-CK40-at-3 : WsL → ⟪ (ℓ "亁") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亄丫乊乥") ⟫ʷ
lem-resp-CK40-at-3 c4 = derive (ℓ "亁") (ℓ "乥乊丫亄丫乊乥")
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q54 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q53 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = wlE 40 c4
  q56 : WsL → Eqn
  q56 c4 = wlE 47 c4
  q57 : WsL → Eqn
  q57 c4 = wlE 29 c4
  q58 : WsL → Eqn
  q58 c4 = wlE 1 c4
  q59 : WsL → Eqn
  q59 c4 = eqn (ℓ "丘乼") (ℓ "乼丘") (c₃ (K ↑ ↑) (Swap))
  q60 : WsL → Eqn
  q60 c4 = eqn (ℓ "丳乼") (ℓ "乼丳") (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q61 : WsL → Eqn
  q61 c4 = wlE 73 c4

-- comm push TOFF203 sw3 L: 76 steps
lem-comm-push-TOFF203-sw3-L : WsL → ⟪ (ℓ "亚乼") ⟫ʷ ≈ ⟪ (ℓ "乼亞") ⟫ʷ
lem-comm-push-TOFF203-sw3-L c4 = derive (ℓ "亚乼") (ℓ "乼亞")
  (re 0 1 (ℓ "乊互乊") ∷
   re 1 1 (ℓ "乥于乥") ∷
   re 2 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q59 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw 2 (q60 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 0 (q59 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q42 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 4 8 (ℓ "于") ∷
   re 3 3 (ℓ "互") ∷
   re 2 3 (ℓ "亖") ∷
   re 1 3 (ℓ "亞") ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = wlE 46 c4
  q63 : WsL → Eqn
  q63 c4 = wlE 28 c4

-- comm push TOFF204 sw3 L: 76 steps
lem-comm-push-TOFF204-sw3-L : WsL → ⟪ (ℓ "亞乼") ⟫ʷ ≈ ⟪ (ℓ "乼亚") ⟫ʷ
lem-comm-push-TOFF204-sw3-L c4 = derive (ℓ "亞乼") (ℓ "乼亚")
  (re 0 1 (ℓ "乊亖乊") ∷
   re 1 1 (ℓ "乼互乼") ∷
   re 2 1 (ℓ "乥于乥") ∷
   re 3 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 2 (q42 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q43 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q59 c4) ∷
   re 5 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw 4 (q60 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 5 (q6 c4) ∷
   rw 2 (q60 c4) ∷
   re 1 1 (ℓ "乼乢乼") ∷
   rw 3 (q6 c4) ∷
   rw 0 (q59 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (ℓ "于") ∷
   re 2 3 (ℓ "互") ∷
   re 1 3 (ℓ "亚") ∷ []) Eq.refl

-- comm push CCZ023 sw3 L: 58 steps
lem-comm-push-CCZ023-sw3-L : WsL → ⟪ (ℓ "亘乼") ⟫ʷ ≈ ⟪ (ℓ "乼亜") ⟫ʷ
lem-comm-push-CCZ023-sw3-L c4 = derive (ℓ "亘乼") (ℓ "乼亜")
  (re 0 1 (ℓ "乊亐乊") ∷
   re 1 1 (ℓ "乥二乥") ∷
   re 2 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乏") ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "丶") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   re 1 3 (ℓ "丳") ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q58 c4) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 (q60 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw 1 (q60 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q11 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   re 4 5 (ℓ "二") ∷
   re 3 3 (ℓ "亐") ∷
   re 2 3 (ℓ "五") ∷
   re 1 3 (ℓ "亜") ∷ []) Eq.refl

-- comm push CCZ024 sw3 L: 58 steps
lem-comm-push-CCZ024-sw3-L : WsL → ⟪ (ℓ "亜乼") ⟫ʷ ≈ ⟪ (ℓ "乼亘") ⟫ʷ
lem-comm-push-CCZ024-sw3-L c4 = derive (ℓ "亜乼") (ℓ "乼亘")
  (re 0 1 (ℓ "乊五乊") ∷
   re 1 1 (ℓ "乼亐乼") ∷
   re 2 1 (ℓ "乥二乥") ∷
   re 3 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   re 1 3 (ℓ "丳") ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw 4 (q13 c4) ∷
   rw 5 (q11 c4) ∷
   re 4 1 (ℓ "乼丶乼") ∷
   rw 6 (q6 c4) ∷
   rw 3 (q60 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 4 (q6 c4) ∷
   rw 1 (q60 c4) ∷
   re 0 1 (ℓ "乼乢乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (ℓ "乥乇乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (ℓ "乥么乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥丯乥") ∷
   rw 7 (q2 c4) ∷
   re 3 5 (ℓ "二") ∷
   re 2 3 (ℓ "亐") ∷
   re 1 3 (ℓ "亘") ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = sE 2364 (lem-comm-push-SWAP04-sw2-L c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (ℓ "义乼") (ℓ "乼义") (c₃ (CZ ↑) (Swap))
  q66 : WsL → Eqn
  q66 c4 = wlE 36 c4
  q67 : WsL → Eqn
  q67 c4 = eqn (ℓ "丫乤") (ℓ "乤丫") (c₂ (Swap) (CZ))
  q68 : WsL → Eqn
  q68 c4 = wlE 33 c4

-- comm SWAP03 BOX(2;14): 21 steps
lem-comm-SWAP03-BOX⟨2·14⟩ : WsL → ⟪ (ℓ "丹休") ⟫ʷ ≈ ⟪ (ℓ "休丹") ⟫ʷ
lem-comm-SWAP03-BOX⟨2·14⟩ c4 = derive (ℓ "丹休") (ℓ "休丹")
  (re 1 1 (ℓ "乗") ∷
   re 1 1 (ℓ "乼乥义乥乼") ∷
   rw⁻ 0 (q6 c4) ∷
   re 1 3 (ℓ "乀") ∷
   rw 1 (q64 c4) ∷
   re 2 1 (ℓ "乼乥乊丫乊乥乼") ∷
   rw⁻ 8 (q65 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "乐") ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   re 4 1 (ℓ "乥义乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   re 3 7 (ℓ "乀") ∷
   rw 3 (q64 c4) ∷
   re 4 1 (ℓ "乼丹乼") ∷
   rw 6 (q6 c4) ∷
   re 0 5 (ℓ "乗") ∷
   re 0 1 (ℓ "休") ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (ℓ "乊丞") (ℓ "丞乊") (c₃ (Swap ↑) (K))

-- comm push TOFF302 sw3 L: 76 steps
lem-comm-push-TOFF302-sw3-L : WsL → ⟪ (ℓ "些乼") ⟫ʷ ≈ ⟪ (ℓ "乼亟") ⟫ʷ
lem-comm-push-TOFF302-sw3-L c4 = derive (ℓ "些乼") (ℓ "乼亟")
  (re 0 1 (ℓ "乊亓乊") ∷
   re 1 1 (ℓ "乥亏乥") ∷
   re 2 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw 0 (q69 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q58 c4) ∷
   rw 6 (q69 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw 2 (q60 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 4 8 (ℓ "亏") ∷
   re 3 3 (ℓ "亓") ∷
   re 2 3 (ℓ "亗") ∷
   re 1 3 (ℓ "亟") ∷ []) Eq.refl

-- comm push TOFF402 sw3 L: 76 steps
lem-comm-push-TOFF402-sw3-L : WsL → ⟪ (ℓ "亟乼") ⟫ʷ ≈ ⟪ (ℓ "乼些") ⟫ʷ
lem-comm-push-TOFF402-sw3-L c4 = derive (ℓ "亟乼") (ℓ "乼些")
  (re 0 1 (ℓ "乊亗乊") ∷
   re 1 1 (ℓ "乼亓乼") ∷
   re 2 1 (ℓ "乥亏乥") ∷
   re 3 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q13 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q5 c4) ∷
   re 5 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw 4 (q60 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 5 (q6 c4) ∷
   rw 2 (q60 c4) ∷
   re 1 1 (ℓ "乼乢乼") ∷
   rw 3 (q6 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q69 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw 8 (q69 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (ℓ "亏") ∷
   re 2 3 (ℓ "亓") ∷
   re 1 3 (ℓ "些") ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = sE 2373 (lem-comm-push-SWAP04-sw0-L c4)

-- resp SWAP04 at 1: 2 steps
lem-resp-SWAP04-at-1 : WsL → ⟪ (ℓ "乀") ⟫ʷ ≈ ⟪ (ℓ "丫乘丫") ⟫ʷ
lem-resp-SWAP04-at-1 c4 = derive (ℓ "乀") (ℓ "丫乘丫")
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = sE 2372 (lem-comm-push-CX04-sw2-L c4)
  q72 : WsL → Eqn
  q72 c4 = sE 2355 (lem-comm-push-CX04-sw1-L c4)
  q73 : WsL → Eqn
  q73 c4 = sE 2354 (lem-comm-push-CX04-sw0-L c4)

-- resp CX04 at 3: 6 steps
lem-resp-CX04-at-3 : WsL → ⟪ (ℓ "乁") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乙丫乊乥") ⟫ʷ
lem-resp-CX04-at-3 c4 = derive (ℓ "乁") (ℓ "乥乊丫乙丫乊乥")
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q71 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

-- comm SWAP03 BOX(2;41): 21 steps
lem-comm-SWAP03-BOX⟨2·41⟩ : WsL → ⟪ (ℓ "丹佗") ⟫ʷ ≈ ⟪ (ℓ "佗丹") ⟫ʷ
lem-comm-SWAP03-BOX⟨2·41⟩ c4 = derive (ℓ "丹佗") (ℓ "佗丹")
  (re 1 1 (ℓ "乗") ∷
   re 1 1 (ℓ "乼乥义乥乼") ∷
   rw⁻ 0 (q6 c4) ∷
   re 1 3 (ℓ "乀") ∷
   rw 1 (q64 c4) ∷
   re 2 1 (ℓ "乼乥乊丫乊乥乼") ∷
   rw⁻ 8 (q65 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "乐") ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   re 4 1 (ℓ "乥义乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   re 3 7 (ℓ "乀") ∷
   rw 3 (q64 c4) ∷
   re 4 1 (ℓ "乼丹乼") ∷
   rw 6 (q6 c4) ∷
   re 0 5 (ℓ "乗") ∷
   re 0 1 (ℓ "佗") ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = sE 2370 (lem-comm-push-BOX⟨2·03⟩-sw1-L c4)
  q75 : WsL → Eqn
  q75 c4 = wlE 101 c4
  q76 : WsL → Eqn
  q76 c4 = wlE 102 c4

-- comm push BOX(0;213) sw1 L: 8 steps
lem-comm-push-BOX⟨0·213⟩-sw1-L : WsL → ⟪ (ℓ "仉乊") ⟫ʷ ≈ ⟪ (ℓ "乊亶") ⟫ʷ
lem-comm-push-BOX⟨0·213⟩-sw1-L c4 = derive (ℓ "仉乊") (ℓ "乊亶")
  (re 0 1 (ℓ "二亍仈亍二仈") ∷
   rw 5 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 2 (q74 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   rw 0 (q75 c4) ∷
   re 1 6 (ℓ "亶") ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = sE 2369 (lem-comm-push-BOX⟨1·03⟩-sw0-L c4)
  q78 : WsL → Eqn
  q78 c4 = wlE 103 c4
  q79 : WsL → Eqn
  q79 c4 = wlE 104 c4

-- comm push BOX(0;123) sw0 L: 8 steps
lem-comm-push-BOX⟨0·123⟩-sw0-L : WsL → ⟪ (ℓ "亶丫") ⟫ʷ ≈ ⟪ (ℓ "丫仃") ⟫ʷ
lem-comm-push-BOX⟨0·123⟩-sw0-L c4 = derive (ℓ "亶丫") (ℓ "丫仃")
  (re 0 1 (ℓ "二亍亵亍二亵") ∷
   rw 5 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q79 c4) ∷
   rw 2 (q77 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw 0 (q78 c4) ∷
   re 1 6 (ℓ "仃") ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = wlE 107 c4
  q81 : WsL → Eqn
  q81 c4 = sE 2371 (lem-comm-push-CSd14-sw0-L c4)
  q82 : WsL → Eqn
  q82 c4 = sE 1622 (lem-comm-push-CS14-sw0-L c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (ℓ "乄乼") (ℓ "乼乄") (c₂ (CX₁₀) (Swap ↑))
  q84 : WsL → Eqn
  q84 c4 = eqn (ℓ "乄乥") (ℓ "乥乄") (c₂ (CX₁₀) (Swap))
  q85 : WsL → Eqn
  q85 c4 = wlE 108 c4

-- comm push CCZ014 sw0 L: 48 steps
lem-comm-push-CCZ014-sw0-L : WsL → ⟪ (ℓ "五丫") ⟫ʷ ≈ ⟪ (ℓ "丫五") ⟫ʷ
lem-comm-push-CCZ014-sw0-L c4 = derive (ℓ "五丫") (ℓ "丫五")
  (re 0 1 (ℓ "乼亐乼") ∷
   re 1 1 (ℓ "乥二乥") ∷
   re 2 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乏") ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "丶") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 0 3 (ℓ "乕") ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乖") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 (q6 c4) ∷
   rw 4 (q31 c4) ∷
   rw 3 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q82 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 3 1 (ℓ "乼丶乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   re 5 1 (ℓ "乼丷乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   re 7 1 (ℓ "乼乎乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (ℓ "乥丯乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   re 6 1 (ℓ "乥丰乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 7 (q2 c4) ∷
   rw 3 (q85 c4) ∷
   re 3 5 (ℓ "二") ∷
   re 2 3 (ℓ "亐") ∷
   re 1 3 (ℓ "五") ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = wlE 109 c4
  q87 : WsL → Eqn
  q87 c4 = wlE 110 c4

-- comm push TOFF104 sw0 L: 63 steps
lem-comm-push-TOFF104-sw0-L : WsL → ⟪ (ℓ "亖丫") ⟫ʷ ≈ ⟪ (ℓ "丫井") ⟫ʷ
lem-comm-push-TOFF104-sw0-L c4 = derive (ℓ "亖丫") (ℓ "丫井")
  (re 0 1 (ℓ "乼互乼") ∷
   re 1 1 (ℓ "乥于乥") ∷
   re 2 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 (q43 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 6 (q86 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   re 4 1 (ℓ "乼丶乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   re 6 1 (ℓ "乼丷乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   re 8 1 (ℓ "乼乎乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   re 5 1 (ℓ "乥丯乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   re 7 1 (ℓ "乥丰乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   re 9 1 (ℓ "乥乇乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 3 (q87 c4) ∷
   re 3 8 (ℓ "亍") ∷
   re 2 3 (ℓ "云") ∷
   re 1 3 (ℓ "井") ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = sE 2367 (lem-comm-push-BOX⟨0·13⟩-sw2-L c4)

-- comm push BOX(1;023) sw2 L: 12 steps
lem-comm-push-BOX⟨1·023⟩-sw2-L : WsL → ⟪ (ℓ "仃乥") ⟫ʷ ≈ ⟪ (ℓ "乥仅") ⟫ʷ
lem-comm-push-BOX⟨1·023⟩-sw2-L c4 = derive (ℓ "仃乥") (ℓ "乥仅")
  (re 0 1 (ℓ "二于人于二人") ∷
   rw 5 (q88 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 5 3 (ℓ "亐") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "互") ∷
   rw 2 (q88 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "互") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "亐") ∷
   re 1 6 (ℓ "仅") ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = sE 2365 (lem-comm-push-BOX⟨0·12⟩-sw1-L c4)

-- comm push BOX(1;032) sw1 L: 12 steps
lem-comm-push-BOX⟨1·032⟩-sw1-L : WsL → ⟪ (ℓ "仅乊") ⟫ʷ ≈ ⟪ (ℓ "乊仝") ⟫ʷ
lem-comm-push-BOX⟨1·032⟩-sw1-L c4 = derive (ℓ "仅乊") (ℓ "乊仝")
  (re 0 1 (ℓ "亐互亴互亐亴") ∷
   rw 5 (q89 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 3 (ℓ "亘") ∷
   rw⁻ 3 (q11 c4) ∷
   re 4 3 (ℓ "亚") ∷
   rw 2 (q89 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   re 2 3 (ℓ "亚") ∷
   rw⁻ 0 (q11 c4) ∷
   re 1 3 (ℓ "亘") ∷
   re 1 6 (ℓ "仝") ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = sE 2368 (lem-comm-push-BOX⟨0·21⟩-sw1-R c4)

-- comm push BOX(2;031) sw1 R: 12 steps
lem-comm-push-BOX⟨2·031⟩-sw1-R : WsL → ⟪ (ℓ "乊仝") ⟫ʷ ≈ ⟪ (ℓ "仅乊") ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw1-R c4 = derive (ℓ "乊仝") (ℓ "仅乊")
  (re 1 1 (ℓ "亘亚仇亚亘仇") ∷
   re 1 1 (ℓ "乊亐乊") ∷
   rw 0 (q11 c4) ∷
   re 2 1 (ℓ "乊互乊") ∷
   rw 1 (q11 c4) ∷
   rw 2 (q90 c4) ∷
   re 4 1 (ℓ "乊互乊") ∷
   rw 3 (q11 c4) ∷
   re 5 1 (ℓ "乊亐乊") ∷
   rw 4 (q11 c4) ∷
   rw 5 (q90 c4) ∷
   re 0 6 (ℓ "仅") ∷ []) Eq.refl

-- comm push CCZ014 sw2 R: 47 steps
lem-comm-push-CCZ014-sw2-R : WsL → ⟪ (ℓ "乥五") ⟫ʷ ≈ ⟪ (ℓ "五乥") ⟫ʷ
lem-comm-push-CCZ014-sw2-R c4 = derive (ℓ "乥五") (ℓ "五乥")
  (re 1 1 (ℓ "乼亐乼") ∷
   re 2 1 (ℓ "乥二乥") ∷
   re 3 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   re 2 1 (ℓ "乼乎乼") ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   re 4 1 (ℓ "乼乏乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (ℓ "乼丶乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 3 1 (ℓ "乥乇乥") ∷
   rw 2 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (ℓ "乥么乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥丯乥") ∷
   rw 6 (q2 c4) ∷
   re 2 5 (ℓ "二") ∷
   re 1 3 (ℓ "亐") ∷
   re 0 3 (ℓ "五") ∷ []) Eq.refl

-- comm push TOFF014 sw2 R: 62 steps
lem-comm-push-TOFF014-sw2-R : WsL → ⟪ (ℓ "乥井") ⟫ʷ ≈ ⟪ (ℓ "井乥") ⟫ʷ
lem-comm-push-TOFF014-sw2-R c4 = derive (ℓ "乥井") (ℓ "井乥")
  (re 1 1 (ℓ "乼云乼") ∷
   re 2 1 (ℓ "乥亍乥") ∷
   re 3 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 2 (q38 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   re 3 1 (ℓ "乼乎乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (ℓ "乼乏乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (ℓ "乼丶乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   re 4 1 (ℓ "乥乇乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (ℓ "乥么乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥丯乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (ℓ "亍") ∷
   re 1 3 (ℓ "云") ∷
   re 0 3 (ℓ "井") ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = sE 2366 (lem-comm-push-BOX⟨0·12⟩-sw2-R c4)

-- comm push BOX(1;032) sw2 R: 12 steps
lem-comm-push-BOX⟨1·032⟩-sw2-R : WsL → ⟪ (ℓ "乥仅") ⟫ʷ ≈ ⟪ (ℓ "仃乥") ⟫ʷ
lem-comm-push-BOX⟨1·032⟩-sw2-R c4 = derive (ℓ "乥仅") (ℓ "仃乥")
  (re 1 1 (ℓ "亐互亴互亐亴") ∷
   re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q2 c4) ∷
   re 2 1 (ℓ "乥于乥") ∷
   rw 1 (q2 c4) ∷
   rw 2 (q91 c4) ∷
   re 4 1 (ℓ "乥于乥") ∷
   rw 3 (q2 c4) ∷
   re 5 1 (ℓ "乥二乥") ∷
   rw 4 (q2 c4) ∷
   rw 5 (q91 c4) ∷
   re 0 6 (ℓ "仃") ∷ []) Eq.refl
