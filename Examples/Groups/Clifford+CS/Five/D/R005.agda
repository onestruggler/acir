{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR005 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R005 (Sᴰ : SR005) where

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
  lem-comm-push-CS04-sw1-L : WsL → St 1621
  lem-comm-push-CS04-sw1-L = pickᴰ 1 Sᴰ
  lem-comm-push-CS04-sw1-R : WsL → St 2005
  lem-comm-push-CS04-sw1-R = pickᴰ 2 Sᴰ
  lem-comm-push-CS04-sw2-L : WsL → St 2349
  lem-comm-push-CS04-sw2-L = pickᴰ 3 Sᴰ
  lem-comm-push-CS04-sw2-R : WsL → St 2350
  lem-comm-push-CS04-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-CSd04-sw0-L : WsL → St 2351
  lem-comm-push-CSd04-sw0-L = pickᴰ 5 Sᴰ
  lem-comm-push-CSd04-sw1-L : WsL → St 2352
  lem-comm-push-CSd04-sw1-L = pickᴰ 6 Sᴰ
  lem-comm-push-CSd04-sw2-L : WsL → St 2353
  lem-comm-push-CSd04-sw2-L = pickᴰ 7 Sᴰ
  lem-comm-push-CX04-sw0-L : WsL → St 2354
  lem-comm-push-CX04-sw0-L = pickᴰ 8 Sᴰ
  lem-comm-push-CX04-sw1-L : WsL → St 2355
  lem-comm-push-CX04-sw1-L = pickᴰ 9 Sᴰ
  lem-comm-push-CZ04-sw0-L : WsL → St 2356
  lem-comm-push-CZ04-sw0-L = pickᴰ 10 Sᴰ

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
  q5 c4 = wlE 5 c4
  q6 : WsL → Eqn
  q6 c4 = wlE 6 c4
  q7 : WsL → Eqn
  q7 c4 = wlE 7 c4
  q8 : WsL → Eqn
  q8 c4 = sE 2005 (lem-comm-push-CS04-sw1-R c4)
  q9 : WsL → Eqn
  q9 c4 = wlE 8 c4
  q10 : WsL → Eqn
  q10 c4 = wlE 9 c4
  q11 : WsL → Eqn
  q11 c4 = sE 2350 (lem-comm-push-CS04-sw2-R c4)
  q12 : WsL → Eqn
  q12 c4 = sE 1621 (lem-comm-push-CS04-sw1-L c4)
  q13 : WsL → Eqn
  q13 c4 = wlE 10 c4
  q14 : WsL → Eqn
  q14 c4 = eqn (ℓ "乊乺") (ℓ "乺乊") (c₃ (Swap ↑) (CS • CS • CS))
  q15 : WsL → Eqn
  q15 c4 = eqn (ℓ "乊乹") (ℓ "乹乊") (c₃ (Swap ↑) (CS))
  q16 : WsL → Eqn
  q16 c4 = wlE 11 c4
  q17 : WsL → Eqn
  q17 c4 = wlE 12 c4
  q18 : WsL → Eqn
  q18 c4 = wlE 13 c4
  q19 : WsL → Eqn
  q19 c4 = wlE 14 c4

-- comm push CCZ034 sw1 L: 83 steps
lem-comm-push-CCZ034-sw1-L : WsL → ⟪ (ℓ "亠乊") ⟫ʷ ≈ ⟪ (ℓ "乊亠") ⟫ʷ
lem-comm-push-CCZ034-sw1-L c4 = derive (ℓ "亠乊") (ℓ "乊亠")
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
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q8 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "为") ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "为") ∷
   rw 4 (q11 c4) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   re 4 1 (ℓ "乥丳乥") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   re 6 1 (ℓ "乥丳乥") ∷
   rw 5 (q1 c4) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q6 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q1 c4) ∷
   re 5 5 (ℓ "二") ∷
   re 4 3 (ℓ "亐") ∷
   re 3 3 (ℓ "五") ∷
   re 2 3 (ℓ "亜") ∷
   re 1 3 (ℓ "亠") ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = sE 1620 (lem-comm-push-CS04-sw0-L c4)
  q21 : WsL → Eqn
  q21 c4 = wlE 16 c4
  q22 : WsL → Eqn
  q22 c4 = eqn (ℓ "丫乺") (ℓ "乺丫") (c₂ (Swap) ((CS • CS • CS) ↑))
  q23 : WsL → Eqn
  q23 c4 = eqn (ℓ "丫乹") (ℓ "乹丫") (c₂ (Swap) (CS ↑))
  q24 : WsL → Eqn
  q24 c4 = wlE 17 c4
  q25 : WsL → Eqn
  q25 c4 = eqn (ℓ "之乼") (ℓ "乼之") (c₃ (CX₀₁ ↑) (Swap))

-- comm push CCZ034 sw0 L: 64 steps
lem-comm-push-CCZ034-sw0-L : WsL → ⟪ (ℓ "亠丫") ⟫ʷ ≈ ⟪ (ℓ "丫京") ⟫ʷ
lem-comm-push-CCZ034-sw0-L c4 = derive (ℓ "亠丫") (ℓ "丫京")
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
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q8 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "为") ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "为") ∷
   rw 4 (q11 c4) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 0 (q23 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   re 4 1 (ℓ "乥之乥") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   re 6 1 (ℓ "乥之乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (ℓ "乼乎乼") ∷
   rw 7 (q3 c4) ∷
   re 3 5 (ℓ "交") ∷
   re 2 3 (ℓ "亨") ∷
   re 1 3 (ℓ "京") ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (ℓ "丌乥") (ℓ "乥丌") (c₁ (K) (Swap ↑))
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "一乥") (ℓ "乥一") (c₁ (iI) (Swap ↑))
  q28 : WsL → Eqn
  q28 c4 = eqn (ℓ "丌乼") (ℓ "乼丌") (c₁ (K) (Swap ↑ ↑))
  q29 : WsL → Eqn
  q29 c4 = eqn (ℓ "一乼") (ℓ "乼一") (c₁ (iI) (Swap ↑ ↑))
  q30 : WsL → Eqn
  q30 c4 = eqn (ℓ "丌乊") (ℓ "乊丌") (c₁ (K) (Swap))
  q31 : WsL → Eqn
  q31 c4 = eqn (ℓ "一乊") (ℓ "乊一") (c₁ (iI) (Swap))
  q32 : WsL → Eqn
  q32 c4 = wlE 25 c4
  q33 : WsL → Eqn
  q33 c4 = wlE 26 c4
  q34 : WsL → Eqn
  q34 c4 = eqn (ℓ "丒乥") (ℓ "乥丒") (c₂ (K ↑) (Swap))
  q35 : WsL → Eqn
  q35 c4 = eqn (ℓ "丒乼") (ℓ "乼丒") (c₂ (K ↑) (Swap ↑))
  q36 : WsL → Eqn
  q36 c4 = wlE 27 c4

-- comm push TOFF034 sw0 L: 86 steps
lem-comm-push-TOFF034-sw0-L : WsL → ⟪ (ℓ "亡丫") ⟫ʷ ≈ ⟪ (ℓ "丫亭") ⟫ʷ
lem-comm-push-TOFF034-sw0-L c4 = derive (ℓ "亡丫") (ℓ "丫亭")
  (re 0 1 (ℓ "乥亝乥") ∷
   re 1 1 (ℓ "乊井乊") ∷
   re 2 1 (ℓ "乼云乼") ∷
   re 3 1 (ℓ "乥亍乥") ∷
   re 4 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (ℓ "乥之乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (ℓ "乥之乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (ℓ "乼乣乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   re 9 1 (ℓ "乼乎乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw 3 (q36 c4) ∷
   re 3 8 (ℓ "亥") ∷
   re 2 3 (ℓ "亩") ∷
   re 1 3 (ℓ "亭") ∷ []) Eq.refl

-- comm push TOFF034 sw1 L: 110 steps
lem-comm-push-TOFF034-sw1-L : WsL → ⟪ (ℓ "亡乊") ⟫ʷ ≈ ⟪ (ℓ "乊亡") ⟫ʷ
lem-comm-push-TOFF034-sw1-L c4 = derive (ℓ "亡乊") (ℓ "乊亡")
  (re 0 1 (ℓ "乥亝乥") ∷
   re 1 1 (ℓ "乊井乊") ∷
   re 2 1 (ℓ "乼云乼") ∷
   re 3 1 (ℓ "乥亍乥") ∷
   re 4 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw 5 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (ℓ "乥丳乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (ℓ "乥丳乥") ∷
   rw 6 (q1 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   re 8 1 (ℓ "乊丬乊") ∷
   rw 7 (q6 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   re 6 1 (ℓ "乼乎乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (ℓ "乼乏乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 10 1 (ℓ "乼丶乼") ∷
   rw 9 (q3 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (ℓ "乥乇乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥么乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 11 1 (ℓ "乥丯乥") ∷
   rw 10 (q1 c4) ∷
   rw⁻ 11 (q26 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   re 5 8 (ℓ "亍") ∷
   re 4 3 (ℓ "云") ∷
   re 3 3 (ℓ "井") ∷
   re 2 3 (ℓ "亝") ∷
   re 1 3 (ℓ "亡") ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = wlE 39 c4
  q38 : WsL → Eqn
  q38 c4 = eqn (ℓ "丫乪") (ℓ "乪丫") (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q39 : WsL → Eqn
  q39 c4 = eqn (ℓ "丫乩") (ℓ "乩丫") (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- comm push CCZ024 sw0 L: 46 steps
lem-comm-push-CCZ024-sw0-L : WsL → ⟪ (ℓ "亜丫") ⟫ʷ ≈ ⟪ (ℓ "丫亨") ⟫ʷ
lem-comm-push-CCZ024-sw0-L c4 = derive (ℓ "亜丫") (ℓ "丫亨")
  (re 0 1 (ℓ "乊五乊") ∷
   re 1 1 (ℓ "乼亐乼") ∷
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
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "丳") ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw 4 (q8 c4) ∷
   rw 5 (q6 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 1 (q37 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 3 1 (ℓ "乼乢乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (ℓ "乼乎乼") ∷
   rw 6 (q3 c4) ∷
   re 2 5 (ℓ "交") ∷
   re 1 3 (ℓ "亨") ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = wlE 40 c4
  q41 : WsL → Eqn
  q41 c4 = eqn (ℓ "丫丘") (ℓ "丘丫") (c₂ (Swap) (K))
  q42 : WsL → Eqn
  q42 c4 = eqn (ℓ "丘乼") (ℓ "乼丘") (c₃ (K ↑ ↑) (Swap))
  q43 : WsL → Eqn
  q43 c4 = wlE 41 c4

-- comm push TOFF204 sw0 L: 62 steps
lem-comm-push-TOFF204-sw0-L : WsL → ⟪ (ℓ "亞丫") ⟫ʷ ≈ ⟪ (ℓ "丫亪") ⟫ʷ
lem-comm-push-TOFF204-sw0-L c4 = derive (ℓ "亞丫") (ℓ "丫亪")
  (re 0 1 (ℓ "乊亖乊") ∷
   re 1 1 (ℓ "乼互乼") ∷
   re 2 1 (ℓ "乥于乥") ∷
   re 3 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q34 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q35 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (ℓ "乼乎乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 2 (q43 c4) ∷
   re 2 8 (ℓ "亦") ∷
   re 1 3 (ℓ "亪") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = wlE 18 c4
  q45 : WsL → Eqn
  q45 c4 = sE 2351 (lem-comm-push-CSd04-sw0-L c4)

-- resp CSd04 at 1: 2 steps
lem-resp-CSd04-at-1 : WsL → ⟪ (ℓ "举") ⟫ʷ ≈ ⟪ (ℓ "丫乖丫") ⟫ʷ
lem-resp-CSd04-at-1 c4 = derive (ℓ "举") (ℓ "丫乖丫")
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q45 c4) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = sE 2352 (lem-comm-push-CSd04-sw1-L c4)

-- resp CSd04 at 2: 4 steps
lem-resp-CSd04-at-2 : WsL → ⟪ (ℓ "举") ⟫ʷ ≈ ⟪ (ℓ "乊丫乖丫乊") ⟫ʷ
lem-resp-CSd04-at-2 c4 = derive (ℓ "举") (ℓ "乊丫乖丫乊")
  (rw⁻ 1 (q6 c4) ∷
   rw 0 (q46 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 1 (q45 c4) ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = sE 2354 (lem-comm-push-CX04-sw0-L c4)

-- resp CX04 at 1: 2 steps
lem-resp-CX04-at-1 : WsL → ⟪ (ℓ "乁") ⟫ʷ ≈ ⟪ (ℓ "丫乙丫") ⟫ʷ
lem-resp-CX04-at-1 c4 = derive (ℓ "乁") (ℓ "丫乙丫")
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = sE 2349 (lem-comm-push-CS04-sw2-L c4)
  q49 : WsL → Eqn
  q49 c4 = wlE 48 c4

-- comm push CCZ014 sw2 L: 47 steps
lem-comm-push-CCZ014-sw2-L : WsL → ⟪ (ℓ "五乥") ⟫ʷ ≈ ⟪ (ℓ "乥五") ⟫ʷ
lem-comm-push-CCZ014-sw2-L c4 = derive (ℓ "五乥") (ℓ "乥五")
  (re 0 1 (ℓ "乼亐乼") ∷
   re 1 1 (ℓ "乥二乥") ∷
   re 2 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乏") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "丶") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 0 3 (ℓ "乕") ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乖") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 (q3 c4) ∷
   rw 4 (q48 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q49 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q24 c4) ∷
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
   re 1 3 (ℓ "五") ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = sE 2355 (lem-comm-push-CX04-sw1-L c4)

-- resp CX04 at 2: 4 steps
lem-resp-CX04-at-2 : WsL → ⟪ (ℓ "乁") ⟫ʷ ≈ ⟪ (ℓ "乊丫乙丫乊") ⟫ʷ
lem-resp-CX04-at-2 c4 = derive (ℓ "乁") (ℓ "乊丫乙丫乊")
  (rw⁻ 1 (q6 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = sE 2356 (lem-comm-push-CZ04-sw0-L c4)

-- resp CZ04 at 1: 2 steps
lem-resp-CZ04-at-1 : WsL → ⟪ (ℓ "丿") ⟫ʷ ≈ ⟪ (ℓ "丫乗丫") ⟫ʷ
lem-resp-CZ04-at-1 c4 = derive (ℓ "丿") (ℓ "丫乗丫")
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

-- comm push TOFF024 sw0 L: 62 steps
lem-comm-push-TOFF024-sw0-L : WsL → ⟪ (ℓ "亝丫") ⟫ʷ ≈ ⟪ (ℓ "丫亩") ⟫ʷ
lem-comm-push-TOFF024-sw0-L c4 = derive (ℓ "亝丫") (ℓ "丫亩")
  (re 0 1 (ℓ "乊井乊") ∷
   re 1 1 (ℓ "乼云乼") ∷
   re 2 1 (ℓ "乥亍乥") ∷
   re 3 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (ℓ "乼乎乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 2 (q36 c4) ∷
   re 2 8 (ℓ "亥") ∷
   re 1 3 (ℓ "亩") ∷ []) Eq.refl

-- resp CS04 at 2: 4 steps
lem-resp-CS04-at-2 : WsL → ⟪ (ℓ "丽") ⟫ʷ ≈ ⟪ (ℓ "乊丫乕丫乊") ⟫ʷ
lem-resp-CS04-at-2 c4 = derive (ℓ "丽") (ℓ "乊丫乕丫乊")
  (rw⁻ 1 (q6 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

-- resp CS04 at 1: 2 steps
lem-resp-CS04-at-1 : WsL → ⟪ (ℓ "丽") ⟫ʷ ≈ ⟪ (ℓ "丫乕丫") ⟫ʷ
lem-resp-CS04-at-1 c4 = derive (ℓ "丽") (ℓ "丫乕丫")
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q20 c4) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = sE 2353 (lem-comm-push-CSd04-sw2-L c4)

-- resp CSd04 at 3: 6 steps
lem-resp-CSd04-at-3 : WsL → ⟪ (ℓ "举") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乖丫乊乥") ⟫ʷ
lem-resp-CSd04-at-3 c4 = derive (ℓ "举") (ℓ "乥乊丫乖丫乊乥")
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

-- resp CS04 at 3: 6 steps
lem-resp-CS04-at-3 : WsL → ⟪ (ℓ "丽") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乕丫乊乥") ⟫ʷ
lem-resp-CS04-at-3 c4 = derive (ℓ "丽") (ℓ "乥乊丫乕丫乊乥")
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 2 (q20 c4) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = wlE 64 c4
  q54 : WsL → Eqn
  q54 c4 = wlE 65 c4
  q55 : WsL → Eqn
  q55 c4 = eqn (ℓ "乥两") (ℓ "两乥") (c₄ (Swap ↑ ↑) (K))
  q56 : WsL → Eqn
  q56 c4 = wlE 66 c4
  q57 : WsL → Eqn
  q57 c4 = wlE 67 c4

-- comm push TOFF401 sw2 L: 62 steps
lem-comm-push-TOFF401-sw2-L : WsL → ⟪ (ℓ "亗乥") ⟫ʷ ≈ ⟪ (ℓ "乥亗") ⟫ʷ
lem-comm-push-TOFF401-sw2-L c4 = derive (ℓ "亗乥") (ℓ "乥亗")
  (re 0 1 (ℓ "乼亓乼") ∷
   re 1 1 (ℓ "乥亏乥") ∷
   re 2 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 1 (q53 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (ℓ "乕") ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乖") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q48 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q49 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q57 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   re 3 8 (ℓ "亏") ∷
   re 2 3 (ℓ "亓") ∷
   re 1 3 (ℓ "亗") ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (ℓ "乊两") (ℓ "两乊") (c₃ (Swap ↑) (K ↑))
  q59 : WsL → Eqn
  q59 c4 = eqn (ℓ "丫两") (ℓ "两丫") (c₂ (Swap) (K ↑ ↑))
  q60 : WsL → Eqn
  q60 c4 = wlE 68 c4

-- comm push TOFF402 sw0 L: 62 steps
lem-comm-push-TOFF402-sw0-L : WsL → ⟪ (ℓ "亟丫") ⟫ʷ ≈ ⟪ (ℓ "丫享") ⟫ʷ
lem-comm-push-TOFF402-sw0-L c4 = derive (ℓ "亟丫") (ℓ "丫享")
  (re 0 1 (ℓ "乊亗乊") ∷
   re 1 1 (ℓ "乼亓乼") ∷
   re 2 1 (ℓ "乥亏乥") ∷
   re 3 1 (ℓ "丘乇丬么丬丯丘一") ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q53 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw 0 (q58 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q8 c4) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (ℓ "乼乎乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 2 (q60 c4) ∷
   re 2 8 (ℓ "产") ∷
   re 1 3 (ℓ "享") ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (ℓ "乊丞") (ℓ "丞乊") (c₃ (Swap ↑) (K))
  q62 : WsL → Eqn
  q62 c4 = wlE 73 c4

-- comm push TOFF304 sw1 L: 110 steps
lem-comm-push-TOFF304-sw1-L : WsL → ⟪ (ℓ "亢乊") ⟫ʷ ≈ ⟪ (ℓ "乊亢") ⟫ʷ
lem-comm-push-TOFF304-sw1-L c4 = derive (ℓ "亢乊") (ℓ "乊亢")
  (re 0 1 (ℓ "乥亞乥") ∷
   re 1 1 (ℓ "乊亖乊") ∷
   re 2 1 (ℓ "乼互乼") ∷
   re 3 1 (ℓ "乥于乥") ∷
   re 4 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q40 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 5 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (ℓ "乥丳乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (ℓ "乥丳乥") ∷
   rw 6 (q1 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   re 8 1 (ℓ "乊丬乊") ∷
   rw 7 (q6 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (ℓ "乼乎乼") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (ℓ "乼乏乼") ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 10 1 (ℓ "乼丶乼") ∷
   rw 9 (q3 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (ℓ "乥乇乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥么乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 11 1 (ℓ "乥丯乥") ∷
   rw 10 (q1 c4) ∷
   rw⁻ 11 (q34 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   re 5 8 (ℓ "于") ∷
   re 4 3 (ℓ "互") ∷
   re 3 3 (ℓ "亖") ∷
   re 2 3 (ℓ "亞") ∷
   re 1 3 (ℓ "亢") ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (ℓ "丫丞") (ℓ "丞丫") (c₂ (Swap) (K ↑))

-- comm push TOFF304 sw0 L: 86 steps
lem-comm-push-TOFF304-sw0-L : WsL → ⟪ (ℓ "亢丫") ⟫ʷ ≈ ⟪ (ℓ "丫亮") ⟫ʷ
lem-comm-push-TOFF304-sw0-L c4 = derive (ℓ "亢丫") (ℓ "丫亮")
  (re 0 1 (ℓ "乥亞乥") ∷
   re 1 1 (ℓ "乊亖乊") ∷
   re 2 1 (ℓ "乼互乼") ∷
   re 3 1 (ℓ "乥于乥") ∷
   re 4 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q40 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "为") ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (ℓ "乥之乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (ℓ "乥之乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (ℓ "乼乣乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   re 9 1 (ℓ "乼乎乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw 3 (q43 c4) ∷
   re 3 8 (ℓ "亦") ∷
   re 2 3 (ℓ "亪") ∷
   re 1 3 (ℓ "亮") ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = wlE 47 c4
  q65 : WsL → Eqn
  q65 c4 = wlE 29 c4
  q66 : WsL → Eqn
  q66 c4 = wlE 1 c4
  q67 : WsL → Eqn
  q67 c4 = eqn (ℓ "丳乼") (ℓ "乼丳") (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))

-- comm push TOFF023 sw3 L: 76 steps
lem-comm-push-TOFF023-sw3-L : WsL → ⟪ (ℓ "亙乼") ⟫ʷ ≈ ⟪ (ℓ "乼亝") ⟫ʷ
lem-comm-push-TOFF023-sw3-L c4 = derive (ℓ "亙乼") (ℓ "乼亝")
  (re 0 1 (ℓ "乊云乊") ∷
   re 1 1 (ℓ "乥亍乥") ∷
   re 2 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (ℓ "乎") ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乏") ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "丶") ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q65 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q66 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw 2 (q67 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q6 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   re 4 8 (ℓ "亍") ∷
   re 3 3 (ℓ "云") ∷
   re 2 3 (ℓ "井") ∷
   re 1 3 (ℓ "亝") ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = wlE 46 c4
  q69 : WsL → Eqn
  q69 c4 = wlE 28 c4

-- comm push TOFF024 sw3 L: 76 steps
lem-comm-push-TOFF024-sw3-L : WsL → ⟪ (ℓ "亝乼") ⟫ʷ ≈ ⟪ (ℓ "乼亙") ⟫ʷ
lem-comm-push-TOFF024-sw3-L c4 = derive (ℓ "亝乼") (ℓ "乼亙")
  (re 0 1 (ℓ "乊井乊") ∷
   re 1 1 (ℓ "乼云乼") ∷
   re 2 1 (ℓ "乥亍乥") ∷
   re 3 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q28 c4) ∷
   re 5 1 (ℓ "乼丶乼") ∷
   rw 7 (q3 c4) ∷
   rw 4 (q67 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 5 (q3 c4) ∷
   rw 2 (q67 c4) ∷
   re 1 1 (ℓ "乼乢乼") ∷
   rw 3 (q3 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   re 3 8 (ℓ "亍") ∷
   re 2 3 (ℓ "云") ∷
   re 1 3 (ℓ "亙") ∷ []) Eq.refl
