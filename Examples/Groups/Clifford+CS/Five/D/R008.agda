{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR008 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R008 (Sᴰ : SR008) where

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
  lem-comm-push-CS04-sw1-R : WsL → St 2005
  lem-comm-push-CS04-sw1-R = pickᴰ 0 Sᴰ
  lem-comm-push-CS04-sw2-R : WsL → St 2350
  lem-comm-push-CS04-sw2-R = pickᴰ 1 Sᴰ
  lem-comm-push-BOX⟨0·21⟩-sw0-R : WsL → St 2385
  lem-comm-push-BOX⟨0·21⟩-sw0-R = pickᴰ 2 Sᴰ
  lem-comm-push-BOX⟨1·20⟩-sw1-R : WsL → St 2386
  lem-comm-push-BOX⟨1·20⟩-sw1-R = pickᴰ 3 Sᴰ
  lem-comm-push-BOX⟨1·230⟩-sw2-R : WsL → St 2387
  lem-comm-push-BOX⟨1·230⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-BOX⟨1·320⟩-sw3-R : WsL → St 2388
  lem-comm-push-BOX⟨1·320⟩-sw3-R = pickᴰ 5 Sᴰ
  lem-comm-push-BOX⟨1·420⟩-sw2-R : WsL → St 2389
  lem-comm-push-BOX⟨1·420⟩-sw2-R = pickᴰ 6 Sᴰ
  lem-comm-push-BOX⟨2·03⟩-sw2-R : WsL → St 2390
  lem-comm-push-BOX⟨2·03⟩-sw2-R = pickᴰ 7 Sᴰ
  lem-comm-push-BOX⟨4·03⟩-sw1-R : WsL → St 2391
  lem-comm-push-BOX⟨4·03⟩-sw1-R = pickᴰ 8 Sᴰ
  lem-comm-push-BOX⟨4·103⟩-sw1-R : WsL → St 2392
  lem-comm-push-BOX⟨4·103⟩-sw1-R = pickᴰ 9 Sᴰ
  lem-comm-push-BOX⟨4·10⟩-sw1-R : WsL → St 2393
  lem-comm-push-BOX⟨4·10⟩-sw1-R = pickᴰ 10 Sᴰ
  lem-comm-push-BOX⟨4·20⟩-sw0-R : WsL → St 2394
  lem-comm-push-BOX⟨4·20⟩-sw0-R = pickᴰ 11 Sᴰ
  lem-comm-push-CS04-sw0-R : WsL → St 2381
  lem-comm-push-CS04-sw0-R = pickᴰ 12 Sᴰ
  lem-comm-push-CS14-sw0-R : WsL → St 2008
  lem-comm-push-CS14-sw0-R = pickᴰ 13 Sᴰ
  lem-comm-push-CSd14-sw0-R : WsL → St 2382
  lem-comm-push-CSd14-sw0-R = pickᴰ 14 Sᴰ
  lem-comm-push-CX04-sw1-R : WsL → St 2383
  lem-comm-push-CX04-sw1-R = pickᴰ 15 Sᴰ
  lem-comm-push-CX04-sw2-R : WsL → St 2384
  lem-comm-push-CX04-sw2-R = pickᴰ 16 Sᴰ

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
  q9 c4 = eqn (ℓ "乥两") (ℓ "两乥") (c₄ (Swap ↑ ↑) (K))
  q10 : WsL → Eqn
  q10 c4 = wlE 17 c4
  q11 : WsL → Eqn
  q11 c4 = wlE 48 c4
  q12 : WsL → Eqn
  q12 c4 = sE 2350 (lem-comm-push-CS04-sw2-R c4)
  q13 : WsL → Eqn
  q13 c4 = wlE 66 c4
  q14 : WsL → Eqn
  q14 c4 = wlE 67 c4

-- comm push TOFF401 sw2 R: 62 steps
lem-comm-push-TOFF401-sw2-R : WsL → ⟪ (ℓ "乥亗") ⟫ʷ ≈ ⟪ (ℓ "亗乥") ⟫ʷ
lem-comm-push-TOFF401-sw2-R c4 = derive (ℓ "乥亗") (ℓ "亗乥")
  (re 1 1 (ℓ "乼亓乼") ∷
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
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 3 1 (ℓ "乼乎乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (ℓ "乼乏乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (ℓ "乼丶乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   re 4 1 (ℓ "乥乇乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (ℓ "乥么乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥丯乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (ℓ "亏") ∷
   re 1 3 (ℓ "亓") ∷
   re 0 3 (ℓ "亗") ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = wlE 5 c4
  q16 : WsL → Eqn
  q16 c4 = wlE 6 c4
  q17 : WsL → Eqn
  q17 c4 = wlE 7 c4
  q18 : WsL → Eqn
  q18 c4 = sE 2005 (lem-comm-push-CS04-sw1-R c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (ℓ "丫乩") (ℓ "乩丫") (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = wlE 117 c4
  q21 : WsL → Eqn
  q21 c4 = eqn (ℓ "丫乪") (ℓ "乪丫") (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q22 : WsL → Eqn
  q22 c4 = sE 2381 (lem-comm-push-CS04-sw0-R c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (ℓ "之乼") (ℓ "乼之") (c₃ (CX₀₁ ↑) (Swap))

-- comm push CCZ024 sw0 R: 46 steps
lem-comm-push-CCZ024-sw0-R : WsL → ⟪ (ℓ "丫亜") ⟫ʷ ≈ ⟪ (ℓ "亨丫") ⟫ʷ
lem-comm-push-CCZ024-sw0-R c4 = derive (ℓ "丫亜") (ℓ "亨丫")
  (re 1 1 (ℓ "乊五乊") ∷
   re 2 1 (ℓ "乼亐乼") ∷
   re 3 1 (ℓ "乥二乥") ∷
   re 4 1 (ℓ "乇丬么丬丯") ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乎") ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乏") ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "丶") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乖") ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   re 2 3 (ℓ "丳") ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw 5 (q18 c4) ∷
   rw 6 (q16 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   re 2 1 (ℓ "乼乢乼") ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   re 4 1 (ℓ "乼乣乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   re 6 1 (ℓ "乼乎乼") ∷
   rw 5 (q6 c4) ∷
   re 1 5 (ℓ "交") ∷
   re 0 3 (ℓ "亨") ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (ℓ "丌乥") (ℓ "乥丌") (c₁ (K) (Swap ↑))
  q25 : WsL → Eqn
  q25 c4 = eqn (ℓ "丌乼") (ℓ "乼丌") (c₁ (K) (Swap ↑ ↑))
  q26 : WsL → Eqn
  q26 c4 = eqn (ℓ "丌乊") (ℓ "乊丌") (c₁ (K) (Swap))
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "一乊") (ℓ "乊一") (c₁ (iI) (Swap))
  q28 : WsL → Eqn
  q28 c4 = wlE 109 c4
  q29 : WsL → Eqn
  q29 c4 = wlE 25 c4
  q30 : WsL → Eqn
  q30 c4 = eqn (ℓ "丒乼") (ℓ "乼丒") (c₂ (K ↑) (Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = wlE 27 c4

-- comm push TOFF024 sw0 R: 62 steps
lem-comm-push-TOFF024-sw0-R : WsL → ⟪ (ℓ "丫亝") ⟫ʷ ≈ ⟪ (ℓ "亩丫") ⟫ʷ
lem-comm-push-TOFF024-sw0-R c4 = derive (ℓ "丫亝") (ℓ "亩丫")
  (re 1 1 (ℓ "乊井乊") ∷
   re 2 1 (ℓ "乼云乼") ∷
   re 3 1 (ℓ "乥亍乥") ∷
   re 4 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q16 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   re 3 1 (ℓ "乼乢乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 7 1 (ℓ "乼乎乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 1 (q31 c4) ∷
   re 1 8 (ℓ "亥") ∷
   re 0 3 (ℓ "亩") ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (ℓ "丫两") (ℓ "两丫") (c₂ (Swap) (K ↑ ↑))
  q33 : WsL → Eqn
  q33 c4 = sE 2008 (lem-comm-push-CS14-sw0-R c4)
  q34 : WsL → Eqn
  q34 c4 = wlE 115 c4
  q35 : WsL → Eqn
  q35 c4 = sE 2382 (lem-comm-push-CSd14-sw0-R c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (ℓ "乄乼") (ℓ "乼乄") (c₂ (CX₁₀) (Swap ↑))
  q37 : WsL → Eqn
  q37 c4 = eqn (ℓ "乄乥") (ℓ "乥乄") (c₂ (CX₁₀) (Swap))
  q38 : WsL → Eqn
  q38 c4 = wlE 124 c4

-- comm push TOFF401 sw0 R: 63 steps
lem-comm-push-TOFF401-sw0-R : WsL → ⟪ (ℓ "丫亗") ⟫ʷ ≈ ⟪ (ℓ "亗丫") ⟫ʷ
lem-comm-push-TOFF401-sw0-R c4 = derive (ℓ "丫亗") (ℓ "亗丫")
  (re 1 1 (ℓ "乼亓乼") ∷
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
   rw 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q22 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 3 1 (ℓ "乼丶乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 5 1 (ℓ "乼丷乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 7 1 (ℓ "乼乎乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   re 4 1 (ℓ "乥丯乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   re 6 1 (ℓ "乥丰乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 8 (ℓ "亏") ∷
   re 1 3 (ℓ "亓") ∷
   re 0 3 (ℓ "亗") ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = wlE 122 c4
  q40 : WsL → Eqn
  q40 c4 = wlE 123 c4
  q41 : WsL → Eqn
  q41 c4 = sE 2392 (lem-comm-push-BOX⟨4·103⟩-sw1-R c4)

-- comm push BOX(1;4203) sw1 R: 8 steps
lem-comm-push-BOX⟨1·4203⟩-sw1-R : WsL → ⟪ (ℓ "乊伪") ⟫ʷ ≈ ⟪ (ℓ "佝乊") ⟫ʷ
lem-comm-push-BOX⟨1·4203⟩-sw1-R c4 = derive (ℓ "乊伪") (ℓ "佝乊")
  (re 1 1 (ℓ "亨亩伩亩亨伩") ∷
   rw⁻ 0 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 5 (q41 c4) ∷
   re 0 6 (ℓ "佝") ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = wlE 39 c4
  q43 : WsL → Eqn
  q43 c4 = wlE 13 c4
  q44 : WsL → Eqn
  q44 c4 = wlE 14 c4

-- comm push CCZ124 sw0 R: 46 steps
lem-comm-push-CCZ124-sw0-R : WsL → ⟪ (ℓ "丫亨") ⟫ʷ ≈ ⟪ (ℓ "亜丫") ⟫ʷ
lem-comm-push-CCZ124-sw0-R c4 = derive (ℓ "丫亨") (ℓ "亜丫")
  (re 1 1 (ℓ "乼交乼") ∷
   re 2 1 (ℓ "乢之乣之乎") ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "乕") ∷
   rw 6 (q6 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   re 3 1 (ℓ "乊丬乊") ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q16 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 3 1 (ℓ "乼乎乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (ℓ "乼乏乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (ℓ "乼丶乼") ∷
   rw 6 (q6 c4) ∷
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
   re 1 3 (ℓ "五") ∷
   re 0 3 (ℓ "亜") ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (ℓ "丘乼") (ℓ "乼丘") (c₃ (K ↑ ↑) (Swap))
  q46 : WsL → Eqn
  q46 c4 = eqn (ℓ "丂乼") (ℓ "乼丂") (c₂ (iI ↑) (Swap ↑))
  q47 : WsL → Eqn
  q47 c4 = eqn (ℓ "丫丘") (ℓ "丘丫") (c₂ (Swap) (K))
  q48 : WsL → Eqn
  q48 c4 = wlE 118 c4
  q49 : WsL → Eqn
  q49 c4 = wlE 73 c4
  q50 : WsL → Eqn
  q50 c4 = wlE 119 c4
  q51 : WsL → Eqn
  q51 c4 = eqn (ℓ "丒乥") (ℓ "乥丒") (c₂ (K ↑) (Swap))
  q52 : WsL → Eqn
  q52 c4 = eqn (ℓ "丂乥") (ℓ "乥丂") (c₂ (iI ↑) (Swap))
  q53 : WsL → Eqn
  q53 c4 = wlE 134 c4

-- comm push TOFF214 sw0 R: 62 steps
lem-comm-push-TOFF214-sw0-R : WsL → ⟪ (ℓ "丫亪") ⟫ʷ ≈ ⟪ (ℓ "亞丫") ⟫ʷ
lem-comm-push-TOFF214-sw0-R c4 = derive (ℓ "丫亪") (ℓ "亞丫")
  (re 1 1 (ℓ "乼亦乼") ∷
   re 2 1 (ℓ "丘乢之乣之乎丘丂") ∷
   rw⁻ 1 (q45 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw⁻ 3 (q23 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "乕") ∷
   rw⁻ 7 (q45 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q47 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 5 (q33 c4) ∷
   rw 6 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q49 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q16 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   re 3 8 (ℓ "于") ∷
   re 2 3 (ℓ "互") ∷
   re 1 3 (ℓ "亖") ∷
   re 0 3 (ℓ "亞") ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (ℓ "乊两") (ℓ "两乊") (c₃ (Swap ↑) (K ↑))
  q55 : WsL → Eqn
  q55 c4 = wlE 68 c4

-- comm push TOFF402 sw0 R: 62 steps
lem-comm-push-TOFF402-sw0-R : WsL → ⟪ (ℓ "丫亟") ⟫ʷ ≈ ⟪ (ℓ "享丫") ⟫ʷ
lem-comm-push-TOFF402-sw0-R c4 = derive (ℓ "丫亟") (ℓ "享丫")
  (re 1 1 (ℓ "乊亗乊") ∷
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
   rw 1 (q54 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q18 c4) ∷
   rw 7 (q54 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q16 c4) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q22 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 3 1 (ℓ "乼乢乼") ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 7 1 (ℓ "乼乎乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 1 (q55 c4) ∷
   re 1 8 (ℓ "产") ∷
   re 0 3 (ℓ "享") ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = wlE 135 c4
  q57 : WsL → Eqn
  q57 c4 = wlE 136 c4
  q58 : WsL → Eqn
  q58 c4 = sE 2385 (lem-comm-push-BOX⟨0·21⟩-sw0-R c4)

-- comm push BOX(2;031) sw0 R: 8 steps
lem-comm-push-BOX⟨2·031⟩-sw0-R : WsL → ⟪ (ℓ "丫仝") ⟫ʷ ≈ ⟪ (ℓ "众丫") ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw0-R c4 = derive (ℓ "丫仝") (ℓ "众丫")
  (re 1 1 (ℓ "亘亚仇亚亘仇") ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q58 c4) ∷
   re 0 6 (ℓ "众") ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = wlE 8 c4
  q60 : WsL → Eqn
  q60 c4 = wlE 9 c4
  q61 : WsL → Eqn
  q61 c4 = wlE 26 c4
  q62 : WsL → Eqn
  q62 c4 = eqn (ℓ "丫乹") (ℓ "乹丫") (c₂ (Swap) (CS ↑))
  q63 : WsL → Eqn
  q63 c4 = wlE 16 c4
  q64 : WsL → Eqn
  q64 c4 = eqn (ℓ "丫乺") (ℓ "乺丫") (c₂ (Swap) ((CS • CS • CS) ↑))
  q65 : WsL → Eqn
  q65 c4 = wlE 11 c4
  q66 : WsL → Eqn
  q66 c4 = wlE 12 c4
  q67 : WsL → Eqn
  q67 c4 = wlE 125 c4

-- comm push TOFF134 sw0 R: 86 steps
lem-comm-push-TOFF134-sw0-R : WsL → ⟪ (ℓ "丫亭") ⟫ʷ ≈ ⟪ (ℓ "亡丫") ⟫ʷ
lem-comm-push-TOFF134-sw0-R c4 = derive (ℓ "丫亭") (ℓ "亡丫")
  (re 1 1 (ℓ "乥亩乥") ∷
   re 2 1 (ℓ "乼亥乼") ∷
   re 3 1 (ℓ "丒乢之乣之乎丒丂") ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乩") ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 6 (q23 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (ℓ "乕") ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "乒") ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乒") ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 8 (q52 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q24 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   re 4 1 (ℓ "乥丳乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   re 6 1 (ℓ "乥丳乥") ∷
   rw 5 (q2 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q52 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (ℓ "乊丬乊") ∷
   rw 4 (q16 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (ℓ "乊丬乊") ∷
   rw 6 (q16 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw 9 (q50 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (ℓ "乼丶乼") ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (ℓ "乥丯乥") ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 4 8 (ℓ "亍") ∷
   re 3 3 (ℓ "云") ∷
   re 2 3 (ℓ "井") ∷
   re 1 3 (ℓ "亝") ∷
   re 0 3 (ℓ "亡") ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = wlE 137 c4
  q69 : WsL → Eqn
  q69 c4 = wlE 138 c4
  q70 : WsL → Eqn
  q70 c4 = sE 2386 (lem-comm-push-BOX⟨1·20⟩-sw1-R c4)

-- comm push BOX(2;130) sw1 R: 8 steps
lem-comm-push-BOX⟨2·130⟩-sw1-R : WsL → ⟪ (ℓ "乊众") ⟫ʷ ≈ ⟪ (ℓ "伔乊") ⟫ʷ
lem-comm-push-BOX⟨2·130⟩-sw1-R c4 = derive (ℓ "乊众") (ℓ "伔乊")
  (re 1 1 (ℓ "交亦伐亦交伐") ∷
   rw⁻ 0 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q70 c4) ∷
   re 0 6 (ℓ "伔") ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = sE 2387 (lem-comm-push-BOX⟨1·230⟩-sw2-R c4)

-- comm push BOX(2;1430) sw2 R: 12 steps
lem-comm-push-BOX⟨2·1430⟩-sw2-R : WsL → ⟪ (ℓ "乥伶") ⟫ʷ ≈ ⟪ (ℓ "佯乥") ⟫ʷ
lem-comm-push-BOX⟨2·1430⟩-sw2-R c4 = derive (ℓ "乥伶") (ℓ "佯乥")
  (re 1 1 (ℓ "亨亪伔亪亨伔") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "京") ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (ℓ "亮") ∷
   rw 2 (q71 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "亮") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw 5 (q71 c4) ∷
   re 0 6 (ℓ "佯") ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = wlE 141 c4
  q73 : WsL → Eqn
  q73 c4 = wlE 142 c4
  q74 : WsL → Eqn
  q74 c4 = sE 2388 (lem-comm-push-BOX⟨1·320⟩-sw3-R c4)

-- comm push BOX(3;1420) sw3 R: 8 steps
lem-comm-push-BOX⟨3·1420⟩-sw3-R : WsL → ⟪ (ℓ "乼佯") ⟫ʷ ≈ ⟪ (ℓ "侖乼") ⟫ʷ
lem-comm-push-BOX⟨3·1420⟩-sw3-R c4 = derive (ℓ "乼佯") (ℓ "侖乼")
  (re 1 1 (ℓ "京亮伞亮京伞") ∷
   rw⁻ 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   re 0 6 (ℓ "侖") ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (ℓ "丳乼") (ℓ "乼丳") (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q76 : WsL → Eqn
  q76 c4 = wlE 46 c4
  q77 : WsL → Eqn
  q77 c4 = wlE 28 c4
  q78 : WsL → Eqn
  q78 c4 = wlE 1 c4

-- comm push TOFF024 sw3 R: 76 steps
lem-comm-push-TOFF024-sw3-R : WsL → ⟪ (ℓ "乼亝") ⟫ʷ ≈ ⟪ (ℓ "亙乼") ⟫ʷ
lem-comm-push-TOFF024-sw3-R c4 = derive (ℓ "乼亝") (ℓ "亙乼")
  (re 1 1 (ℓ "乊井乊") ∷
   re 2 1 (ℓ "乼云乼") ∷
   re 3 1 (ℓ "乥亍乥") ∷
   re 4 1 (ℓ "丌乇丬么丬丯丌一") ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "乎") ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "乏") ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "丶") ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (ℓ "乖") ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (ℓ "丳") ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (ℓ "丳") ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q16 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   re 2 1 (ℓ "乼乢乼") ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   re 4 1 (ℓ "乼乣乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q75 c4) ∷
   re 6 1 (ℓ "乼丶乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q16 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   re 4 1 (ℓ "乥乇乥") ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (ℓ "乥么乥") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (ℓ "乥丯乥") ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (ℓ "亍") ∷
   re 1 3 (ℓ "云") ∷
   re 0 3 (ℓ "亙") ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = sE 2389 (lem-comm-push-BOX⟨1·420⟩-sw2-R c4)

-- comm push BOX(4;1320) sw2 R: 12 steps
lem-comm-push-BOX⟨4·1320⟩-sw2-R : WsL → ⟪ (ℓ "乥侖") ⟫ʷ ≈ ⟪ (ℓ "侔乥") ⟫ʷ
lem-comm-push-BOX⟨4·1320⟩-sw2-R c4 = derive (ℓ "乥侖") (ℓ "侔乥")
  (re 1 1 (ℓ "京亯伧亯京伧") ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q2 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q2 c4) ∷
   rw 2 (q79 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 3 (q2 c4) ∷
   re 5 1 (ℓ "乥亨乥") ∷
   rw 4 (q2 c4) ∷
   rw 5 (q79 c4) ∷
   re 0 6 (ℓ "侔") ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = wlE 44 c4
  q81 : WsL → Eqn
  q81 c4 = wlE 83 c4
  q82 : WsL → Eqn
  q82 c4 = sE 2393 (lem-comm-push-BOX⟨4·10⟩-sw1-R c4)

-- comm push BOX(1;430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·430⟩-sw1-R : WsL → ⟪ (ℓ "乊伬") ⟫ʷ ≈ ⟪ (ℓ "你乊") ⟫ʷ
lem-comm-push-BOX⟨1·430⟩-sw1-R c4 = derive (ℓ "乊伬") (ℓ "你乊")
  (re 1 1 (ℓ "京亭伦亭京伦") ∷
   rw⁻ 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q81 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   re 0 6 (ℓ "你") ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = wlE 120 c4

-- comm push TOFF412 sw0 R: 62 steps
lem-comm-push-TOFF412-sw0-R : WsL → ⟪ (ℓ "丫享") ⟫ʷ ≈ ⟪ (ℓ "亟丫") ⟫ʷ
lem-comm-push-TOFF412-sw0-R c4 = derive (ℓ "丫享") (ℓ "亟丫")
  (re 1 1 (ℓ "乼产乼") ∷
   re 2 1 (ℓ "丞乢之乣之乎丞丂") ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw⁻ 3 (q23 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "乕") ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 5 (q33 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (ℓ "乊丬乊") ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   re 6 1 (ℓ "乊丬乊") ∷
   rw 5 (q16 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   re 4 1 (ℓ "乼乎乼") ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (ℓ "乼乏乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (ℓ "乼丶乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (ℓ "乥乇乥") ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "乥么乥") ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (ℓ "乥丯乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   re 3 8 (ℓ "亏") ∷
   re 2 3 (ℓ "亓") ∷
   re 1 3 (ℓ "亗") ∷
   re 0 3 (ℓ "亟") ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (ℓ "丫亰") (ℓ "亰丫") (c₂ (Swap) (CCZ))
  q85 : WsL → Eqn
  q85 c4 = eqn (ℓ "丫亱") (ℓ "亱丫") (c₂ (Swap) (Toff))
  q86 : WsL → Eqn
  q86 c4 = sE 2394 (lem-comm-push-BOX⟨4·20⟩-sw0-R c4)

-- comm push BOX(2;430) sw0 R: 8 steps
lem-comm-push-BOX⟨2·430⟩-sw0-R : WsL → ⟪ (ℓ "丫你") ⟫ʷ ≈ ⟪ (ℓ "佣丫") ⟫ʷ
lem-comm-push-BOX⟨2·430⟩-sw0-R c4 = derive (ℓ "丫你") (ℓ "佣丫")
  (re 1 1 (ℓ "亰亱佚亱亰佚") ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   re 0 6 (ℓ "佣") ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = sE 2390 (lem-comm-push-BOX⟨2·03⟩-sw2-R c4)

-- comm push BOX(0;213) sw2 R: 12 steps
lem-comm-push-BOX⟨0·213⟩-sw2-R : WsL → ⟪ (ℓ "乥仉") ⟫ʷ ≈ ⟪ (ℓ "仡乥") ⟫ʷ
lem-comm-push-BOX⟨0·213⟩-sw2-R c4 = derive (ℓ "乥仉") (ℓ "仡乥")
  (re 1 1 (ℓ "二亍仈亍二仈") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "亐") ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (ℓ "云") ∷
   rw 2 (q87 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "云") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "亐") ∷
   rw 5 (q87 c4) ∷
   re 0 6 (ℓ "仡") ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = wlE 40 c4
  q89 : WsL → Eqn
  q89 c4 = wlE 129 c4
  q90 : WsL → Eqn
  q90 c4 = wlE 128 c4
  q91 : WsL → Eqn
  q91 c4 = sE 2384 (lem-comm-push-CX04-sw2-R c4)
  q92 : WsL → Eqn
  q92 c4 = sE 2383 (lem-comm-push-CX04-sw1-R c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (ℓ "丨乼") (ℓ "乼丨") (c₂ (CS) (Swap ↑))
  q94 : WsL → Eqn
  q94 c4 = eqn (ℓ "丨乥") (ℓ "乥丨") (c₂ (CS) (Swap))
  q95 : WsL → Eqn
  q95 c4 = wlE 149 c4

-- comm push TOFF304 sw3 R: 114 steps
lem-comm-push-TOFF304-sw3-R : WsL → ⟪ (ℓ "乼亢") ⟫ʷ ≈ ⟪ (ℓ "亣乼") ⟫ʷ
lem-comm-push-TOFF304-sw3-R c4 = derive (ℓ "乼亢") (ℓ "亣乼")
  (re 1 1 (ℓ "乥亞乥") ∷
   re 2 1 (ℓ "乊亖乊") ∷
   re 3 1 (ℓ "乼互乼") ∷
   re 4 1 (ℓ "乥于乥") ∷
   re 5 1 (ℓ "丒乇丬么丬丯丒一") ∷
   rw⁻ 4 (q51 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乎") ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "乏") ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   re 9 3 (ℓ "丶") ∷
   rw⁻ 10 (q51 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乕") ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (ℓ "乖") ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (ℓ "丳") ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   re 6 3 (ℓ "丳") ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q88 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "为") ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "为") ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (ℓ "乁") ∷
   rw⁻ 3 (q90 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (ℓ "乁") ∷
   re 6 1 (ℓ "乼丶乼") ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q91 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 5 (q91 c4) ∷
   re 7 1 (ℓ "乥丯乥") ∷
   rw 6 (q2 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 2 (q54 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw 6 (q92 c4) ∷
   re 8 1 (ℓ "乊丨乊") ∷
   rw 7 (q16 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   re 5 1 (ℓ "乼乎乼") ∷
   rw 4 (q6 c4) ∷
   re 6 1 (ℓ "乼为乼") ∷
   rw 5 (q6 c4) ∷
   re 7 1 (ℓ "乼乏乼") ∷
   rw 6 (q6 c4) ∷
   re 8 1 (ℓ "乼为乼") ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q93 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (ℓ "乥乇乥") ∷
   rw 5 (q2 c4) ∷
   re 7 1 (ℓ "乥丳乥") ∷
   rw 6 (q2 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 7 (q2 c4) ∷
   re 9 1 (ℓ "乥丳乥") ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q94 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   re 4 8 (ℓ "亏") ∷
   re 3 3 (ℓ "亓") ∷
   re 2 3 (ℓ "亗") ∷
   re 1 3 (ℓ "亟") ∷
   re 0 3 (ℓ "亣") ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = sE 2391 (lem-comm-push-BOX⟨4·03⟩-sw1-R c4)

-- comm push BOX(0;413) sw1 R: 12 steps
lem-comm-push-BOX⟨0·413⟩-sw1-R : WsL → ⟪ (ℓ "乊仾") ⟫ʷ ≈ ⟪ (ℓ "伆乊") ⟫ʷ
lem-comm-push-BOX⟨0·413⟩-sw1-R c4 = derive (ℓ "乊仾") (ℓ "伆乊")
  (re 1 1 (ℓ "五井份井五份") ∷
   rw⁻ 2 (q16 c4) ∷
   re 0 3 (ℓ "亜") ∷
   rw⁻ 3 (q16 c4) ∷
   re 1 3 (ℓ "亝") ∷
   rw 2 (q96 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (ℓ "亝") ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (ℓ "亜") ∷
   rw 5 (q96 c4) ∷
   re 0 6 (ℓ "伆") ∷ []) Eq.refl
