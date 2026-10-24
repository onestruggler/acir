{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)

module Examples.Groups.Clifford+CS.Five.D.R003 where

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

private
  q1 : WsL → Eqn
  q1 c4 = wlE 4 c4
  q2 : WsL → Eqn
  q2 c4 = wlE 3 c4
  q3 : WsL → Eqn
  q3 c4 = wlE 37 c4
  q4 : WsL → Eqn
  q4 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))
  q5 : WsL → Eqn
  q5 c4 = wlE 44 c4

-- comm CCZ123 CX04: 13 steps
lem-comm-CCZ123-CX04 : WsL → ⟪ (ℓ "交乁") ⟫ʷ ≈ ⟪ (ℓ "乁交") ⟫ʷ
lem-comm-CCZ123-CX04 c4 = derive (ℓ "交乁") (ℓ "乁交")
  (re 1 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亨") ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "京") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   re 5 1 (ℓ "乥亨乥") ∷
   rw 7 (q2 c4) ∷
   re 6 1 (ℓ "乼交乼") ∷
   rw 8 (q1 c4) ∷
   re 0 7 (ℓ "乁") ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))

-- comm CCZ134 CSd02: 23 steps
lem-comm-CCZ134-CSd02 : WsL → ⟪ (ℓ "京丰") ⟫ʷ ≈ ⟪ (ℓ "丰京") ⟫ʷ
lem-comm-CCZ134-CSd02 c4 = derive (ℓ "京丰") (ℓ "丰京")
  (re 0 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "丷") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "举") ∷
   re 3 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "亨") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q5 c4) ∷
   re 7 1 (ℓ "乥亨乥") ∷
   rw 9 (q2 c4) ∷
   re 8 1 (ℓ "乼交乼") ∷
   rw 10 (q1 c4) ∷
   re 2 7 (ℓ "举") ∷
   re 2 1 (ℓ "乼丷乼") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乥丰乥") ∷
   rw 0 (q2 c4) ∷
   re 1 5 (ℓ "京") ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (ℓ "个亰") (ℓ "亰个") (c₂ (CZ) (CCZ))

-- comm CZ02 CCZ134: 23 steps
lem-comm-CZ02-CCZ134 : WsL → ⟪ (ℓ "丱京") ⟫ʷ ≈ ⟪ (ℓ "京丱") ⟫ʷ
lem-comm-CZ02-CCZ134 c4 = derive (ℓ "丱京") (ℓ "京丱")
  (re 1 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "丸") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "丿") ∷
   re 2 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "亨") ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "京") ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 3 (q2 c4) ∷
   re 3 1 (ℓ "乼交乼") ∷
   rw 2 (q1 c4) ∷
   re 3 7 (ℓ "丿") ∷
   re 3 1 (ℓ "乼丸乼") ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乥丱乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "京") ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = wlE 13 c4
  q9 : WsL → Eqn
  q9 c4 = wlE 11 c4
  q10 : WsL → Eqn
  q10 c4 = eqn (ℓ "亏乹") (ℓ "乹亏") (c₃ (Toffᵗ) (CS))
  q11 : WsL → Eqn
  q11 c4 = wlE 8 c4
  q12 : WsL → Eqn
  q12 c4 = wlE 5 c4

-- comm CS14 TOFF302: 7 steps
lem-comm-CS14-TOFF302 : WsL → ⟪ (ℓ "乕些") ⟫ʷ ≈ ⟪ (ℓ "些乕") ⟫ʷ
lem-comm-CS14-TOFF302 c4 = derive (ℓ "乕些") (ℓ "些乕")
  (re 1 1 (ℓ "乊乥亏乥乊") ∷
   rw 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   re 0 5 (ℓ "些") ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = wlE 99 c4
  q14 : WsL → Eqn
  q14 c4 = wlE 6 c4
  q15 : WsL → Eqn
  q15 c4 = wlE 87 c4
  q16 : WsL → Eqn
  q16 c4 = wlE 18 c4
  q17 : WsL → Eqn
  q17 c4 = eqn (ℓ "丫亇") (ℓ "亇丫") (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : WsL → ⟪ (ℓ "亄") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亇丫乊乥") ⟫ʷ
lem-resp-CK41-at-3 c4 = derive (ℓ "亄") (ℓ "乥乊丫亇丫乊乥")
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = wlE 72 c4
  q19 : WsL → Eqn
  q19 c4 = eqn (ℓ "个乬") (ℓ "乬个") (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = wlE 93 c4

-- comm SWAP14 BOX(3;02): 7 steps
lem-comm-SWAP14-BOX⟨3·02⟩ : WsL → ⟪ (ℓ "乘仠") ⟫ʷ ≈ ⟪ (ℓ "仠乘") ⟫ʷ
lem-comm-SWAP14-BOX⟨3·02⟩ c4 = derive (ℓ "乘仠") (ℓ "仠乘")
  (re 1 1 (ℓ "丱") ∷
   re 1 1 (ℓ "乊个乊") ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   re 0 3 (ℓ "丱") ∷
   re 0 1 (ℓ "仠") ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = wlE 90 c4
  q22 : WsL → Eqn
  q22 c4 = eqn (ℓ "乊亊") (ℓ "亊乊") (c₃ (Swap ↑) (CK₁₀))
  q23 : WsL → Eqn
  q23 c4 = eqn (ℓ "丫亊") (ℓ "亊丫") (c₂ (Swap) (CK₁₀ ↑))

-- resp CK42 at 3: 6 steps
lem-resp-CK42-at-3 : WsL → ⟪ (ℓ "亇") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亊丫乊乥") ⟫ʷ
lem-resp-CK42-at-3 c4 = derive (ℓ "亇") (ℓ "乥乊丫亊丫乊乥")
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q21 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q23 c4) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = wlE 91 c4
  q25 : WsL → Eqn
  q25 c4 = eqn (ℓ "亏亊") (ℓ "亊亏") (c₃ (Toffᵗ) (CK₁₀))

-- comm TOFF301 CK42: 15 steps
lem-comm-TOFF301-CK42 : WsL → ⟪ (ℓ "亓亇") ⟫ʷ ≈ ⟪ (ℓ "亇亓") ⟫ʷ
lem-comm-TOFF301-CK42 c4 = derive (ℓ "亓亇") (ℓ "亇亓")
  (re 1 1 (ℓ "乼乷乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亗") ∷
   re 1 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亇") ∷
   rw⁻ 4 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (ℓ "乼乷乼") ∷
   rw 1 (q1 c4) ∷
   re 2 5 (ℓ "亗") ∷
   re 2 1 (ℓ "乼亓乼") ∷
   rw 4 (q1 c4) ∷
   re 0 3 (ℓ "亇") ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (ℓ "乄亰") (ℓ "亰乄") (c₂ (CX₁₀) (CCZ))

-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : WsL → ⟪ (ℓ "乜京") ⟫ʷ ≈ ⟪ (ℓ "京乜") ⟫ʷ
lem-comm-CX20-CCZ134 c4 = derive (ℓ "乜京") (ℓ "京乜")
  (re 1 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "买") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亀") ∷
   re 2 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "亨") ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "京") ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 3 (q2 c4) ∷
   re 3 1 (ℓ "乼交乼") ∷
   rw 2 (q1 c4) ∷
   re 3 7 (ℓ "亀") ∷
   re 3 1 (ℓ "乼买乼") ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乥乜乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "京") ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "丫乼") (ℓ "乼丫") (c₂ (Swap) (Swap ↑))
  q28 : WsL → Eqn
  q28 c4 = wlE 98 c4

-- comm push SWAP04 sw0 L: 5 steps
lem-comm-push-SWAP04-sw0-L : WsL → ⟪ (ℓ "乀丫") ⟫ʷ ≈ ⟪ (ℓ "丫乘") ⟫ʷ
lem-comm-push-SWAP04-sw0-L c4 = derive (ℓ "乀丫") (ℓ "丫乘")
  (re 0 1 (ℓ "乼丹乼") ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   re 1 3 (ℓ "乘") ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = wlE 2 c4
  q30 : WsL → Eqn
  q30 c4 = eqn (ℓ "乊乼") (ℓ "乼乊") (c₃ (Swap ↑) (Swap))
  q31 : WsL → Eqn
  q31 c4 = eqn (ℓ "丬乼") (ℓ "乼丬") (c₂ (CX₀₁) (Swap ↑))

-- comm push CX04 sw2 L: 7 steps
lem-comm-push-CX04-sw2-L : WsL → ⟪ (ℓ "乁乥") ⟫ʷ ≈ ⟪ (ℓ "乥乁") ⟫ʷ
lem-comm-push-CX04-sw2-L c4 = derive (ℓ "乁乥") (ℓ "乥乁")
  (re 0 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw 5 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q30 c4) ∷
   rw⁻ 0 (q29 c4) ∷
   re 1 7 (ℓ "乁") ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (ℓ "义乼") (ℓ "乼义") (c₃ (CZ ↑) (Swap))
  q33 : WsL → Eqn
  q33 c4 = wlE 36 c4
  q34 : WsL → Eqn
  q34 c4 = eqn (ℓ "丫乤") (ℓ "乤丫") (c₂ (Swap) (CZ))
  q35 : WsL → Eqn
  q35 c4 = wlE 33 c4

-- comm SWAP04 BOX(3;21): 13 steps
lem-comm-SWAP04-BOX⟨3·21⟩ : WsL → ⟪ (ℓ "乀伸") ⟫ʷ ≈ ⟪ (ℓ "伸乀") ⟫ʷ
lem-comm-SWAP04-BOX⟨3·21⟩ c4 = derive (ℓ "乀伸") (ℓ "伸乀")
  (re 1 1 (ℓ "义") ∷
   re 0 1 (ℓ "乼乥乊丫乊乥乼") ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "乐") ∷
   rw⁻ 4 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   re 2 1 (ℓ "乥义乥") ∷
   rw 1 (q2 c4) ∷
   rw⁻ 0 (q32 c4) ∷
   re 1 7 (ℓ "乀") ∷
   re 0 1 (ℓ "伸") ∷ []) Eq.refl

-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : WsL → ⟪ (ℓ "京乜") ⟫ʷ ≈ ⟪ (ℓ "乜京") ⟫ʷ
lem-comm-CCZ134-CX20 c4 = derive (ℓ "京乜") (ℓ "乜京")
  (re 0 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "买") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "亀") ∷
   re 3 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "亨") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw 6 (q5 c4) ∷
   re 7 1 (ℓ "乥亨乥") ∷
   rw 9 (q2 c4) ∷
   re 8 1 (ℓ "乼交乼") ∷
   rw 10 (q1 c4) ∷
   re 2 7 (ℓ "亀") ∷
   re 2 1 (ℓ "乼买乼") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乥乜乥") ∷
   rw 0 (q2 c4) ∷
   re 1 5 (ℓ "京") ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = wlE 85 c4
  q37 : WsL → Eqn
  q37 c4 = eqn (ℓ "久亳") (ℓ "亳久") (c₂ (CK₁₀) (Toffᵗ))
  q38 : WsL → Eqn
  q38 c4 = wlE 84 c4

-- comm TOFF312 CK40: 13 steps
lem-comm-TOFF312-CK40 : WsL → ⟪ (ℓ "产亁") ⟫ʷ ≈ ⟪ (ℓ "亁产") ⟫ʷ
lem-comm-TOFF312-CK40 c4 = derive (ℓ "产亁") (ℓ "亁产")
  (re 1 1 (ℓ "乼乥乊久乊乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "享") ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "亯") ∷
   rw⁻ 2 (q36 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   re 5 1 (ℓ "乥享乥") ∷
   rw 7 (q2 c4) ∷
   re 6 1 (ℓ "乼产乼") ∷
   rw 8 (q1 c4) ∷
   re 0 7 (ℓ "亁") ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = wlE 29 c4
  q40 : WsL → Eqn
  q40 c4 = wlE 9 c4
  q41 : WsL → Eqn
  q41 c4 = eqn (ℓ "二乺") (ℓ "乺二") (c₃ (CCZ) (CS • CS • CS))
  q42 : WsL → Eqn
  q42 c4 = wlE 12 c4
  q43 : WsL → Eqn
  q43 c4 = wlE 28 c4

-- comm CCZ034 CSd12: 15 steps
lem-comm-CCZ034-CSd12 : WsL → ⟪ (ℓ "亠么") ⟫ʷ ≈ ⟪ (ℓ "么亠") ⟫ʷ
lem-comm-CCZ034-CSd12 c4 = derive (ℓ "亠么") (ℓ "么亠")
  (re 0 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "乏") ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "乪") ∷
   rw⁻ 5 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 2 (q1 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   re 1 1 (ℓ "乥么乥") ∷
   rw 0 (q2 c4) ∷
   re 1 9 (ℓ "亠") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (ℓ "二乹") (ℓ "乹二") (c₃ (CCZ) (CS))

-- comm CCZ014 CS23: 9 steps
lem-comm-CCZ014-CS23 : WsL → ⟪ (ℓ "五乢") ⟫ʷ ≈ ⟪ (ℓ "乢五") ⟫ʷ
lem-comm-CCZ014-CS23 c4 = derive (ℓ "五乢") (ℓ "乢五")
  (re 0 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乩") ∷
   rw⁻ 3 (q11 c4) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 1 1 (ℓ "乼乢乼") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "五") ∷ []) Eq.refl

-- comm CCZ014 CSd23: 9 steps
lem-comm-CCZ014-CSd23 : WsL → ⟪ (ℓ "五乣") ⟫ʷ ≈ ⟪ (ℓ "乣五") ⟫ʷ
lem-comm-CCZ014-CSd23 c4 = derive (ℓ "五乣") (ℓ "乣五")
  (re 0 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw⁻ 3 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   re 1 1 (ℓ "乼乣乼") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "五") ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = wlE 38 c4
  q46 : WsL → Eqn
  q46 c4 = eqn (ℓ "丬亲") (ℓ "亲丬") (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q47 : WsL → Eqn
  q47 c4 = wlE 45 c4

-- comm TOFF314 CX02: 23 steps
lem-comm-TOFF314-CX02 : WsL → ⟪ (ℓ "亮丳") ⟫ʷ ≈ ⟪ (ℓ "丳亮") ⟫ʷ
lem-comm-TOFF314-CX02 c4 = derive (ℓ "亮丳") (ℓ "丳亮")
  (re 0 1 (ℓ "乥乼亦乼乥") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乁") ∷
   re 3 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "亪") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "亮") ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   re 7 1 (ℓ "乥亪乥") ∷
   rw 9 (q2 c4) ∷
   re 8 1 (ℓ "乼亦乼") ∷
   rw 10 (q1 c4) ∷
   re 2 7 (ℓ "乁") ∷
   re 2 1 (ℓ "乼为乼") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乥丳乥") ∷
   rw 0 (q2 c4) ∷
   re 1 5 (ℓ "亮") ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = wlE 100 c4

-- resp SWAP02 at 1: 2 steps
lem-resp-SWAP02-at-1 : WsL → ⟪ (ℓ "串") ⟫ʷ ≈ ⟪ (ℓ "丫乊丫") ⟫ʷ
lem-resp-SWAP02-at-1 c4 = derive (ℓ "串") (ℓ "丫乊丫")
  (rw⁻ 1 (q16 c4) ∷
   rw⁻ 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (ℓ "串乼") (ℓ "乼串") (c₃ (Swap ↑ • Swap • Swap ↑) (Swap))
  q50 : WsL → Eqn
  q50 c4 = wlE 86 c4

-- comm SWAP02 BOX(3;41): 11 steps
lem-comm-SWAP02-BOX⟨3·41⟩ : WsL → ⟪ (ℓ "串佼") ⟫ʷ ≈ ⟪ (ℓ "佼串") ⟫ʷ
lem-comm-SWAP02-BOX⟨3·41⟩ c4 = derive (ℓ "串佼") (ℓ "佼串")
  (re 1 1 (ℓ "乗") ∷
   re 1 1 (ℓ "乼乥义乥乼") ∷
   rw 0 (q49 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "丹") ∷
   rw⁻ 2 (q50 c4) ∷
   re 3 1 (ℓ "乥串乥") ∷
   rw 5 (q2 c4) ∷
   rw 4 (q49 c4) ∷
   re 0 5 (ℓ "乗") ∷
   re 0 1 (ℓ "佼") ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = wlE 57 c4
  q52 : WsL → Eqn
  q52 c4 = wlE 58 c4
  q53 : WsL → Eqn
  q53 c4 = eqn (ℓ "于争") (ℓ "争于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))
  q54 : WsL → Eqn
  q54 c4 = wlE 59 c4
  q55 : WsL → Eqn
  q55 c4 = wlE 60 c4

-- comm CX31 TOFF204: 11 steps
lem-comm-CX31-TOFF204 : WsL → ⟪ (ℓ "乳亞") ⟫ʷ ≈ ⟪ (ℓ "亞乳") ⟫ʷ
lem-comm-CX31-TOFF204 c4 = derive (ℓ "乳亞") (ℓ "亞乳")
  (re 1 1 (ℓ "乊乼乥于乥乼乊") ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "了") ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (ℓ "乼乶乼") ∷
   rw 7 (q1 c4) ∷
   rw 6 (q55 c4) ∷
   re 0 7 (ℓ "亞") ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = wlE 20 c4
  q57 : WsL → Eqn
  q57 c4 = eqn (ℓ "亏乽") (ℓ "乽亏") (c₃ (Toffᵗ) (CX₀₁))
  q58 : WsL → Eqn
  q58 c4 = wlE 21 c4

-- comm CX24 TOFF301: 5 steps
lem-comm-CX24-TOFF301 : WsL → ⟪ (ℓ "乭亓") ⟫ʷ ≈ ⟪ (ℓ "亓乭") ⟫ʷ
lem-comm-CX24-TOFF301 c4 = derive (ℓ "乭亓") (ℓ "亓乭")
  (re 1 1 (ℓ "乥亏乥") ∷
   rw 0 (q56 c4) ∷
   rw⁻ 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   re 0 3 (ℓ "亓") ∷ []) Eq.refl

-- comm CX21 TOFF304: 15 steps
lem-comm-CX21-TOFF304 : WsL → ⟪ (ℓ "也亢") ⟫ʷ ≈ ⟪ (ℓ "亢也") ⟫ʷ
lem-comm-CX21-TOFF304 c4 = derive (ℓ "也亢") (ℓ "亢也")
  (re 1 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "乳") ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "了") ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (ℓ "乼乶乼") ∷
   rw 8 (q1 c4) ∷
   rw 7 (q55 c4) ∷
   re 8 1 (ℓ "乥也乥") ∷
   rw 10 (q2 c4) ∷
   re 0 9 (ℓ "亢") ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (ℓ "乄亲") (ℓ "亲乄") (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI))

-- comm CX20 TOFF314: 23 steps
lem-comm-CX20-TOFF314 : WsL → ⟪ (ℓ "乜亮") ⟫ʷ ≈ ⟪ (ℓ "亮乜") ⟫ʷ
lem-comm-CX20-TOFF314 c4 = derive (ℓ "乜亮") (ℓ "亮乜")
  (re 1 1 (ℓ "乥乼亦乼乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "买") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亀") ∷
   re 2 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "亪") ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "亮") ∷
   rw 6 (q47 c4) ∷
   rw 5 (q59 c4) ∷
   rw 4 (q45 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 3 (q2 c4) ∷
   re 3 1 (ℓ "乼亦乼") ∷
   rw 2 (q1 c4) ∷
   re 3 7 (ℓ "亀") ∷
   re 3 1 (ℓ "乼买乼") ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乥乜乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "亮") ∷ []) Eq.refl

-- comm CK40 TOFF312: 13 steps
lem-comm-CK40-TOFF312 : WsL → ⟪ (ℓ "亁产") ⟫ʷ ≈ ⟪ (ℓ "产亁") ⟫ʷ
lem-comm-CK40-TOFF312 c4 = derive (ℓ "亁产") (ℓ "产亁")
  (re 0 1 (ℓ "乼乥乊久乊乥乼") ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "享") ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "亯") ∷
   rw 4 (q38 c4) ∷
   rw 3 (q37 c4) ∷
   rw 2 (q36 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q2 c4) ∷
   re 1 1 (ℓ "乼产乼") ∷
   rw 0 (q1 c4) ∷
   re 1 7 (ℓ "亁") ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = wlE 74 c4

-- comm SWAP13 BOX(2;04): 13 steps
lem-comm-SWAP13-BOX⟨2·04⟩ : WsL → ⟪ (ℓ "乑仍") ⟫ʷ ≈ ⟪ (ℓ "仍乑") ⟫ʷ
lem-comm-SWAP13-BOX⟨2·04⟩ c4 = derive (ℓ "乑仍") (ℓ "仍乑")
  (re 1 1 (ℓ "丿") ∷
   re 1 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乘") ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q60 c4) ∷
   re 6 1 (ℓ "乼乑乼") ∷
   rw 8 (q1 c4) ∷
   re 0 7 (ℓ "丿") ∷
   re 0 1 (ℓ "仍") ∷ []) Eq.refl

-- comm TOFF214 CX03: 9 steps
lem-comm-TOFF214-CX03 : WsL → ⟪ (ℓ "亪为") ⟫ʷ ≈ ⟪ (ℓ "为亪") ⟫ʷ
lem-comm-TOFF214-CX03 c4 = derive (ℓ "亪为") (ℓ "为亪")
  (re 1 1 (ℓ "乥乊丬乊乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "亮") ∷
   rw⁻ 1 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "为") ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (ℓ "亍争") (ℓ "争亍") (c₃ (Toff) (CX₁₀))

-- comm CX32 TOFF014: 9 steps
lem-comm-CX32-TOFF014 : WsL → ⟪ (ℓ "乶井") ⟫ʷ ≈ ⟪ (ℓ "井乶") ⟫ʷ
lem-comm-CX32-TOFF014 c4 = derive (ℓ "乶井") (ℓ "井乶")
  (re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "了") ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q54 c4) ∷
   re 4 1 (ℓ "乼乶乼") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "井") ∷ []) Eq.refl

-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : WsL → ⟪ (ℓ "亐乩") ⟫ʷ ≈ ⟪ (ℓ "乩亐") ⟫ʷ
lem-comm-CCZ013-CS24 c4 = derive (ℓ "亐乩") (ℓ "乩亐")
  (re 1 1 (ℓ "乼乢乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "五") ∷
   re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乩") ∷
   rw⁻ 4 (q11 c4) ∷
   rw 3 (q44 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 2 1 (ℓ "乼乢乼") ∷
   rw 1 (q1 c4) ∷
   re 2 5 (ℓ "五") ∷
   re 2 1 (ℓ "乼亐乼") ∷
   rw 4 (q1 c4) ∷
   re 0 3 (ℓ "乩") ∷ []) Eq.refl

-- comm CCZ013 CSd24: 15 steps
lem-comm-CCZ013-CSd24 : WsL → ⟪ (ℓ "亐乪") ⟫ʷ ≈ ⟪ (ℓ "乪亐") ⟫ʷ
lem-comm-CCZ013-CSd24 c4 = derive (ℓ "亐乪") (ℓ "乪亐")
  (re 1 1 (ℓ "乼乣乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "五") ∷
   re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q1 c4) ∷
   re 2 5 (ℓ "五") ∷
   re 2 1 (ℓ "乼亐乼") ∷
   rw 4 (q1 c4) ∷
   re 0 3 (ℓ "乪") ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = wlE 43 c4

-- comm push SBOXd(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (ℓ "促乊") ⟫ʷ ≈ ⟪ (ℓ "乊侺") ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L c4 = derive (ℓ "促乊") (ℓ "乊侺")
  (re 0 1 (ℓ "丷") ∷
   rw 0 (q62 c4) ∷
   re 1 1 (ℓ "侺") ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = wlE 1 c4

-- comm push SBOX(2;0;3;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L : WsL → ⟪ (ℓ "係乊") ⟫ʷ ≈ ⟪ (ℓ "乊侹") ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L c4 = derive (ℓ "係乊") (ℓ "乊侹")
  (re 0 1 (ℓ "丶") ∷
   rw 0 (q63 c4) ∷
   re 1 1 (ℓ "侹") ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = wlE 79 c4

-- comm push BOX(2;03) sw1 L: 3 steps
lem-comm-push-BOX⟨2·03⟩-sw1-L : WsL → ⟪ (ℓ "仈乊") ⟫ʷ ≈ ⟪ (ℓ "乊亵") ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw1-L c4 = derive (ℓ "仈乊") (ℓ "乊亵")
  (re 0 1 (ℓ "丸") ∷
   rw 0 (q64 c4) ∷
   re 1 1 (ℓ "亵") ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = wlE 42 c4

-- comm push SBOXd(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (ℓ "侺丫") ⟫ʷ ≈ ⟪ (ℓ "丫侦") ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L c4 = derive (ℓ "侺丫") (ℓ "丫侦")
  (re 0 1 (ℓ "丷") ∷
   rw 0 (q65 c4) ∷
   re 1 1 (ℓ "侦") ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = wlE 15 c4

-- comm push SBOX(1;0;3;2) sw0 L: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L : WsL → ⟪ (ℓ "侹丫") ⟫ʷ ≈ ⟪ (ℓ "丫侥") ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L c4 = derive (ℓ "侹丫") (ℓ "丫侥")
  (re 0 1 (ℓ "丶") ∷
   rw 0 (q66 c4) ∷
   re 1 1 (ℓ "侥") ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = wlE 49 c4

-- comm push BOX(1;03) sw0 L: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw0-L : WsL → ⟪ (ℓ "亵丫") ⟫ʷ ≈ ⟪ (ℓ "丫人") ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw0-L c4 = derive (ℓ "亵丫") (ℓ "丫人")
  (re 0 1 (ℓ "丸") ∷
   rw 0 (q67 c4) ∷
   re 1 1 (ℓ "人") ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = wlE 105 c4

-- comm push CSd14 sw0 L: 5 steps
lem-comm-push-CSd14-sw0-L : WsL → ⟪ (ℓ "乖丫") ⟫ʷ ≈ ⟪ (ℓ "丫举") ⟫ʷ
lem-comm-push-CSd14-sw0-L c4 = derive (ℓ "乖丫") (ℓ "丫举")
  (re 0 1 (ℓ "乼乏乼") ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q68 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   re 1 3 (ℓ "举") ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = wlE 106 c4

-- comm push CS14 sw0 L: 5 steps
lem-comm-push-CS14-sw0-L : WsL → ⟪ (ℓ "乕丫") ⟫ʷ ≈ ⟪ (ℓ "丫丽") ⟫ʷ
lem-comm-push-CS14-sw0-L c4 = derive (ℓ "乕丫") (ℓ "丫丽")
  (re 0 1 (ℓ "乼乎乼") ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   re 1 3 (ℓ "丽") ∷ []) Eq.refl

-- comm push SBOXd(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (ℓ "侦乥") ⟫ʷ ≈ ⟪ (ℓ "乥侨") ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L c4 = derive (ℓ "侦乥") (ℓ "乥侨")
  (re 0 1 (ℓ "乏") ∷
   re 0 1 (ℓ "乥么乥") ∷
   rw 2 (q2 c4) ∷
   re 1 1 (ℓ "侨") ∷ []) Eq.refl

-- comm push SBOX(0;1;3;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L : WsL → ⟪ (ℓ "侥乥") ⟫ʷ ≈ ⟪ (ℓ "乥侤") ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L c4 = derive (ℓ "侥乥") (ℓ "乥侤")
  (re 0 1 (ℓ "乎") ∷
   re 0 1 (ℓ "乥乇乥") ∷
   rw 2 (q2 c4) ∷
   re 1 1 (ℓ "侤") ∷ []) Eq.refl

-- comm push BOX(0;13) sw2 L: 4 steps
lem-comm-push-BOX⟨0·13⟩-sw2-L : WsL → ⟪ (ℓ "人乥") ⟫ʷ ≈ ⟪ (ℓ "乥亴") ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw2-L c4 = derive (ℓ "人乥") (ℓ "乥亴")
  (re 0 1 (ℓ "乐") ∷
   re 0 1 (ℓ "乥义乥") ∷
   rw 2 (q2 c4) ∷
   re 1 1 (ℓ "亴") ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = wlE 112 c4

-- comm push SBOXd(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (ℓ "侨乊") ⟫ʷ ≈ ⟪ (ℓ "乊侫") ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L c4 = derive (ℓ "侨乊") (ℓ "乊侫")
  (re 0 1 (ℓ "么") ∷
   rw 0 (q70 c4) ∷
   re 1 1 (ℓ "侫") ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = wlE 113 c4

-- comm push SBOX(0;1;2;3) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L : WsL → ⟪ (ℓ "侤乊") ⟫ʷ ≈ ⟪ (ℓ "乊侪") ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L c4 = derive (ℓ "侤乊") (ℓ "乊侪")
  (re 0 1 (ℓ "乇") ∷
   rw 0 (q71 c4) ∷
   re 1 1 (ℓ "侪") ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = wlE 114 c4

-- comm push BOX(0;12) sw1 L: 3 steps
lem-comm-push-BOX⟨0·12⟩-sw1-L : WsL → ⟪ (ℓ "亴乊") ⟫ʷ ≈ ⟪ (ℓ "乊仇") ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw1-L c4 = derive (ℓ "亴乊") (ℓ "乊仇")
  (re 0 1 (ℓ "义") ∷
   rw 0 (q72 c4) ∷
   re 1 1 (ℓ "仇") ∷ []) Eq.refl

-- comm push BOX(0;21) sw1 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw1-R : WsL → ⟪ (ℓ "乊仇") ⟫ʷ ≈ ⟪ (ℓ "亴乊") ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw1-R c4 = derive (ℓ "乊仇") (ℓ "亴乊")
  (re 1 1 (ℓ "义") ∷
   rw⁻ 0 (q72 c4) ∷
   re 0 1 (ℓ "亴") ∷ []) Eq.refl

-- comm push SBOX(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (ℓ "乊侪") ⟫ʷ ≈ ⟪ (ℓ "侤乊") ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R c4 = derive (ℓ "乊侪") (ℓ "侤乊")
  (re 1 1 (ℓ "乇") ∷
   rw⁻ 0 (q71 c4) ∷
   re 0 1 (ℓ "侤") ∷ []) Eq.refl

-- comm push SBOXd(0;2;1;3) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R : WsL → ⟪ (ℓ "乊侫") ⟫ʷ ≈ ⟪ (ℓ "侨乊") ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R c4 = derive (ℓ "乊侫") (ℓ "侨乊")
  (re 1 1 (ℓ "么") ∷
   rw⁻ 0 (q70 c4) ∷
   re 0 1 (ℓ "侨") ∷ []) Eq.refl

-- comm push BOX(0;12) sw2 R: 4 steps
lem-comm-push-BOX⟨0·12⟩-sw2-R : WsL → ⟪ (ℓ "乥亴") ⟫ʷ ≈ ⟪ (ℓ "人乥") ⟫ʷ
lem-comm-push-BOX⟨0·12⟩-sw2-R c4 = derive (ℓ "乥亴") (ℓ "人乥")
  (re 1 1 (ℓ "义") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "乐") ∷
   re 0 1 (ℓ "人") ∷ []) Eq.refl

-- comm push SBOX(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (ℓ "乥侤") ⟫ʷ ≈ ⟪ (ℓ "侥乥") ⟫ʷ
lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R c4 = derive (ℓ "乥侤") (ℓ "侥乥")
  (re 1 1 (ℓ "乇") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "乎") ∷
   re 0 1 (ℓ "侥") ∷ []) Eq.refl

-- comm push SBOXd(0;1;2;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R : WsL → ⟪ (ℓ "乥侨") ⟫ʷ ≈ ⟪ (ℓ "侦乥") ⟫ʷ
lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R c4 = derive (ℓ "乥侨") (ℓ "侦乥")
  (re 1 1 (ℓ "么") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "乏") ∷
   re 0 1 (ℓ "侦") ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = wlE 81 c4

-- comm push CK41 sw0 R: 5 steps
lem-comm-push-CK41-sw0-R : WsL → ⟪ (ℓ "丫亄") ⟫ʷ ≈ ⟪ (ℓ "亁丫") ⟫ʷ
lem-comm-push-CK41-sw0-R c4 = derive (ℓ "丫亄") (ℓ "亁丫")
  (re 1 1 (ℓ "乼乴乼") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (ℓ "亁") ∷ []) Eq.refl

-- comm push CS14 sw0 R: 5 steps
lem-comm-push-CS14-sw0-R : WsL → ⟪ (ℓ "丫乕") ⟫ʷ ≈ ⟪ (ℓ "丽丫") ⟫ʷ
lem-comm-push-CS14-sw0-R c4 = derive (ℓ "丫乕") (ℓ "丽丫")
  (re 1 1 (ℓ "乼乎乼") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (ℓ "丽") ∷ []) Eq.refl

-- comm push CSd14 sw0 R: 5 steps
lem-comm-push-CSd14-sw0-R : WsL → ⟪ (ℓ "丫乖") ⟫ʷ ≈ ⟪ (ℓ "举丫") ⟫ʷ
lem-comm-push-CSd14-sw0-R c4 = derive (ℓ "丫乖") (ℓ "举丫")
  (re 1 1 (ℓ "乼乏乼") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (ℓ "举") ∷ []) Eq.refl

-- comm push CS04 sw0 R: 5 steps
lem-comm-push-CS04-sw0-R : WsL → ⟪ (ℓ "丫丽") ⟫ʷ ≈ ⟪ (ℓ "乕丫") ⟫ʷ
lem-comm-push-CS04-sw0-R c4 = derive (ℓ "丫丽") (ℓ "乕丫")
  (re 1 1 (ℓ "乼丶乼") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw 2 (q27 c4) ∷
   re 0 3 (ℓ "乕") ∷ []) Eq.refl

-- comm push BOX(0;13) sw0 R: 3 steps
lem-comm-push-BOX⟨0·13⟩-sw0-R : WsL → ⟪ (ℓ "丫人") ⟫ʷ ≈ ⟪ (ℓ "亵丫") ⟫ʷ
lem-comm-push-BOX⟨0·13⟩-sw0-R c4 = derive (ℓ "丫人") (ℓ "亵丫")
  (re 1 1 (ℓ "乐") ∷
   rw⁻ 0 (q67 c4) ∷
   re 0 1 (ℓ "亵") ∷ []) Eq.refl

-- comm push SBOX(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (ℓ "丫侥") ⟫ʷ ≈ ⟪ (ℓ "侹丫") ⟫ʷ
lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R c4 = derive (ℓ "丫侥") (ℓ "侹丫")
  (re 1 1 (ℓ "乎") ∷
   rw⁻ 0 (q66 c4) ∷
   re 0 1 (ℓ "侹") ∷ []) Eq.refl

-- comm push SBOXd(0;1;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R : WsL → ⟪ (ℓ "丫侦") ⟫ʷ ≈ ⟪ (ℓ "侺丫") ⟫ʷ
lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R c4 = derive (ℓ "丫侦") (ℓ "侺丫")
  (re 1 1 (ℓ "乏") ∷
   rw⁻ 0 (q65 c4) ∷
   re 0 1 (ℓ "侺") ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = wlE 88 c4

-- comm push CK40 sw1 R: 5 steps
lem-comm-push-CK40-sw1-R : WsL → ⟪ (ℓ "乊亁") ⟫ʷ ≈ ⟪ (ℓ "亁乊") ⟫ʷ
lem-comm-push-CK40-sw1-R c4 = derive (ℓ "乊亁") (ℓ "亁乊")
  (re 1 1 (ℓ "乼乱乼") ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (ℓ "亁") ∷ []) Eq.refl

-- comm push BOX(1;03) sw1 R: 3 steps
lem-comm-push-BOX⟨1·03⟩-sw1-R : WsL → ⟪ (ℓ "乊亵") ⟫ʷ ≈ ⟪ (ℓ "仈乊") ⟫ʷ
lem-comm-push-BOX⟨1·03⟩-sw1-R c4 = derive (ℓ "乊亵") (ℓ "仈乊")
  (re 1 1 (ℓ "丸") ∷
   rw⁻ 0 (q64 c4) ∷
   re 0 1 (ℓ "仈") ∷ []) Eq.refl

-- comm push SBOX(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (ℓ "乊侹") ⟫ʷ ≈ ⟪ (ℓ "係乊") ⟫ʷ
lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R c4 = derive (ℓ "乊侹") (ℓ "係乊")
  (re 1 1 (ℓ "丶") ∷
   rw⁻ 0 (q63 c4) ∷
   re 0 1 (ℓ "係") ∷ []) Eq.refl

-- comm push SBOXd(1;0;3;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R : WsL → ⟪ (ℓ "乊侺") ⟫ʷ ≈ ⟪ (ℓ "促乊") ⟫ʷ
lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R c4 = derive (ℓ "乊侺") (ℓ "促乊")
  (re 1 1 (ℓ "丷") ∷
   rw⁻ 0 (q62 c4) ∷
   re 0 1 (ℓ "促") ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (ℓ "二争") (ℓ "争二") (c₃ (CCZ) (CX₁₀))

-- comm CCZ014 CX32: 9 steps
lem-comm-CCZ014-CX32 : WsL → ⟪ (ℓ "五乶") ⟫ʷ ≈ ⟪ (ℓ "乶五") ⟫ʷ
lem-comm-CCZ014-CX32 c4 = derive (ℓ "五乶") (ℓ "乶五")
  (re 0 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "了") ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q75 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   re 1 1 (ℓ "乼乶乼") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "五") ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = eqn (ℓ "乊佒") (ℓ "佒乊") (c₃ (Swap ↑) (CZ))

-- comm push BOX(4;203) sw1 L: 12 steps
lem-comm-push-BOX⟨4·203⟩-sw1-L : WsL → ⟪ (ℓ "作乊") ⟫ʷ ≈ ⟪ (ℓ "乊伩") ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw1-L c4 = derive (ℓ "作乊") (ℓ "乊伩")
  (re 0 1 (ℓ "亜亟佒亟亜佒") ∷
   rw⁻ 5 (q76 c4) ∷
   re 4 1 (ℓ "乊五乊") ∷
   rw 6 (q14 c4) ∷
   re 3 1 (ℓ "乊亗乊") ∷
   rw 5 (q14 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   re 1 1 (ℓ "乊亗乊") ∷
   rw 3 (q14 c4) ∷
   re 0 1 (ℓ "乊五乊") ∷
   rw 2 (q14 c4) ∷
   re 1 6 (ℓ "伩") ∷ []) Eq.refl

-- comm push SBOXd(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (ℓ "侳乥") ⟫ʷ ≈ ⟪ (ℓ "乥侵") ⟫ʷ
lem-comm-push-SBOXd⟨0·4·3·1⟩-sw2-L c4 = derive (ℓ "侳乥") (ℓ "乥侵")
  (re 0 1 (ℓ "乺") ∷
   rw 0 (q40 c4) ∷
   re 1 1 (ℓ "侵") ∷ []) Eq.refl

-- comm push SBOX(0;4;3;1) sw2 L: 3 steps
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L : WsL → ⟪ (ℓ "侲乥") ⟫ʷ ≈ ⟪ (ℓ "乥侱") ⟫ʷ
lem-comm-push-SBOX⟨0·4·3·1⟩-sw2-L c4 = derive (ℓ "侲乥") (ℓ "乥侱")
  (re 0 1 (ℓ "乹") ∷
   rw 0 (q11 c4) ∷
   re 1 1 (ℓ "侱") ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = wlE 35 c4

-- comm push BOX(0;43) sw2 L: 3 steps
lem-comm-push-BOX⟨0·43⟩-sw2-L : WsL → ⟪ (ℓ "仺乥") ⟫ʷ ≈ ⟪ (ℓ "乥仿") ⟫ʷ
lem-comm-push-BOX⟨0·43⟩-sw2-L c4 = derive (ℓ "仺乥") (ℓ "乥仿")
  (re 0 1 (ℓ "乻") ∷
   rw 0 (q77 c4) ∷
   re 1 1 (ℓ "仿") ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = wlE 7 c4

-- comm push SBOXd(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (ℓ "侵乊") ⟫ʷ ≈ ⟪ (ℓ "乊侷") ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L c4 = derive (ℓ "侵乊") (ℓ "乊侷")
  (re 0 1 (ℓ "乪") ∷
   rw 0 (q78 c4) ∷
   re 1 1 (ℓ "侷") ∷ []) Eq.refl

-- comm push SBOX(0;4;2;1) sw1 L: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L : WsL → ⟪ (ℓ "侱乊") ⟫ʷ ≈ ⟪ (ℓ "乊侰") ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L c4 = derive (ℓ "侱乊") (ℓ "乊侰")
  (re 0 1 (ℓ "乩") ∷
   rw 0 (q12 c4) ∷
   re 1 1 (ℓ "侰") ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = wlE 53 c4

-- comm push BOX(0;42) sw1 L: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw1-L : WsL → ⟪ (ℓ "仿乊") ⟫ʷ ≈ ⟪ (ℓ "乊价") ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw1-L c4 = derive (ℓ "仿乊") (ℓ "乊价")
  (re 0 1 (ℓ "乫") ∷
   rw 0 (q79 c4) ∷
   re 1 1 (ℓ "价") ∷ []) Eq.refl

-- comm push SBOXd(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (ℓ "侷乼") ⟫ʷ ≈ ⟪ (ℓ "乼侮") ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw3-L c4 = derive (ℓ "侷乼") (ℓ "乼侮")
  (re 0 1 (ℓ "乖") ∷
   re 0 1 (ℓ "乼乏乼") ∷
   rw 2 (q1 c4) ∷
   re 1 1 (ℓ "侮") ∷ []) Eq.refl

-- comm push SBOX(0;4;1;2) sw3 L: 4 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L : WsL → ⟪ (ℓ "侰乼") ⟫ʷ ≈ ⟪ (ℓ "乼侭") ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw3-L c4 = derive (ℓ "侰乼") (ℓ "乼侭")
  (re 0 1 (ℓ "乕") ∷
   re 0 1 (ℓ "乼乎乼") ∷
   rw 2 (q1 c4) ∷
   re 1 1 (ℓ "侭") ∷ []) Eq.refl

-- comm push BOX(0;41) sw3 L: 4 steps
lem-comm-push-BOX⟨0·41⟩-sw3-L : WsL → ⟪ (ℓ "价乼") ⟫ʷ ≈ ⟪ (ℓ "乼仟") ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw3-L c4 = derive (ℓ "价乼") (ℓ "乼仟")
  (re 0 1 (ℓ "乗") ∷
   re 0 1 (ℓ "乼乐乼") ∷
   rw 2 (q1 c4) ∷
   re 1 1 (ℓ "仟") ∷ []) Eq.refl

-- comm push CX04 sw2 R: 7 steps
lem-comm-push-CX04-sw2-R : WsL → ⟪ (ℓ "乥乁") ⟫ʷ ≈ ⟪ (ℓ "乁乥") ⟫ʷ
lem-comm-push-CX04-sw2-R c4 = derive (ℓ "乥乁") (ℓ "乁乥")
  (re 1 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw 0 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   re 0 7 (ℓ "乁") ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = wlE 10 c4

-- comm push CX04 sw1 R: 5 steps
lem-comm-push-CX04-sw1-R : WsL → ⟪ (ℓ "乊乁") ⟫ʷ ≈ ⟪ (ℓ "乁乊") ⟫ʷ
lem-comm-push-CX04-sw1-R c4 = derive (ℓ "乊乁") (ℓ "乁乊")
  (re 1 1 (ℓ "乼为乼") ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q80 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (ℓ "乁") ∷ []) Eq.refl

-- comm push SBOXd(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (ℓ "侮乥") ⟫ʷ ≈ ⟪ (ℓ "乥侫") ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L c4 = derive (ℓ "侮乥") (ℓ "乥侫")
  (re 0 1 (ℓ "乏") ∷
   re 0 1 (ℓ "乥么乥") ∷
   rw 2 (q2 c4) ∷
   re 1 1 (ℓ "侫") ∷ []) Eq.refl

-- comm push SBOX(0;3;1;2) sw2 L: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L : WsL → ⟪ (ℓ "侭乥") ⟫ʷ ≈ ⟪ (ℓ "乥侪") ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L c4 = derive (ℓ "侭乥") (ℓ "乥侪")
  (re 0 1 (ℓ "乎") ∷
   re 0 1 (ℓ "乥乇乥") ∷
   rw 2 (q2 c4) ∷
   re 1 1 (ℓ "侪") ∷ []) Eq.refl

-- comm push BOX(0;31) sw2 L: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw2-L : WsL → ⟪ (ℓ "仟乥") ⟫ʷ ≈ ⟪ (ℓ "乥仇") ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw2-L c4 = derive (ℓ "仟乥") (ℓ "乥仇")
  (re 0 1 (ℓ "乐") ∷
   re 0 1 (ℓ "乥义乥") ∷
   rw 2 (q2 c4) ∷
   re 1 1 (ℓ "仇") ∷ []) Eq.refl

-- comm push BOX(0;21) sw2 R: 4 steps
lem-comm-push-BOX⟨0·21⟩-sw2-R : WsL → ⟪ (ℓ "乥仇") ⟫ʷ ≈ ⟪ (ℓ "仟乥") ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw2-R c4 = derive (ℓ "乥仇") (ℓ "仟乥")
  (re 1 1 (ℓ "义") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "乐") ∷
   re 0 1 (ℓ "仟") ∷ []) Eq.refl

-- comm push SBOX(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (ℓ "乥侪") ⟫ʷ ≈ ⟪ (ℓ "侭乥") ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R c4 = derive (ℓ "乥侪") (ℓ "侭乥")
  (re 1 1 (ℓ "乇") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "乎") ∷
   re 0 1 (ℓ "侭") ∷ []) Eq.refl

-- comm push SBOXd(0;2;1;3) sw2 R: 4 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R : WsL → ⟪ (ℓ "乥侫") ⟫ʷ ≈ ⟪ (ℓ "侮乥") ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R c4 = derive (ℓ "乥侫") (ℓ "侮乥")
  (re 1 1 (ℓ "么") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "乏") ∷
   re 0 1 (ℓ "侮") ∷ []) Eq.refl

-- comm push BOX(0;31) sw3 R: 4 steps
lem-comm-push-BOX⟨0·31⟩-sw3-R : WsL → ⟪ (ℓ "乼仟") ⟫ʷ ≈ ⟪ (ℓ "价乼") ⟫ʷ
lem-comm-push-BOX⟨0·31⟩-sw3-R c4 = derive (ℓ "乼仟") (ℓ "价乼")
  (re 1 1 (ℓ "乐") ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (ℓ "乗") ∷
   re 0 1 (ℓ "价") ∷ []) Eq.refl

-- comm push SBOX(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (ℓ "乼侭") ⟫ʷ ≈ ⟪ (ℓ "侰乼") ⟫ʷ
lem-comm-push-SBOX⟨0·3·1·2⟩-sw3-R c4 = derive (ℓ "乼侭") (ℓ "侰乼")
  (re 1 1 (ℓ "乎") ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (ℓ "乕") ∷
   re 0 1 (ℓ "侰") ∷ []) Eq.refl

-- comm push SBOXd(0;3;1;2) sw3 R: 4 steps
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R : WsL → ⟪ (ℓ "乼侮") ⟫ʷ ≈ ⟪ (ℓ "侷乼") ⟫ʷ
lem-comm-push-SBOXd⟨0·3·1·2⟩-sw3-R c4 = derive (ℓ "乼侮") (ℓ "侷乼")
  (re 1 1 (ℓ "乏") ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (ℓ "乖") ∷
   re 0 1 (ℓ "侷") ∷ []) Eq.refl

-- comm push BOX(0;41) sw1 R: 3 steps
lem-comm-push-BOX⟨0·41⟩-sw1-R : WsL → ⟪ (ℓ "乊价") ⟫ʷ ≈ ⟪ (ℓ "仿乊") ⟫ʷ
lem-comm-push-BOX⟨0·41⟩-sw1-R c4 = derive (ℓ "乊价") (ℓ "仿乊")
  (re 1 1 (ℓ "乗") ∷
   rw⁻ 0 (q79 c4) ∷
   re 0 1 (ℓ "仿") ∷ []) Eq.refl

-- comm push SBOX(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (ℓ "乊侰") ⟫ʷ ≈ ⟪ (ℓ "侱乊") ⟫ʷ
lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4 = derive (ℓ "乊侰") (ℓ "侱乊")
  (re 1 1 (ℓ "乕") ∷
   rw⁻ 0 (q12 c4) ∷
   re 0 1 (ℓ "侱") ∷ []) Eq.refl

-- comm push SBOXd(0;4;1;2) sw1 R: 3 steps
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R : WsL → ⟪ (ℓ "乊侷") ⟫ʷ ≈ ⟪ (ℓ "侵乊") ⟫ʷ
lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4 = derive (ℓ "乊侷") (ℓ "侵乊")
  (re 1 1 (ℓ "乖") ∷
   rw⁻ 0 (q78 c4) ∷
   re 0 1 (ℓ "侵") ∷ []) Eq.refl

-- comm push BOX(0;42) sw2 R: 3 steps
lem-comm-push-BOX⟨0·42⟩-sw2-R : WsL → ⟪ (ℓ "乥仿") ⟫ʷ ≈ ⟪ (ℓ "仺乥") ⟫ʷ
lem-comm-push-BOX⟨0·42⟩-sw2-R c4 = derive (ℓ "乥仿") (ℓ "仺乥")
  (re 1 1 (ℓ "乫") ∷
   rw⁻ 0 (q77 c4) ∷
   re 0 1 (ℓ "仺") ∷ []) Eq.refl

-- comm push SBOX(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (ℓ "乥侱") ⟫ʷ ≈ ⟪ (ℓ "侲乥") ⟫ʷ
lem-comm-push-SBOX⟨0·4·2·1⟩-sw2-R c4 = derive (ℓ "乥侱") (ℓ "侲乥")
  (re 1 1 (ℓ "乩") ∷
   rw⁻ 0 (q11 c4) ∷
   re 0 1 (ℓ "侲") ∷ []) Eq.refl

-- comm push SBOXd(0;4;2;1) sw2 R: 3 steps
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R : WsL → ⟪ (ℓ "乥侵") ⟫ʷ ≈ ⟪ (ℓ "侳乥") ⟫ʷ
lem-comm-push-SBOXd⟨0·4·2·1⟩-sw2-R c4 = derive (ℓ "乥侵") (ℓ "侳乥")
  (re 1 1 (ℓ "乪") ∷
   rw⁻ 0 (q40 c4) ∷
   re 0 1 (ℓ "侳") ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (ℓ "乊伨") (ℓ "伨乊") (c₃ (Swap ↑) (CZ))

-- comm push BOX(4;103) sw1 R: 12 steps
lem-comm-push-BOX⟨4·103⟩-sw1-R : WsL → ⟪ (ℓ "乊伩") ⟫ʷ ≈ ⟪ (ℓ "作乊") ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw1-R c4 = derive (ℓ "乊伩") (ℓ "作乊")
  (re 1 1 (ℓ "五亗伨亗五伨") ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (ℓ "亜") ∷
   rw⁻ 3 (q14 c4) ∷
   re 1 3 (ℓ "亟") ∷
   rw 2 (q81 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 3 3 (ℓ "亟") ∷
   rw⁻ 6 (q14 c4) ∷
   re 4 3 (ℓ "亜") ∷
   rw 5 (q81 c4) ∷
   re 0 6 (ℓ "作") ∷ []) Eq.refl

-- comm CX40 TOFF213: 13 steps
lem-comm-CX40-TOFF213 : WsL → ⟪ (ℓ "亀亦") ⟫ʷ ≈ ⟪ (ℓ "亦亀") ⟫ʷ
lem-comm-CX40-TOFF213 c4 = derive (ℓ "亀亦") (ℓ "亦亀")
  (re 0 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (ℓ "亪") ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (ℓ "亮") ∷
   rw 4 (q47 c4) ∷
   rw 3 (q59 c4) ∷
   rw 2 (q45 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q2 c4) ∷
   re 1 1 (ℓ "乼亦乼") ∷
   rw 0 (q1 c4) ∷
   re 1 7 (ℓ "亀") ∷ []) Eq.refl

-- comm TOFF213 CX40: 13 steps
lem-comm-TOFF213-CX40 : WsL → ⟪ (ℓ "亦亀") ⟫ʷ ≈ ⟪ (ℓ "亀亦") ⟫ʷ
lem-comm-TOFF213-CX40 c4 = derive (ℓ "亦亀") (ℓ "亀亦")
  (re 1 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亪") ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "亮") ∷
   rw⁻ 2 (q45 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   re 5 1 (ℓ "乥亪乥") ∷
   rw 7 (q2 c4) ∷
   re 6 1 (ℓ "乼亦乼") ∷
   rw 8 (q1 c4) ∷
   re 0 7 (ℓ "亀") ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = wlE 76 c4

-- comm push BOX(0;21) sw0 R: 3 steps
lem-comm-push-BOX⟨0·21⟩-sw0-R : WsL → ⟪ (ℓ "丫仇") ⟫ʷ ≈ ⟪ (ℓ "伐丫") ⟫ʷ
lem-comm-push-BOX⟨0·21⟩-sw0-R c4 = derive (ℓ "丫仇") (ℓ "伐丫")
  (re 1 1 (ℓ "义") ∷
   rw⁻ 0 (q82 c4) ∷
   re 0 1 (ℓ "伐") ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = wlE 24 c4

-- comm push SBOX(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (ℓ "丫侪") ⟫ʷ ≈ ⟪ (ℓ "侼丫") ⟫ʷ
lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4 = derive (ℓ "丫侪") (ℓ "侼丫")
  (re 1 1 (ℓ "乇") ∷
   rw⁻ 0 (q83 c4) ∷
   re 0 1 (ℓ "侼") ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = wlE 23 c4

-- comm push SBOXd(0;2;1;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R : WsL → ⟪ (ℓ "丫侫") ⟫ʷ ≈ ⟪ (ℓ "侽丫") ⟫ʷ
lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4 = derive (ℓ "丫侫") (ℓ "侽丫")
  (re 1 1 (ℓ "么") ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (ℓ "侽") ∷ []) Eq.refl

-- comm push BOX(1;20) sw1 R: 4 steps
lem-comm-push-BOX⟨1·20⟩-sw1-R : WsL → ⟪ (ℓ "乊伐") ⟫ʷ ≈ ⟪ (ℓ "伓乊") ⟫ʷ
lem-comm-push-BOX⟨1·20⟩-sw1-R c4 = derive (ℓ "乊伐") (ℓ "伓乊")
  (re 1 1 (ℓ "丱") ∷
   re 1 1 (ℓ "乊个乊") ∷
   rw 0 (q14 c4) ∷
   re 0 1 (ℓ "伓") ∷ []) Eq.refl

-- comm push SBOX(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (ℓ "乊侼") ⟫ʷ ≈ ⟪ (ℓ "俅乊") ⟫ʷ
lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4 = derive (ℓ "乊侼") (ℓ "俅乊")
  (re 1 1 (ℓ "丯") ∷
   re 1 1 (ℓ "乊丨乊") ∷
   rw 0 (q14 c4) ∷
   re 0 1 (ℓ "俅") ∷ []) Eq.refl

-- comm push SBOXd(1;2;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R : WsL → ⟪ (ℓ "乊侽") ⟫ʷ ≈ ⟪ (ℓ "俆乊") ⟫ʷ
lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4 = derive (ℓ "乊侽") (ℓ "俆乊")
  (re 1 1 (ℓ "丰") ∷
   re 1 1 (ℓ "乊丩乊") ∷
   rw 0 (q14 c4) ∷
   re 0 1 (ℓ "俆") ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = wlE 139 c4
  q86 : WsL → Eqn
  q86 c4 = wlE 140 c4
  q87 : WsL → Eqn
  q87 c4 = eqn (ℓ "伓乥") (ℓ "乥伓") (c₂ (CZ) (Swap))

-- comm push BOX(1;230) sw2 R: 8 steps
lem-comm-push-BOX⟨1·230⟩-sw2-R : WsL → ⟪ (ℓ "乥伔") ⟫ʷ ≈ ⟪ (ℓ "伞乥") ⟫ʷ
lem-comm-push-BOX⟨1·230⟩-sw2-R c4 = derive (ℓ "乥伔") (ℓ "伞乥")
  (re 1 1 (ℓ "交亥伓亥交伓") ∷
   rw⁻ 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw⁻ 5 (q87 c4) ∷
   re 0 6 (ℓ "伞") ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (ℓ "伝乼") (ℓ "乼伝") (c₂ (CZ) (Swap ↑))

-- comm push BOX(1;320) sw3 R: 12 steps
lem-comm-push-BOX⟨1·320⟩-sw3-R : WsL → ⟪ (ℓ "乼伞") ⟫ʷ ≈ ⟪ (ℓ "伧乼") ⟫ʷ
lem-comm-push-BOX⟨1·320⟩-sw3-R c4 = derive (ℓ "乼伞") (ℓ "伧乼")
  (re 1 1 (ℓ "交亥伝亥交伝") ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (ℓ "亨") ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "亩") ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "亩") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "亨") ∷
   rw⁻ 5 (q88 c4) ∷
   re 0 6 (ℓ "伧") ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (ℓ "伦乥") (ℓ "乥伦") (c₂ (CZ) (Swap))

-- comm push BOX(1;420) sw2 R: 12 steps
lem-comm-push-BOX⟨1·420⟩-sw2-R : WsL → ⟪ (ℓ "乥伧") ⟫ʷ ≈ ⟪ (ℓ "伬乥") ⟫ʷ
lem-comm-push-BOX⟨1·420⟩-sw2-R c4 = derive (ℓ "乥伧") (ℓ "伬乥")
  (re 1 1 (ℓ "亨亩伦亩亨伦") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "京") ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (ℓ "亭") ∷
   rw⁻ 2 (q89 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "亭") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 5 (q89 c4) ∷
   re 0 6 (ℓ "伬") ∷ []) Eq.refl

-- comm push BOX(4;10) sw1 R: 4 steps
lem-comm-push-BOX⟨4·10⟩-sw1-R : WsL → ⟪ (ℓ "乊伦") ⟫ʷ ≈ ⟪ (ℓ "佚乊") ⟫ʷ
lem-comm-push-BOX⟨4·10⟩-sw1-R c4 = derive (ℓ "乊伦") (ℓ "佚乊")
  (re 1 1 (ℓ "个") ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (ℓ "丱") ∷
   re 0 1 (ℓ "佚") ∷ []) Eq.refl

-- comm push SBOX(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (ℓ "乊俪") ⟫ʷ ≈ ⟪ (ℓ "俲乊") ⟫ʷ
lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R c4 = derive (ℓ "乊俪") (ℓ "俲乊")
  (re 1 1 (ℓ "丨") ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (ℓ "丯") ∷
   re 0 1 (ℓ "俲") ∷ []) Eq.refl

-- comm push SBOXd(4;1;0;3) sw1 R: 4 steps
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R : WsL → ⟪ (ℓ "乊修") ⟫ʷ ≈ ⟪ (ℓ "俶乊") ⟫ʷ
lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R c4 = derive (ℓ "乊修") (ℓ "俶乊")
  (re 1 1 (ℓ "丩") ∷
   rw⁻ 2 (q14 c4) ∷
   re 0 3 (ℓ "丰") ∷
   re 0 1 (ℓ "俶") ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = wlE 145 c4

-- comm push BOX(4;20) sw0 R: 3 steps
lem-comm-push-BOX⟨4·20⟩-sw0-R : WsL → ⟪ (ℓ "丫佚") ⟫ʷ ≈ ⟪ (ℓ "佐丫") ⟫ʷ
lem-comm-push-BOX⟨4·20⟩-sw0-R c4 = derive (ℓ "丫佚") (ℓ "佐丫")
  (re 1 1 (ℓ "丱") ∷
   rw⁻ 0 (q90 c4) ∷
   re 0 1 (ℓ "佐") ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = wlE 146 c4

-- comm push SBOX(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (ℓ "丫俲") ⟫ʷ ≈ ⟪ (ℓ "俳丫") ⟫ʷ
lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R c4 = derive (ℓ "丫俲") (ℓ "俳丫")
  (re 1 1 (ℓ "丯") ∷
   rw⁻ 0 (q91 c4) ∷
   re 0 1 (ℓ "俳") ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = wlE 147 c4

-- comm push SBOXd(4;2;0;3) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R : WsL → ⟪ (ℓ "丫俶") ⟫ʷ ≈ ⟪ (ℓ "俴丫") ⟫ʷ
lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R c4 = derive (ℓ "丫俶") (ℓ "俴丫")
  (re 1 1 (ℓ "丰") ∷
   rw⁻ 0 (q92 c4) ∷
   re 0 1 (ℓ "俴") ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (ℓ "亏乺") (ℓ "乺亏") (c₃ (Toffᵗ) (CS • CS • CS))

-- comm CSd13 TOFF402: 11 steps
lem-comm-CSd13-TOFF402 : WsL → ⟪ (ℓ "乏亟") ⟫ʷ ≈ ⟪ (ℓ "亟乏") ⟫ʷ
lem-comm-CSd13-TOFF402 c4 = derive (ℓ "乏亟") (ℓ "亟乏")
  (re 1 1 (ℓ "乊乼乥亏乥乼乊") ∷
   rw 0 (q43 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乪") ∷
   rw 2 (q42 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw 4 (q40 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 7 (q1 c4) ∷
   rw 6 (q39 c4) ∷
   re 0 7 (ℓ "亟") ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = wlE 46 c4
  q95 : WsL → Eqn
  q95 c4 = wlE 47 c4

-- comm CS13 TOFF402: 11 steps
lem-comm-CS13-TOFF402 : WsL → ⟪ (ℓ "乎亟") ⟫ʷ ≈ ⟪ (ℓ "亟乎") ⟫ʷ
lem-comm-CS13-TOFF402 c4 = derive (ℓ "乎亟") (ℓ "亟乎")
  (re 1 1 (ℓ "乊乼乥亏乥乼乊") ∷
   rw 0 (q94 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 7 (q1 c4) ∷
   rw 6 (q95 c4) ∷
   re 0 7 (ℓ "亟") ∷ []) Eq.refl

-- comm SWAP03 BOX(4;21): 3 steps
lem-comm-SWAP03-BOX⟨4·21⟩ : WsL → ⟪ (ℓ "丹佐") ⟫ʷ ≈ ⟪ (ℓ "佐丹") ⟫ʷ
lem-comm-SWAP03-BOX⟨4·21⟩ c4 = derive (ℓ "丹佐") (ℓ "佐丹")
  (re 1 1 (ℓ "义") ∷
   rw⁻ 0 (q50 c4) ∷
   re 0 1 (ℓ "佐") ∷ []) Eq.refl

-- comm TOFF402 CSd13: 11 steps
lem-comm-TOFF402-CSd13 : WsL → ⟪ (ℓ "亟乏") ⟫ʷ ≈ ⟪ (ℓ "乏亟") ⟫ʷ
lem-comm-TOFF402-CSd13 c4 = derive (ℓ "亟乏") (ℓ "乏亟")
  (re 0 1 (ℓ "乊乼乥亏乥乼乊") ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   re 1 7 (ℓ "亟") ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (ℓ "丩亳") (ℓ "亳丩") (c₂ (CS • CS • CS) (Toffᵗ))

-- comm CSd02 TOFF413: 23 steps
lem-comm-CSd02-TOFF413 : WsL → ⟪ (ℓ "丰亯") ⟫ʷ ≈ ⟪ (ℓ "亯丰") ⟫ʷ
lem-comm-CSd02-TOFF413 c4 = derive (ℓ "丰亯") (ℓ "亯丰")
  (re 1 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "丷") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "举") ∷
   re 2 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "享") ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "亯") ∷
   rw 6 (q38 c4) ∷
   rw 5 (q96 c4) ∷
   rw 4 (q36 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 3 (q2 c4) ∷
   re 3 1 (ℓ "乼产乼") ∷
   rw 2 (q1 c4) ∷
   re 3 7 (ℓ "举") ∷
   re 3 1 (ℓ "乼丷乼") ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乥丰乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "亯") ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (ℓ "中亳") (ℓ "亳中") (c₂ (CK₀₁) (Toffᵗ))

-- comm CK02 TOFF413: 23 steps
lem-comm-CK02-TOFF413 : WsL → ⟪ (ℓ "临亯") ⟫ʷ ≈ ⟪ (ℓ "亯临") ⟫ʷ
lem-comm-CK02-TOFF413 c4 = derive (ℓ "临亯") (ℓ "亯临")
  (re 1 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "主") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乂") ∷
   re 2 1 (ℓ "乼乥乊中乊乥乼") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "享") ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "亯") ∷
   rw 6 (q38 c4) ∷
   rw 5 (q97 c4) ∷
   rw 4 (q36 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 3 (q2 c4) ∷
   re 3 1 (ℓ "乼产乼") ∷
   rw 2 (q1 c4) ∷
   re 3 7 (ℓ "乂") ∷
   re 3 1 (ℓ "乼主乼") ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乥临乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "亯") ∷ []) Eq.refl

-- comm push BOX(2;03) sw2 R: 4 steps
lem-comm-push-BOX⟨2·03⟩-sw2-R : WsL → ⟪ (ℓ "乥仈") ⟫ʷ ≈ ⟪ (ℓ "仠乥") ⟫ʷ
lem-comm-push-BOX⟨2·03⟩-sw2-R c4 = derive (ℓ "乥仈") (ℓ "仠乥")
  (re 1 1 (ℓ "丸") ∷
   re 1 1 (ℓ "乥丱乥") ∷
   rw 0 (q2 c4) ∷
   re 0 1 (ℓ "仠") ∷ []) Eq.refl

-- comm push SBOX(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (ℓ "乥係") ⟫ʷ ≈ ⟪ (ℓ "俑乥") ⟫ʷ
lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R c4 = derive (ℓ "乥係") (ℓ "俑乥")
  (re 1 1 (ℓ "丶") ∷
   re 1 1 (ℓ "乥丯乥") ∷
   rw 0 (q2 c4) ∷
   re 0 1 (ℓ "俑") ∷ []) Eq.refl

-- comm push SBOXd(2;0;3;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R : WsL → ⟪ (ℓ "乥促") ⟫ʷ ≈ ⟪ (ℓ "俕乥") ⟫ʷ
lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R c4 = derive (ℓ "乥促") (ℓ "俕乥")
  (re 1 1 (ℓ "丷") ∷
   re 1 1 (ℓ "乥丰乥") ∷
   rw 0 (q2 c4) ∷
   re 0 1 (ℓ "俕") ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (ℓ "仠乼") (ℓ "乼仠") (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- comm push BOX(0;312) sw3 R: 12 steps
lem-comm-push-BOX⟨0·312⟩-sw3-R : WsL → ⟪ (ℓ "乼仡") ⟫ʷ ≈ ⟪ (ℓ "仹乼") ⟫ʷ
lem-comm-push-BOX⟨0·312⟩-sw3-R c4 = derive (ℓ "乼仡") (ℓ "仹乼")
  (re 1 1 (ℓ "亐云仠云亐仠") ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (ℓ "五") ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "井") ∷
   rw⁻ 2 (q98 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "井") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "五") ∷
   rw⁻ 5 (q98 c4) ∷
   re 0 6 (ℓ "仹") ∷ []) Eq.refl

-- comm push BOX(4;02) sw2 R: 4 steps
lem-comm-push-BOX⟨4·02⟩-sw2-R : WsL → ⟪ (ℓ "乥仸") ⟫ʷ ≈ ⟪ (ℓ "份乥") ⟫ʷ
lem-comm-push-BOX⟨4·02⟩-sw2-R c4 = derive (ℓ "乥仸") (ℓ "份乥")
  (re 1 1 (ℓ "丱") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "丸") ∷
   re 0 1 (ℓ "份") ∷ []) Eq.refl

-- comm push SBOX(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (ℓ "乥俣") ⟫ʷ ≈ ⟪ (ℓ "俤乥") ⟫ʷ
lem-comm-push-SBOX⟨4·0·2·1⟩-sw2-R c4 = derive (ℓ "乥俣") (ℓ "俤乥")
  (re 1 1 (ℓ "丯") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "丶") ∷
   re 0 1 (ℓ "俤") ∷ []) Eq.refl

-- comm push SBOXd(4;0;2;1) sw2 R: 4 steps
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R : WsL → ⟪ (ℓ "乥俧") ⟫ʷ ≈ ⟪ (ℓ "俥乥") ⟫ʷ
lem-comm-push-SBOXd⟨4·0·2·1⟩-sw2-R c4 = derive (ℓ "乥俧") (ℓ "俥乥")
  (re 1 1 (ℓ "丰") ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (ℓ "丷") ∷
   re 0 1 (ℓ "俥") ∷ []) Eq.refl

-- comm push BOX(4;03) sw1 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw1-R : WsL → ⟪ (ℓ "乊份") ⟫ʷ ≈ ⟪ (ℓ "份乊") ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw1-R c4 = derive (ℓ "乊份") (ℓ "份乊")
  (re 1 1 (ℓ "丸") ∷
   rw⁻ 0 (q64 c4) ∷
   re 0 1 (ℓ "份") ∷ []) Eq.refl

-- comm push SBOX(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (ℓ "乊俤") ⟫ʷ ≈ ⟪ (ℓ "俠乊") ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R c4 = derive (ℓ "乊俤") (ℓ "俠乊")
  (re 1 1 (ℓ "丶") ∷
   rw⁻ 0 (q63 c4) ∷
   re 0 1 (ℓ "俠") ∷ []) Eq.refl

-- comm push SBOXd(4;0;3;1) sw1 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R : WsL → ⟪ (ℓ "乊俥") ⟫ʷ ≈ ⟪ (ℓ "信乊") ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R c4 = derive (ℓ "乊俥") (ℓ "信乊")
  (re 1 1 (ℓ "丷") ∷
   rw⁻ 0 (q62 c4) ∷
   re 0 1 (ℓ "信") ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = wlE 151 c4

-- comm push BOX(4;03) sw0 R: 3 steps
lem-comm-push-BOX⟨4·03⟩-sw0-R : WsL → ⟪ (ℓ "丫份") ⟫ʷ ≈ ⟪ (ℓ "伤丫") ⟫ʷ
lem-comm-push-BOX⟨4·03⟩-sw0-R c4 = derive (ℓ "丫份") (ℓ "伤丫")
  (re 1 1 (ℓ "丸") ∷
   rw⁻ 0 (q99 c4) ∷
   re 0 1 (ℓ "伤") ∷ []) Eq.refl

-- comm push SBOX(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (ℓ "丫俠") ⟫ʷ ≈ ⟪ (ℓ "俫丫") ⟫ʷ
lem-comm-push-SBOX⟨4·0·3·2⟩-sw0-R c4 = derive (ℓ "丫俠") (ℓ "俫丫")
  (re 1 1 (ℓ "丶") ∷
   rw⁻ 0 (q69 c4) ∷
   re 0 1 (ℓ "俫") ∷ []) Eq.refl

-- comm push SBOXd(4;0;3;2) sw0 R: 3 steps
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R : WsL → ⟪ (ℓ "丫信") ⟫ʷ ≈ ⟪ (ℓ "俬丫") ⟫ʷ
lem-comm-push-SBOXd⟨4·0·3·2⟩-sw0-R c4 = derive (ℓ "丫信") (ℓ "俬丫")
  (re 1 1 (ℓ "丷") ∷
   rw⁻ 0 (q68 c4) ∷
   re 0 1 (ℓ "俬") ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = wlE 75 c4
  q101 : WsL → Eqn
  q101 c4 = eqn (ℓ "个乥") (ℓ "乥个") (c₂ (CZ) (Swap))
  q102 : WsL → Eqn
  q102 c4 = wlE 96 c4

-- comm SWAP12 BOX(4;03): 11 steps
lem-comm-SWAP12-BOX⟨4·03⟩ : WsL → ⟪ (ℓ "乊份") ⟫ʷ ≈ ⟪ (ℓ "份乊") ⟫ʷ
lem-comm-SWAP12-BOX⟨4·03⟩ c4 = derive (ℓ "乊份") (ℓ "份乊")
  (re 1 1 (ℓ "丸") ∷
   re 1 1 (ℓ "乥乊个乊乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "乑") ∷
   rw⁻ 1 (q100 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   re 4 1 (ℓ "乥乊乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "丸") ∷
   re 0 1 (ℓ "份") ∷ []) Eq.refl

-- resp CZ03 at 2: 4 steps
lem-resp-CZ03-at-2 : WsL → ⟪ (ℓ "丸") ⟫ʷ ≈ ⟪ (ℓ "乊丫乐丫乊") ⟫ʷ
lem-resp-CZ03-at-2 c4 = derive (ℓ "丸") (ℓ "乊丫乐丫乊")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q64 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = wlE 34 c4
  q104 : WsL → Eqn
  q104 c4 = eqn (ℓ "亏乻") (ℓ "乻亏") (c₃ (Toffᵗ) (CZ))

-- comm CZ13 TOFF402: 11 steps
lem-comm-CZ13-TOFF402 : WsL → ⟪ (ℓ "乐亟") ⟫ʷ ≈ ⟪ (ℓ "亟乐") ⟫ʷ
lem-comm-CZ13-TOFF402 c4 = derive (ℓ "乐亟") (ℓ "亟乐")
  (re 1 1 (ℓ "乊乼乥亏乥乼乊") ∷
   rw 0 (q35 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乫") ∷
   rw 2 (q103 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 4 (q77 c4) ∷
   re 5 1 (ℓ "乼乤乼") ∷
   rw 7 (q1 c4) ∷
   rw 6 (q33 c4) ∷
   re 0 7 (ℓ "亟") ∷ []) Eq.refl

-- comm TOFF413 CSd02: 23 steps
lem-comm-TOFF413-CSd02 : WsL → ⟪ (ℓ "亯丰") ⟫ʷ ≈ ⟪ (ℓ "丰亯") ⟫ʷ
lem-comm-TOFF413-CSd02 c4 = derive (ℓ "亯丰") (ℓ "丰亯")
  (re 0 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "丷") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "举") ∷
   re 3 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "享") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 5 (q96 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 7 1 (ℓ "乥享乥") ∷
   rw 9 (q2 c4) ∷
   re 8 1 (ℓ "乼产乼") ∷
   rw 10 (q1 c4) ∷
   re 2 7 (ℓ "举") ∷
   re 2 1 (ℓ "乼丷乼") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乥丰乥") ∷
   rw 0 (q2 c4) ∷
   re 1 5 (ℓ "亯") ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (ℓ "中亰") (ℓ "亰中") (c₂ (CK₀₁) (CCZ))

-- comm CCZ134 CK02: 23 steps
lem-comm-CCZ134-CK02 : WsL → ⟪ (ℓ "京临") ⟫ʷ ≈ ⟪ (ℓ "临京") ⟫ʷ
lem-comm-CCZ134-CK02 c4 = derive (ℓ "京临") (ℓ "临京")
  (re 0 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "主") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乂") ∷
   re 3 1 (ℓ "乼乥乊中乊乥乼") ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "亨") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 6 (q5 c4) ∷
   re 7 1 (ℓ "乥亨乥") ∷
   rw 9 (q2 c4) ∷
   re 8 1 (ℓ "乼交乼") ∷
   rw 10 (q1 c4) ∷
   re 2 7 (ℓ "乂") ∷
   re 2 1 (ℓ "乼主乼") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乥临乥") ∷
   rw 0 (q2 c4) ∷
   re 1 5 (ℓ "京") ∷ []) Eq.refl

-- comm CX23 TOFF401: 9 steps
lem-comm-CX23-TOFF401 : WsL → ⟪ (ℓ "书亗") ⟫ʷ ≈ ⟪ (ℓ "亗书") ⟫ʷ
lem-comm-CX23-TOFF401 c4 = derive (ℓ "书亗") (ℓ "亗书")
  (re 1 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乭") ∷
   rw 1 (q56 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   re 4 1 (ℓ "乼书乼") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亗") ∷ []) Eq.refl

-- comm CZ23 TOFF401: 9 steps
lem-comm-CZ23-TOFF401 : WsL → ⟪ (ℓ "乤亗") ⟫ʷ ≈ ⟪ (ℓ "亗乤") ⟫ʷ
lem-comm-CZ23-TOFF401 c4 = derive (ℓ "乤亗") (ℓ "亗乤")
  (re 1 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乫") ∷
   rw 1 (q103 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw 3 (q77 c4) ∷
   re 4 1 (ℓ "乼乤乼") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亗") ∷ []) Eq.refl

-- comm CK02 CCZ134: 23 steps
lem-comm-CK02-CCZ134 : WsL → ⟪ (ℓ "临京") ⟫ʷ ≈ ⟪ (ℓ "京临") ⟫ʷ
lem-comm-CK02-CCZ134 c4 = derive (ℓ "临京") (ℓ "京临")
  (re 1 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "主") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乂") ∷
   re 2 1 (ℓ "乼乥乊中乊乥乼") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "亨") ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (ℓ "京") ∷
   rw⁻ 6 (q5 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 3 (q2 c4) ∷
   re 3 1 (ℓ "乼交乼") ∷
   rw 2 (q1 c4) ∷
   re 3 7 (ℓ "乂") ∷
   re 3 1 (ℓ "乼主乼") ∷
   rw 5 (q1 c4) ∷
   re 4 1 (ℓ "乥临乥") ∷
   rw 6 (q2 c4) ∷
   re 0 5 (ℓ "京") ∷ []) Eq.refl

-- comm TOFF413 CK02: 23 steps
lem-comm-TOFF413-CK02 : WsL → ⟪ (ℓ "亯临") ⟫ʷ ≈ ⟪ (ℓ "临亯") ⟫ʷ
lem-comm-TOFF413-CK02 c4 = derive (ℓ "亯临") (ℓ "临亯")
  (re 0 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (ℓ "主") ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "乂") ∷
   re 3 1 (ℓ "乼乥乊中乊乥乼") ∷
   rw⁻ 2 (q1 c4) ∷
   re 3 3 (ℓ "享") ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 7 1 (ℓ "乥享乥") ∷
   rw 9 (q2 c4) ∷
   re 8 1 (ℓ "乼产乼") ∷
   rw 10 (q1 c4) ∷
   re 2 7 (ℓ "乂") ∷
   re 2 1 (ℓ "乼主乼") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乥临乥") ∷
   rw 0 (q2 c4) ∷
   re 1 5 (ℓ "亯") ∷ []) Eq.refl

-- comm TOFF401 CX23: 9 steps
lem-comm-TOFF401-CX23 : WsL → ⟪ (ℓ "亗书") ⟫ʷ ≈ ⟪ (ℓ "书亗") ⟫ʷ
lem-comm-TOFF401-CX23 c4 = derive (ℓ "亗书") (ℓ "书亗")
  (re 0 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "乭") ∷
   rw⁻ 3 (q58 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   re 1 1 (ℓ "乼书乼") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "亗") ∷ []) Eq.refl
