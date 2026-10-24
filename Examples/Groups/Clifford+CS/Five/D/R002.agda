{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)

module Examples.Groups.Clifford+CS.Five.D.R002 where

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
  q1 c4 = wlE 3 c4
  q2 : WsL → Eqn
  q2 c4 = wlE 28 c4
  q3 : WsL → Eqn
  q3 c4 = wlE 4 c4
  q4 : WsL → Eqn
  q4 c4 = wlE 12 c4
  q5 : WsL → Eqn
  q5 c4 = eqn (ℓ "于乺") (ℓ "乺于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))
  q6 : WsL → Eqn
  q6 c4 = wlE 9 c4
  q7 : WsL → Eqn
  q7 c4 = wlE 29 c4

-- comm CSd12 TOFF304: 15 steps
lem-comm-CSd12-TOFF304 : WsL → ⟪ (ℓ "么亢") ⟫ʷ ≈ ⟪ (ℓ "亢么") ⟫ʷ
lem-comm-CSd12-TOFF304 c4 = derive (ℓ "么亢") (ℓ "亢么")
  (re 1 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乏") ∷
   rw 1 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 8 (q3 c4) ∷
   rw 7 (q7 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亢") ∷ []) Eq.refl

-- comm TOFF304 CSd12: 15 steps
lem-comm-TOFF304-CSd12 : WsL → ⟪ (ℓ "亢么") ⟫ʷ ≈ ⟪ (ℓ "么亢") ⟫ʷ
lem-comm-TOFF304-CSd12 c4 = derive (ℓ "亢么") (ℓ "么亢")
  (re 0 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乏") ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乪") ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 1 1 (ℓ "乥么乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亢") ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = wlE 44 c4
  q9 : WsL → Eqn
  q9 c4 = eqn (ℓ "乄亰") (ℓ "亰乄") (c₂ (CX₁₀) (CCZ))
  q10 : WsL → Eqn
  q10 c4 = wlE 37 c4

-- comm CX40 CCZ123: 13 steps
lem-comm-CX40-CCZ123 : WsL → ⟪ (ℓ "亀交") ⟫ʷ ≈ ⟪ (ℓ "交亀") ⟫ʷ
lem-comm-CX40-CCZ123 c4 = derive (ℓ "亀交") (ℓ "交亀")
  (re 0 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "亨") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "京") ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   re 2 1 (ℓ "乥亨乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼交乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "亀") ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = wlE 84 c4
  q12 : WsL → Eqn
  q12 c4 = eqn (ℓ "丩亳") (ℓ "亳丩") (c₂ (CS • CS • CS) (Toffᵗ))
  q13 : WsL → Eqn
  q13 c4 = wlE 85 c4

-- comm CSd04 TOFF312: 13 steps
lem-comm-CSd04-TOFF312 : WsL → ⟪ (ℓ "举产") ⟫ʷ ≈ ⟪ (ℓ "产举") ⟫ʷ
lem-comm-CSd04-TOFF312 c4 = derive (ℓ "举产") (ℓ "产举")
  (re 0 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "享") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亯") ∷
   rw 4 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼产乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "举") ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (ℓ "乄亳") (ℓ "亳乄") (c₂ (CX₁₀) (Toffᵗ))

-- comm CX40 TOFF312: 13 steps
lem-comm-CX40-TOFF312 : WsL → ⟪ (ℓ "亀产") ⟫ʷ ≈ ⟪ (ℓ "产亀") ⟫ʷ
lem-comm-CX40-TOFF312 c4 = derive (ℓ "亀产") (ℓ "产亀")
  (re 0 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "享") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亯") ∷
   rw 4 (q11 c4) ∷
   rw 3 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼产乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "亀") ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = wlE 33 c4
  q16 : WsL → Eqn
  q16 c4 = wlE 34 c4
  q17 : WsL → Eqn
  q17 c4 = eqn (ℓ "于乻") (ℓ "乻于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CZ))
  q18 : WsL → Eqn
  q18 c4 = wlE 35 c4
  q19 : WsL → Eqn
  q19 c4 = wlE 36 c4

-- comm CZ12 TOFF304: 15 steps
lem-comm-CZ12-TOFF304 : WsL → ⟪ (ℓ "义亢") ⟫ʷ ≈ ⟪ (ℓ "亢义") ⟫ʷ
lem-comm-CZ12-TOFF304 c4 = derive (ℓ "义亢") (ℓ "亢义")
  (re 1 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乐") ∷
   rw 1 (q15 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "乫") ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   re 6 1 (ℓ "乼乤乼") ∷
   rw 8 (q3 c4) ∷
   rw 7 (q19 c4) ∷
   re 8 1 (ℓ "乥义乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亢") ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (ℓ "亏乺") (ℓ "乺亏") (c₃ (Toffᵗ) (CS • CS • CS))

-- comm CSd23 TOFF401: 9 steps
lem-comm-CSd23-TOFF401 : WsL → ⟪ (ℓ "乣亗") ⟫ʷ ≈ ⟪ (ℓ "亗乣") ⟫ʷ
lem-comm-CSd23-TOFF401 c4 = derive (ℓ "乣亗") (ℓ "亗乣")
  (re 1 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "乪") ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q6 c4) ∷
   re 4 1 (ℓ "乼乣乼") ∷
   rw 6 (q3 c4) ∷
   re 0 5 (ℓ "亗") ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = wlE 11 c4
  q22 : WsL → Eqn
  q22 c4 = eqn (ℓ "亏乹") (ℓ "乹亏") (c₃ (Toffᵗ) (CS))
  q23 : WsL → Eqn
  q23 c4 = wlE 8 c4

-- comm CS23 TOFF401: 9 steps
lem-comm-CS23-TOFF401 : WsL → ⟪ (ℓ "乢亗") ⟫ʷ ≈ ⟪ (ℓ "亗乢") ⟫ʷ
lem-comm-CS23-TOFF401 c4 = derive (ℓ "乢亗") (ℓ "亗乢")
  (re 1 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 6 (q3 c4) ∷
   re 0 5 (ℓ "亗") ∷ []) Eq.refl

-- comm CSd24 TOFF301: 5 steps
lem-comm-CSd24-TOFF301 : WsL → ⟪ (ℓ "乪亓") ⟫ʷ ≈ ⟪ (ℓ "亓乪") ⟫ʷ
lem-comm-CSd24-TOFF301 c4 = derive (ℓ "乪亓") (ℓ "亓乪")
  (re 1 1 (ℓ "乥亏乥") ∷
   rw 0 (q4 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw 2 (q6 c4) ∷
   re 0 3 (ℓ "亓") ∷ []) Eq.refl

-- comm CS24 TOFF301: 5 steps
lem-comm-CS24-TOFF301 : WsL → ⟪ (ℓ "乩亓") ⟫ʷ ≈ ⟪ (ℓ "亓乩") ⟫ʷ
lem-comm-CS24-TOFF301 c4 = derive (ℓ "乩亓") (ℓ "亓乩")
  (re 1 1 (ℓ "乥亏乥") ∷
   rw 0 (q21 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   re 0 3 (ℓ "亓") ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (ℓ "串乼") (ℓ "乼串") (c₃ (Swap ↑ • Swap • Swap ↑) (Swap))
  q25 : WsL → Eqn
  q25 c4 = wlE 86 c4

-- comm SWAP02 BOX(3;14): 11 steps
lem-comm-SWAP02-BOX⟨3·14⟩ : WsL → ⟪ (ℓ "串伛") ⟫ʷ ≈ ⟪ (ℓ "伛串") ⟫ʷ
lem-comm-SWAP02-BOX⟨3·14⟩ c4 = derive (ℓ "串伛") (ℓ "伛串")
  (re 1 1 (ℓ "乗") ∷
   re 1 1 (ℓ "乼乥义乥乼") ∷
   rw 0 (q24 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "丹") ∷
   rw⁻ 2 (q25 c4) ∷
   re 3 1 (ℓ "乥串乥") ∷
   rw 5 (q1 c4) ∷
   rw 4 (q24 c4) ∷
   re 0 5 (ℓ "乗") ∷
   re 0 1 (ℓ "伛") ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (ℓ "亏乻") (ℓ "乻亏") (c₃ (Toffᵗ) (CZ))

-- comm CZ12 TOFF403: 15 steps
lem-comm-CZ12-TOFF403 : WsL → ⟪ (ℓ "义亣") ⟫ʷ ≈ ⟪ (ℓ "亣义") ⟫ʷ
lem-comm-CZ12-TOFF403 c4 = derive (ℓ "义亣") (ℓ "亣义")
  (re 1 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乐") ∷
   rw 1 (q15 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "乫") ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 5 (q18 c4) ∷
   re 6 1 (ℓ "乼乤乼") ∷
   rw 8 (q3 c4) ∷
   rw 7 (q19 c4) ∷
   re 8 1 (ℓ "乥义乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亣") ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "丨亳") (ℓ "亳丨") (c₂ (CS) (Toffᵗ))

-- comm CS04 TOFF312: 13 steps
lem-comm-CS04-TOFF312 : WsL → ⟪ (ℓ "丽产") ⟫ʷ ≈ ⟪ (ℓ "产丽") ⟫ʷ
lem-comm-CS04-TOFF312 c4 = derive (ℓ "丽产") (ℓ "产丽")
  (re 0 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "享") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亯") ∷
   rw 4 (q11 c4) ∷
   rw 3 (q27 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼产乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "丽") ∷ []) Eq.refl

-- comm TOFF312 CS04: 13 steps
lem-comm-TOFF312-CS04 : WsL → ⟪ (ℓ "产丽") ⟫ʷ ≈ ⟪ (ℓ "丽产") ⟫ʷ
lem-comm-TOFF312-CS04 c4 = derive (ℓ "产丽") (ℓ "丽产")
  (re 1 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "享") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亯") ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 1 (ℓ "乥享乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼产乼") ∷
   rw 8 (q3 c4) ∷
   re 0 7 (ℓ "丽") ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = wlE 6 c4
  q29 : WsL → Eqn
  q29 c4 = wlE 87 c4
  q30 : WsL → Eqn
  q30 c4 = wlE 18 c4
  q31 : WsL → Eqn
  q31 c4 = eqn (ℓ "丫亇") (ℓ "亇丫") (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- resp CK41 at 2: 4 steps
lem-resp-CK41-at-2 : WsL → ⟪ (ℓ "亄") ⟫ʷ ≈ ⟪ (ℓ "乊丫亇丫乊") ⟫ʷ
lem-resp-CK41-at-2 c4 = derive (ℓ "亄") (ℓ "乊丫亇丫乊")
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q31 c4) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = wlE 45 c4
  q33 : WsL → Eqn
  q33 c4 = eqn (ℓ "丨亲") (ℓ "亲丨") (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q34 : WsL → Eqn
  q34 c4 = wlE 38 c4

-- comm CS04 TOFF213: 13 steps
lem-comm-CS04-TOFF213 : WsL → ⟪ (ℓ "丽亦") ⟫ʷ ≈ ⟪ (ℓ "亦丽") ⟫ʷ
lem-comm-CS04-TOFF213 c4 = derive (ℓ "丽亦") (ℓ "亦丽")
  (re 0 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "亪") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亮") ∷
   rw 4 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼亦乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "丽") ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = wlE 14 c4
  q36 : WsL → Eqn
  q36 c4 = eqn (ℓ "二乺") (ℓ "乺二") (c₃ (CCZ) (CS • CS • CS))
  q37 : WsL → Eqn
  q37 c4 = wlE 7 c4

-- comm CSd14 CCZ023: 7 steps
lem-comm-CSd14-CCZ023 : WsL → ⟪ (ℓ "乖亘") ⟫ʷ ≈ ⟪ (ℓ "亘乖") ⟫ʷ
lem-comm-CSd14-CCZ023 c4 = derive (ℓ "乖亘") (ℓ "亘乖")
  (re 1 1 (ℓ "乊乥二乥乊") ∷
   rw 0 (q35 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (ℓ "亘") ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = wlE 13 c4
  q39 : WsL → Eqn
  q39 c4 = eqn (ℓ "二乹") (ℓ "乹二") (c₃ (CCZ) (CS))
  q40 : WsL → Eqn
  q40 c4 = wlE 5 c4

-- comm CS14 CCZ023: 7 steps
lem-comm-CS14-CCZ023 : WsL → ⟪ (ℓ "乕亘") ⟫ʷ ≈ ⟪ (ℓ "亘乕") ⟫ʷ
lem-comm-CS14-CCZ023 c4 = derive (ℓ "乕亘") (ℓ "亘乕")
  (re 1 1 (ℓ "乊乥二乥乊") ∷
   rw 0 (q38 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q40 c4) ∷
   re 0 5 (ℓ "亘") ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (ℓ "乊乼") (ℓ "乼乊") (c₃ (Swap ↑) (Swap))
  q42 : WsL → Eqn
  q42 c4 = wlE 88 c4

-- comm push CK40 sw1 L: 5 steps
lem-comm-push-CK40-sw1-L : WsL → ⟪ (ℓ "亁乊") ⟫ʷ ≈ ⟪ (ℓ "乊亁") ⟫ʷ
lem-comm-push-CK40-sw1-L c4 = derive (ℓ "亁乊") (ℓ "乊亁")
  (re 0 1 (ℓ "乼乱乼") ∷
   rw⁻ 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   re 1 3 (ℓ "亁") ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))

-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : WsL → ⟪ (ℓ "举交") ⟫ʷ ≈ ⟪ (ℓ "交举") ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = derive (ℓ "举交") (ℓ "交举")
  (re 0 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "亨") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "京") ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   re 2 1 (ℓ "乥亨乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼交乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "举") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))

-- comm CS04 CCZ123: 13 steps
lem-comm-CS04-CCZ123 : WsL → ⟪ (ℓ "丽交") ⟫ʷ ≈ ⟪ (ℓ "交丽") ⟫ʷ
lem-comm-CS04-CCZ123 c4 = derive (ℓ "丽交") (ℓ "交丽")
  (re 0 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "亨") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "京") ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q44 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   re 2 1 (ℓ "乥亨乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼交乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "丽") ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (ℓ "久亲") (ℓ "亲久") (c₂ (CK₁₀) (K ↑ • CCZ • K ↑ • iI))

-- comm CK40 TOFF213: 13 steps
lem-comm-CK40-TOFF213 : WsL → ⟪ (ℓ "亁亦") ⟫ʷ ≈ ⟪ (ℓ "亦亁") ⟫ʷ
lem-comm-CK40-TOFF213 c4 = derive (ℓ "亁亦") (ℓ "亦亁")
  (re 0 1 (ℓ "乼乥乊久乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "亪") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亮") ∷
   rw 4 (q32 c4) ∷
   rw 3 (q45 c4) ∷
   rw 2 (q34 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼亦乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "亁") ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = wlE 2 c4
  q47 : WsL → Eqn
  q47 c4 = eqn (ℓ "久乼") (ℓ "乼久") (c₂ (CK₁₀) (Swap ↑))

-- comm push CK40 sw2 L: 7 steps
lem-comm-push-CK40-sw2-L : WsL → ⟪ (ℓ "亁乥") ⟫ʷ ≈ ⟪ (ℓ "乥亁") ⟫ʷ
lem-comm-push-CK40-sw2-L c4 = derive (ℓ "亁乥") (ℓ "乥亁")
  (re 0 1 (ℓ "乼乥乊久乊乥乼") ∷
   rw 5 (q46 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q47 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   re 1 7 (ℓ "亁") ∷ []) Eq.refl

-- comm CSd13 TOFF204: 11 steps
lem-comm-CSd13-TOFF204 : WsL → ⟪ (ℓ "乏亞") ⟫ʷ ≈ ⟪ (ℓ "亞乏") ⟫ʷ
lem-comm-CSd13-TOFF204 c4 = derive (ℓ "乏亞") (ℓ "亞乏")
  (re 1 1 (ℓ "乊乼乥于乥乼乊") ∷
   rw 0 (q2 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "乪") ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 7 (q3 c4) ∷
   rw 6 (q7 c4) ∷
   re 0 7 (ℓ "亞") ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = wlE 46 c4
  q49 : WsL → Eqn
  q49 c4 = eqn (ℓ "于乹") (ℓ "乹于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))
  q50 : WsL → Eqn
  q50 c4 = wlE 47 c4

-- comm CS13 TOFF204: 11 steps
lem-comm-CS13-TOFF204 : WsL → ⟪ (ℓ "乎亞") ⟫ʷ ≈ ⟪ (ℓ "亞乎") ⟫ʷ
lem-comm-CS13-TOFF204 c4 = derive (ℓ "乎亞") (ℓ "亞乎")
  (re 1 1 (ℓ "乊乼乥于乥乼乊") ∷
   rw 0 (q48 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 4 (q23 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 7 (q3 c4) ∷
   rw 6 (q50 c4) ∷
   re 0 7 (ℓ "亞") ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = wlE 69 c4
  q52 : WsL → Eqn
  q52 c4 = wlE 58 c4
  q53 : WsL → Eqn
  q53 c4 = eqn (ℓ "二争") (ℓ "争二") (c₃ (CCZ) (CX₁₀))
  q54 : WsL → Eqn
  q54 c4 = wlE 59 c4
  q55 : WsL → Eqn
  q55 c4 = wlE 89 c4

-- comm CX41 CCZ023: 7 steps
lem-comm-CX41-CCZ023 : WsL → ⟪ (ℓ "亃亘") ⟫ʷ ≈ ⟪ (ℓ "亘亃") ⟫ʷ
lem-comm-CX41-CCZ023 c4 = derive (ℓ "亃亘") (ℓ "亘亃")
  (re 1 1 (ℓ "乊乥二乥乊") ∷
   rw 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw 4 (q55 c4) ∷
   re 0 5 (ℓ "亘") ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (ℓ "个亲") (ℓ "亲个") (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))

-- comm CZ03 TOFF214: 9 steps
lem-comm-CZ03-TOFF214 : WsL → ⟪ (ℓ "丸亪") ⟫ʷ ≈ ⟪ (ℓ "亪丸") ⟫ʷ
lem-comm-CZ03-TOFF214 c4 = derive (ℓ "丸亪") (ℓ "亪丸")
  (re 0 1 (ℓ "乥乊个乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "亮") ∷
   rw 3 (q32 c4) ∷
   rw 2 (q56 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (ℓ "乥亪乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "丸") ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (ℓ "丩亲") (ℓ "亲丩") (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))

-- comm TOFF214 CSd03: 9 steps
lem-comm-TOFF214-CSd03 : WsL → ⟪ (ℓ "亪丷") ⟫ʷ ≈ ⟪ (ℓ "丷亪") ⟫ʷ
lem-comm-TOFF214-CSd03 c4 = derive (ℓ "亪丷") (ℓ "丷亪")
  (re 1 1 (ℓ "乥乊丩乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亮") ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "丷") ∷ []) Eq.refl

-- comm CSd14 TOFF203: 7 steps
lem-comm-CSd14-TOFF203 : WsL → ⟪ (ℓ "乖亚") ⟫ʷ ≈ ⟪ (ℓ "亚乖") ⟫ʷ
lem-comm-CSd14-TOFF203 c4 = derive (ℓ "乖亚") (ℓ "亚乖")
  (re 1 1 (ℓ "乊乥于乥乊") ∷
   rw 0 (q35 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (ℓ "亚") ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (ℓ "个亰") (ℓ "亰个") (c₂ (CZ) (CCZ))

-- comm CZ03 CCZ124: 9 steps
lem-comm-CZ03-CCZ124 : WsL → ⟪ (ℓ "丸亨") ⟫ʷ ≈ ⟪ (ℓ "亨丸") ⟫ʷ
lem-comm-CZ03-CCZ124 c4 = derive (ℓ "丸亨") (ℓ "亨丸")
  (re 0 1 (ℓ "乥乊个乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 3 (q8 c4) ∷
   rw 2 (q58 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "丸") ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))

-- comm CX03 CCZ124: 9 steps
lem-comm-CX03-CCZ124 : WsL → ⟪ (ℓ "为亨") ⟫ʷ ≈ ⟪ (ℓ "亨为") ⟫ʷ
lem-comm-CX03-CCZ124 c4 = derive (ℓ "为亨") (ℓ "亨为")
  (re 0 1 (ℓ "乥乊丬乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 3 (q8 c4) ∷
   rw 2 (q59 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "为") ∷ []) Eq.refl

-- comm CSd03 TOFF214: 9 steps
lem-comm-CSd03-TOFF214 : WsL → ⟪ (ℓ "丷亪") ⟫ʷ ≈ ⟪ (ℓ "亪丷") ⟫ʷ
lem-comm-CSd03-TOFF214 c4 = derive (ℓ "丷亪") (ℓ "亪丷")
  (re 0 1 (ℓ "乥乊丩乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "亮") ∷
   rw 3 (q32 c4) ∷
   rw 2 (q57 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (ℓ "乥亪乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "丷") ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = wlE 90 c4
  q61 : WsL → Eqn
  q61 c4 = eqn (ℓ "二亊") (ℓ "亊二") (c₃ (CCZ) (CK₁₀))
  q62 : WsL → Eqn
  q62 c4 = wlE 91 c4
  q63 : WsL → Eqn
  q63 c4 = wlE 92 c4

-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : WsL → ⟪ (ℓ "亄亘") ⟫ʷ ≈ ⟪ (ℓ "亘亄") ⟫ʷ
lem-comm-CK41-CCZ023 c4 = derive (ℓ "亄亘") (ℓ "亘亄")
  (re 1 1 (ℓ "乊乥二乥乊") ∷
   rw 0 (q29 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   re 0 5 (ℓ "亘") ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (ℓ "亍亊") (ℓ "亊亍") (c₃ (Toff) (CK₁₀))

-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : WsL → ⟪ (ℓ "亄亙") ⟫ʷ ≈ ⟪ (ℓ "亙亄") ⟫ʷ
lem-comm-CK41-TOFF023 c4 = derive (ℓ "亄亙") (ℓ "亙亄")
  (re 1 1 (ℓ "乊乥亍乥乊") ∷
   rw 0 (q29 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   re 0 5 (ℓ "亙") ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (ℓ "亍乹") (ℓ "乹亍") (c₃ (Toff) (CS))

-- comm CS23 TOFF014: 9 steps
lem-comm-CS23-TOFF014 : WsL → ⟪ (ℓ "乢井") ⟫ʷ ≈ ⟪ (ℓ "井乢") ⟫ʷ
lem-comm-CS23-TOFF014 c4 = derive (ℓ "乢井") (ℓ "井乢")
  (re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q23 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 6 (q3 c4) ∷
   re 0 5 (ℓ "井") ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (ℓ "亍乻") (ℓ "乻亍") (c₃ (Toff) (CZ))

-- comm CZ13 TOFF024: 11 steps
lem-comm-CZ13-TOFF024 : WsL → ⟪ (ℓ "乐亝") ⟫ʷ ≈ ⟪ (ℓ "亝乐") ⟫ʷ
lem-comm-CZ13-TOFF024 c4 = derive (ℓ "乐亝") (ℓ "亝乐")
  (re 1 1 (ℓ "乊乼乥亍乥乼乊") ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "乫") ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 4 (q18 c4) ∷
   re 5 1 (ℓ "乼乤乼") ∷
   rw 7 (q3 c4) ∷
   rw 6 (q19 c4) ∷
   re 0 7 (ℓ "亝") ∷ []) Eq.refl

-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : WsL → ⟪ (ℓ "亇亐") ⟫ʷ ≈ ⟪ (ℓ "亐亇") ⟫ʷ
lem-comm-CK42-CCZ013 c4 = derive (ℓ "亇亐") (ℓ "亐亇")
  (re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q60 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   re 0 3 (ℓ "亐") ∷ []) Eq.refl

-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : WsL → ⟪ (ℓ "亇云") ⟫ʷ ≈ ⟪ (ℓ "云亇") ⟫ʷ
lem-comm-CK42-TOFF013 c4 = derive (ℓ "亇云") (ℓ "云亇")
  (re 1 1 (ℓ "乥亍乥") ∷
   rw 0 (q60 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw 2 (q62 c4) ∷
   re 0 3 (ℓ "云") ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = wlE 74 c4
  q68 : WsL → Eqn
  q68 c4 = wlE 72 c4
  q69 : WsL → Eqn
  q69 c4 = eqn (ℓ "个乬") (ℓ "乬个") (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))
  q70 : WsL → Eqn
  q70 c4 = wlE 93 c4

-- comm SWAP14 BOX(2;03): 9 steps
lem-comm-SWAP14-BOX⟨2·03⟩ : WsL → ⟪ (ℓ "乘仈") ⟫ʷ ≈ ⟪ (ℓ "仈乘") ⟫ʷ
lem-comm-SWAP14-BOX⟨2·03⟩ c4 = derive (ℓ "乘仈") (ℓ "仈乘")
  (re 1 1 (ℓ "丸") ∷
   re 1 1 (ℓ "乥乊个乊乥") ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 4 (q67 c4) ∷
   re 0 5 (ℓ "丸") ∷
   re 0 1 (ℓ "仈") ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = wlE 55 c4
  q72 : WsL → Eqn
  q72 c4 = eqn (ℓ "丫乼") (ℓ "乼丫") (c₂ (Swap) (Swap ↑))

-- resp SWAP24 at 3: 6 steps
lem-resp-SWAP24-at-3 : WsL → ⟪ (ℓ "乬") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乼丫乊乥") ⟫ʷ
lem-resp-SWAP24-at-3 c4 = derive (ℓ "乬") (ℓ "乥乊丫乼丫乊乥")
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q71 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 2 (q72 c4) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (ℓ "义乼") (ℓ "乼义") (c₃ (CZ ↑) (Swap))
  q74 : WsL → Eqn
  q74 c4 = wlE 56 c4

-- comm SWAP24 BOX(0;13): 7 steps
lem-comm-SWAP24-BOX⟨0·13⟩ : WsL → ⟪ (ℓ "乬人") ⟫ʷ ≈ ⟪ (ℓ "人乬") ⟫ʷ
lem-comm-SWAP24-BOX⟨0·13⟩ c4 = derive (ℓ "乬人") (ℓ "人乬")
  (re 1 1 (ℓ "乐") ∷
   re 1 1 (ℓ "乥义乥") ∷
   rw⁻ 0 (q71 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   re 0 3 (ℓ "乐") ∷
   re 0 1 (ℓ "人") ∷ []) Eq.refl

-- comm SWAP23 BOX(0;41): 11 steps
lem-comm-SWAP23-BOX⟨0·41⟩ : WsL → ⟪ (ℓ "乥价") ⟫ʷ ≈ ⟪ (ℓ "价乥") ⟫ʷ
lem-comm-SWAP23-BOX⟨0·41⟩ c4 = derive (ℓ "乥价") (ℓ "价乥")
  (re 1 1 (ℓ "乗") ∷
   re 1 1 (ℓ "乼乥义乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "乬") ∷
   rw⁻ 1 (q71 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 4 1 (ℓ "乼乥乼") ∷
   rw 6 (q3 c4) ∷
   re 0 5 (ℓ "乗") ∷
   re 0 1 (ℓ "价") ∷ []) Eq.refl

-- comm TOFF213 CSd04: 13 steps
lem-comm-TOFF213-CSd04 : WsL → ⟪ (ℓ "亦举") ⟫ʷ ≈ ⟪ (ℓ "举亦") ⟫ʷ
lem-comm-TOFF213-CSd04 c4 = derive (ℓ "亦举") (ℓ "举亦")
  (re 1 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "亪") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亮") ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (ℓ "乥亪乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼亦乼") ∷
   rw 8 (q3 c4) ∷
   re 0 7 (ℓ "举") ∷ []) Eq.refl

-- comm TOFF213 CK40: 13 steps
lem-comm-TOFF213-CK40 : WsL → ⟪ (ℓ "亦亁") ⟫ʷ ≈ ⟪ (ℓ "亁亦") ⟫ʷ
lem-comm-TOFF213-CK40 c4 = derive (ℓ "亦亁") (ℓ "亁亦")
  (re 1 1 (ℓ "乼乥乊久乊乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "亪") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亮") ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (ℓ "乥亪乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼亦乼") ∷
   rw 8 (q3 c4) ∷
   re 0 7 (ℓ "亁") ∷ []) Eq.refl

-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : WsL → ⟪ (ℓ "亐亇") ⟫ʷ ≈ ⟪ (ℓ "亇亐") ⟫ʷ
lem-comm-CCZ013-CK42 c4 = derive (ℓ "亐亇") (ℓ "亇亐")
  (re 1 1 (ℓ "乼乷乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "五") ∷
   re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "亇") ∷
   rw⁻ 4 (q62 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   re 2 1 (ℓ "乼乷乼") ∷
   rw 1 (q3 c4) ∷
   re 2 5 (ℓ "五") ∷
   re 2 1 (ℓ "乼亐乼") ∷
   rw 4 (q3 c4) ∷
   re 0 3 (ℓ "亇") ∷ []) Eq.refl

-- comm TOFF013 CK42: 15 steps
lem-comm-TOFF013-CK42 : WsL → ⟪ (ℓ "云亇") ⟫ʷ ≈ ⟪ (ℓ "亇云") ⟫ʷ
lem-comm-TOFF013-CK42 c4 = derive (ℓ "云亇") (ℓ "亇云")
  (re 1 1 (ℓ "乼乷乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "井") ∷
   re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "亇") ∷
   rw⁻ 4 (q62 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   re 2 1 (ℓ "乼乷乼") ∷
   rw 1 (q3 c4) ∷
   re 2 5 (ℓ "井") ∷
   re 2 1 (ℓ "乼云乼") ∷
   rw 4 (q3 c4) ∷
   re 0 3 (ℓ "亇") ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = wlE 22 c4
  q76 : WsL → Eqn
  q76 c4 = wlE 21 c4
  q77 : WsL → Eqn
  q77 c4 = eqn (ℓ "二乽") (ℓ "乽二") (c₃ (CCZ) (CX₀₁))
  q78 : WsL → Eqn
  q78 c4 = wlE 20 c4
  q79 : WsL → Eqn
  q79 c4 = wlE 19 c4

-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : WsL → ⟪ (ℓ "亜乒") ⟫ʷ ≈ ⟪ (ℓ "乒亜") ⟫ʷ
lem-comm-CCZ024-CX13 c4 = derive (ℓ "亜乒") (ℓ "乒亜")
  (re 0 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw⁻ 6 (q75 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乭") ∷
   rw⁻ 4 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 2 (q78 c4) ∷
   re 2 1 (ℓ "乼书乼") ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q79 c4) ∷
   re 1 7 (ℓ "亜") ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (ℓ "丬亲") (ℓ "亲丬") (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))

-- comm TOFF213 CX04: 13 steps
lem-comm-TOFF213-CX04 : WsL → ⟪ (ℓ "亦乁") ⟫ʷ ≈ ⟪ (ℓ "乁亦") ⟫ʷ
lem-comm-TOFF213-CX04 c4 = derive (ℓ "亦乁") (ℓ "乁亦")
  (re 1 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "亪") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亮") ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (ℓ "乥亪乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼亦乼") ∷
   rw 8 (q3 c4) ∷
   re 0 7 (ℓ "乁") ∷ []) Eq.refl

-- comm CZ02 TOFF314: 23 steps
lem-comm-CZ02-TOFF314 : WsL → ⟪ (ℓ "丱亮") ⟫ʷ ≈ ⟪ (ℓ "亮丱") ⟫ʷ
lem-comm-CZ02-TOFF314 c4 = derive (ℓ "丱亮") (ℓ "亮丱")
  (re 1 1 (ℓ "乥乼亦乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丸") ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "丿") ∷
   re 2 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "亪") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "亮") ∷
   rw 6 (q32 c4) ∷
   rw 5 (q56 c4) ∷
   rw 4 (q34 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼亦乼") ∷
   rw 2 (q3 c4) ∷
   re 3 7 (ℓ "丿") ∷
   re 3 1 (ℓ "乼丸乼") ∷
   rw 5 (q3 c4) ∷
   re 4 1 (ℓ "乥丱乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亮") ∷ []) Eq.refl

-- comm CSd02 TOFF314: 23 steps
lem-comm-CSd02-TOFF314 : WsL → ⟪ (ℓ "丰亮") ⟫ʷ ≈ ⟪ (ℓ "亮丰") ⟫ʷ
lem-comm-CSd02-TOFF314 c4 = derive (ℓ "丰亮") (ℓ "亮丰")
  (re 1 1 (ℓ "乥乼亦乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丷") ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "举") ∷
   re 2 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "亪") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "亮") ∷
   rw 6 (q32 c4) ∷
   rw 5 (q57 c4) ∷
   rw 4 (q34 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼亦乼") ∷
   rw 2 (q3 c4) ∷
   re 3 7 (ℓ "举") ∷
   re 3 1 (ℓ "乼丷乼") ∷
   rw 5 (q3 c4) ∷
   re 4 1 (ℓ "乥丰乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亮") ∷ []) Eq.refl

-- comm CS02 TOFF314: 23 steps
lem-comm-CS02-TOFF314 : WsL → ⟪ (ℓ "丯亮") ⟫ʷ ≈ ⟪ (ℓ "亮丯") ⟫ʷ
lem-comm-CS02-TOFF314 c4 = derive (ℓ "丯亮") (ℓ "亮丯")
  (re 1 1 (ℓ "乥乼亦乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丶") ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "亪") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "亮") ∷
   rw 6 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw 4 (q34 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼亦乼") ∷
   rw 2 (q3 c4) ∷
   re 3 7 (ℓ "丽") ∷
   re 3 1 (ℓ "乼丶乼") ∷
   rw 5 (q3 c4) ∷
   re 4 1 (ℓ "乥丯乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亮") ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (ℓ "丫亳") (ℓ "亳丫") (c₂ (Swap) (Toffᵗ))

-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : WsL → ⟪ (ℓ "亯") ⟫ʷ ≈ ⟪ (ℓ "乊丫亳丫乊") ⟫ʷ
lem-resp-TOFF413-at-2 c4 = derive (ℓ "亯") (ℓ "乊丫亳丫乊")
  (rw⁻ 1 (q28 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q81 c4) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (ℓ "丬亳") (ℓ "亳丬") (c₂ (CX₀₁) (Toffᵗ))

-- comm CX04 TOFF312: 13 steps
lem-comm-CX04-TOFF312 : WsL → ⟪ (ℓ "乁产") ⟫ʷ ≈ ⟪ (ℓ "产乁") ⟫ʷ
lem-comm-CX04-TOFF312 c4 = derive (ℓ "乁产") (ℓ "产乁")
  (re 0 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "享") ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (ℓ "亯") ∷
   rw 4 (q11 c4) ∷
   rw 3 (q82 c4) ∷
   rw 2 (q13 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q1 c4) ∷
   re 1 1 (ℓ "乼产乼") ∷
   rw 0 (q3 c4) ∷
   re 1 7 (ℓ "乁") ∷ []) Eq.refl

-- comm CX30 CCZ124: 9 steps
lem-comm-CX30-CCZ124 : WsL → ⟪ (ℓ "买亨") ⟫ʷ ≈ ⟪ (ℓ "亨买") ⟫ʷ
lem-comm-CX30-CCZ124 c4 = derive (ℓ "买亨") (ℓ "亨买")
  (re 0 1 (ℓ "乥乊乄乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 3 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "买") ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (ℓ "乄亲") (ℓ "亲乄") (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI))

-- comm CX30 TOFF214: 9 steps
lem-comm-CX30-TOFF214 : WsL → ⟪ (ℓ "买亪") ⟫ʷ ≈ ⟪ (ℓ "亪买") ⟫ʷ
lem-comm-CX30-TOFF214 c4 = derive (ℓ "买亪") (ℓ "亪买")
  (re 0 1 (ℓ "乥乊乄乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "亮") ∷
   rw 3 (q32 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (ℓ "乥亪乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "买") ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = wlE 32 c4
  q85 : WsL → Eqn
  q85 c4 = wlE 53 c4

-- comm CZ14 TOFF203: 7 steps
lem-comm-CZ14-TOFF203 : WsL → ⟪ (ℓ "乗亚") ⟫ʷ ≈ ⟪ (ℓ "亚乗") ⟫ʷ
lem-comm-CZ14-TOFF203 c4 = derive (ℓ "乗亚") (ℓ "亚乗")
  (re 1 1 (ℓ "乊乥于乥乊") ∷
   rw 0 (q84 c4) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q85 c4) ∷
   re 0 5 (ℓ "亚") ∷ []) Eq.refl

-- comm CS12 TOFF304: 15 steps
lem-comm-CS12-TOFF304 : WsL → ⟪ (ℓ "乇亢") ⟫ʷ ≈ ⟪ (ℓ "亢乇") ⟫ʷ
lem-comm-CS12-TOFF304 c4 = derive (ℓ "乇亢") (ℓ "亢乇")
  (re 1 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw 1 (q48 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "乩") ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 5 (q23 c4) ∷
   re 6 1 (ℓ "乼乢乼") ∷
   rw 8 (q3 c4) ∷
   rw 7 (q50 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亢") ∷ []) Eq.refl

-- comm TOFF314 CSd02: 23 steps
lem-comm-TOFF314-CSd02 : WsL → ⟪ (ℓ "亮丰") ⟫ʷ ≈ ⟪ (ℓ "丰亮") ⟫ʷ
lem-comm-TOFF314-CSd02 c4 = derive (ℓ "亮丰") (ℓ "丰亮")
  (re 0 1 (ℓ "乥乼亦乼乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "丷") ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "举") ∷
   re 3 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "亪") ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "亮") ∷
   rw⁻ 4 (q34 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 7 1 (ℓ "乥亪乥") ∷
   rw 9 (q1 c4) ∷
   re 8 1 (ℓ "乼亦乼") ∷
   rw 10 (q3 c4) ∷
   re 2 7 (ℓ "举") ∷
   re 2 1 (ℓ "乼丷乼") ∷
   rw 1 (q3 c4) ∷
   re 1 1 (ℓ "乥丰乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "亮") ∷ []) Eq.refl

-- comm CSd14 TOFF302: 7 steps
lem-comm-CSd14-TOFF302 : WsL → ⟪ (ℓ "乖些") ⟫ʷ ≈ ⟪ (ℓ "些乖") ⟫ʷ
lem-comm-CSd14-TOFF302 c4 = derive (ℓ "乖些") (ℓ "些乖")
  (re 1 1 (ℓ "乊乥亏乥乊") ∷
   rw 0 (q35 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (ℓ "些") ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = wlE 80 c4
  q87 : WsL → Eqn
  q87 c4 = wlE 78 c4

-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : WsL → ⟪ (ℓ "买") ⟫ʷ ≈ ⟪ (ℓ "乊丫乳丫乊") ⟫ʷ
lem-resp-CX30-at-2 c4 = derive (ℓ "买") (ℓ "乊丫乳丫乊")
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q87 c4) ∷ []) Eq.refl

-- comm CSd02 CCZ134: 23 steps
lem-comm-CSd02-CCZ134 : WsL → ⟪ (ℓ "丰京") ⟫ʷ ≈ ⟪ (ℓ "京丰") ⟫ʷ
lem-comm-CSd02-CCZ134 c4 = derive (ℓ "丰京") (ℓ "京丰")
  (re 1 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丷") ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "举") ∷
   re 2 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "亨") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "京") ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼交乼") ∷
   rw 2 (q3 c4) ∷
   re 3 7 (ℓ "举") ∷
   re 3 1 (ℓ "乼丷乼") ∷
   rw 5 (q3 c4) ∷
   re 4 1 (ℓ "乥丰乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "京") ∷ []) Eq.refl

-- comm CS02 CCZ134: 23 steps
lem-comm-CS02-CCZ134 : WsL → ⟪ (ℓ "丯京") ⟫ʷ ≈ ⟪ (ℓ "京丯") ⟫ʷ
lem-comm-CS02-CCZ134 c4 = derive (ℓ "丯京") (ℓ "京丯")
  (re 1 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丶") ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (ℓ "亨") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "京") ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼交乼") ∷
   rw 2 (q3 c4) ∷
   re 3 7 (ℓ "丽") ∷
   re 3 1 (ℓ "乼丶乼") ∷
   rw 5 (q3 c4) ∷
   re 4 1 (ℓ "乥丯乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "京") ∷ []) Eq.refl

-- comm CZ14 TOFF302: 7 steps
lem-comm-CZ14-TOFF302 : WsL → ⟪ (ℓ "乗些") ⟫ʷ ≈ ⟪ (ℓ "些乗") ⟫ʷ
lem-comm-CZ14-TOFF302 c4 = derive (ℓ "乗些") (ℓ "些乗")
  (re 1 1 (ℓ "乊乥亏乥乊") ∷
   rw 0 (q84 c4) ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q85 c4) ∷
   re 0 5 (ℓ "些") ∷ []) Eq.refl

-- comm CS03 TOFF214: 9 steps
lem-comm-CS03-TOFF214 : WsL → ⟪ (ℓ "丶亪") ⟫ʷ ≈ ⟪ (ℓ "亪丶") ⟫ʷ
lem-comm-CS03-TOFF214 c4 = derive (ℓ "丶亪") (ℓ "亪丶")
  (re 0 1 (ℓ "乥乊丨乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "亮") ∷
   rw 3 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   re 1 1 (ℓ "乥亪乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "丶") ∷ []) Eq.refl

-- comm TOFF214 CS03: 9 steps
lem-comm-TOFF214-CS03 : WsL → ⟪ (ℓ "亪丶") ⟫ʷ ≈ ⟪ (ℓ "丶亪") ⟫ʷ
lem-comm-TOFF214-CS03 c4 = derive (ℓ "亪丶") (ℓ "丶亪")
  (re 1 1 (ℓ "乥乊丨乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亮") ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "丶") ∷ []) Eq.refl

-- comm CZ23 TOFF014: 9 steps
lem-comm-CZ23-TOFF014 : WsL → ⟪ (ℓ "乤井") ⟫ʷ ≈ ⟪ (ℓ "井乤") ⟫ʷ
lem-comm-CZ23-TOFF014 c4 = derive (ℓ "乤井") (ℓ "井乤")
  (re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "乫") ∷
   rw 1 (q16 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 3 (q18 c4) ∷
   re 4 1 (ℓ "乼乤乼") ∷
   rw 6 (q3 c4) ∷
   re 0 5 (ℓ "井") ∷ []) Eq.refl

-- comm CZ24 TOFF301: 5 steps
lem-comm-CZ24-TOFF301 : WsL → ⟪ (ℓ "乫亓") ⟫ʷ ≈ ⟪ (ℓ "亓乫") ⟫ʷ
lem-comm-CZ24-TOFF301 c4 = derive (ℓ "乫亓") (ℓ "亓乫")
  (re 1 1 (ℓ "乥亏乥") ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 2 (q18 c4) ∷
   re 0 3 (ℓ "亓") ∷ []) Eq.refl

-- comm SWAP14 BOX(3;20): 7 steps
lem-comm-SWAP14-BOX⟨3·20⟩ : WsL → ⟪ (ℓ "乘佂") ⟫ʷ ≈ ⟪ (ℓ "佂乘") ⟫ʷ
lem-comm-SWAP14-BOX⟨3·20⟩ c4 = derive (ℓ "乘佂") (ℓ "佂乘")
  (re 1 1 (ℓ "丱") ∷
   re 1 1 (ℓ "乊个乊") ∷
   rw⁻ 0 (q68 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   re 0 3 (ℓ "丱") ∷
   re 0 1 (ℓ "佂") ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = wlE 57 c4
  q89 : WsL → Eqn
  q89 c4 = eqn (ℓ "亍争") (ℓ "争亍") (c₃ (Toff) (CX₁₀))
  q90 : WsL → Eqn
  q90 c4 = wlE 60 c4

-- comm CX31 TOFF024: 11 steps
lem-comm-CX31-TOFF024 : WsL → ⟪ (ℓ "乳亝") ⟫ʷ ≈ ⟪ (ℓ "亝乳") ⟫ʷ
lem-comm-CX31-TOFF024 c4 = derive (ℓ "乳亝") (ℓ "亝乳")
  (re 1 1 (ℓ "乊乼乥亍乥乼乊") ∷
   rw 0 (q88 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "了") ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (ℓ "乼乶乼") ∷
   rw 7 (q3 c4) ∷
   rw 6 (q90 c4) ∷
   re 0 7 (ℓ "亝") ∷ []) Eq.refl

-- comm CCZ134 CS02: 23 steps
lem-comm-CCZ134-CS02 : WsL → ⟪ (ℓ "京丯") ⟫ʷ ≈ ⟪ (ℓ "丯京") ⟫ʷ
lem-comm-CCZ134-CS02 c4 = derive (ℓ "京丯") (ℓ "丯京")
  (re 0 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "丶") ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "亨") ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw 6 (q8 c4) ∷
   re 7 1 (ℓ "乥亨乥") ∷
   rw 9 (q1 c4) ∷
   re 8 1 (ℓ "乼交乼") ∷
   rw 10 (q3 c4) ∷
   re 2 7 (ℓ "丽") ∷
   re 2 1 (ℓ "乼丶乼") ∷
   rw 1 (q3 c4) ∷
   re 1 1 (ℓ "乥丯乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "京") ∷ []) Eq.refl

-- comm TOFF312 CX04: 13 steps
lem-comm-TOFF312-CX04 : WsL → ⟪ (ℓ "产乁") ⟫ʷ ≈ ⟪ (ℓ "乁产") ⟫ʷ
lem-comm-TOFF312-CX04 c4 = derive (ℓ "产乁") (ℓ "乁产")
  (re 1 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "享") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亯") ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 1 (ℓ "乥享乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼产乼") ∷
   rw 8 (q3 c4) ∷
   re 0 7 (ℓ "乁") ∷ []) Eq.refl

-- comm CZ13 TOFF204: 11 steps
lem-comm-CZ13-TOFF204 : WsL → ⟪ (ℓ "乐亞") ⟫ʷ ≈ ⟪ (ℓ "亞乐") ⟫ʷ
lem-comm-CZ13-TOFF204 c4 = derive (ℓ "乐亞") (ℓ "亞乐")
  (re 1 1 (ℓ "乊乼乥于乥乼乊") ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (ℓ "乫") ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   re 5 1 (ℓ "乼乤乼") ∷
   rw 7 (q3 c4) ∷
   rw 6 (q19 c4) ∷
   re 0 7 (ℓ "亞") ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = wlE 10 c4
  q92 : WsL → Eqn
  q92 c4 = wlE 16 c4

-- resp CX03 at 2: 4 steps
lem-resp-CX03-at-2 : WsL → ⟪ (ℓ "为") ⟫ʷ ≈ ⟪ (ℓ "乊丫乒丫乊") ⟫ʷ
lem-resp-CX03-at-2 c4 = derive (ℓ "为") (ℓ "乊丫乒丫乊")
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q91 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q92 c4) ∷ []) Eq.refl

-- comm push SWAP04 sw2 L: 7 steps
lem-comm-push-SWAP04-sw2-L : WsL → ⟪ (ℓ "乀乥") ⟫ʷ ≈ ⟪ (ℓ "乥乀") ⟫ʷ
lem-comm-push-SWAP04-sw2-L c4 = derive (ℓ "乀乥") (ℓ "乥乀")
  (re 0 1 (ℓ "乼乥乊丫乊乥乼") ∷
   rw 5 (q46 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   re 1 7 (ℓ "乀") ∷ []) Eq.refl

-- comm SWAP14 BOX(2;30): 9 steps
lem-comm-SWAP14-BOX⟨2·30⟩ : WsL → ⟪ (ℓ "乘伷") ⟫ʷ ≈ ⟪ (ℓ "伷乘") ⟫ʷ
lem-comm-SWAP14-BOX⟨2·30⟩ c4 = derive (ℓ "乘伷") (ℓ "伷乘")
  (re 1 1 (ℓ "丸") ∷
   re 1 1 (ℓ "乥乊个乊乥") ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 4 (q67 c4) ∷
   re 0 5 (ℓ "丸") ∷
   re 0 1 (ℓ "伷") ∷ []) Eq.refl

-- comm CX21 TOFF034: 15 steps
lem-comm-CX21-TOFF034 : WsL → ⟪ (ℓ "也亡") ⟫ʷ ≈ ⟪ (ℓ "亡也") ⟫ʷ
lem-comm-CX21-TOFF034 c4 = derive (ℓ "也亡") (ℓ "亡也")
  (re 1 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乳") ∷
   rw 1 (q88 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "了") ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (ℓ "乼乶乼") ∷
   rw 8 (q3 c4) ∷
   rw 7 (q90 c4) ∷
   re 8 1 (ℓ "乥也乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亡") ∷ []) Eq.refl

-- comm CCZ124 CS03: 9 steps
lem-comm-CCZ124-CS03 : WsL → ⟪ (ℓ "亨丶") ⟫ʷ ≈ ⟪ (ℓ "丶亨") ⟫ʷ
lem-comm-CCZ124-CS03 c4 = derive (ℓ "亨丶") (ℓ "丶亨")
  (re 1 1 (ℓ "乥乊丨乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "京") ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 3 (q8 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "丶") ∷ []) Eq.refl

-- comm CCZ024 CX31: 11 steps
lem-comm-CCZ024-CX31 : WsL → ⟪ (ℓ "亜乳") ⟫ʷ ≈ ⟪ (ℓ "乳亜") ⟫ʷ
lem-comm-CCZ024-CX31 c4 = derive (ℓ "亜乳") (ℓ "乳亜")
  (re 0 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw⁻ 6 (q90 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "了") ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   re 2 1 (ℓ "乼乶乼") ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   re 1 7 (ℓ "亜") ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (ℓ "亍乽") (ℓ "乽亍") (c₃ (Toff) (CX₀₁))

-- comm TOFF034 CX12: 15 steps
lem-comm-TOFF034-CX12 : WsL → ⟪ (ℓ "亡之") ⟫ʷ ≈ ⟪ (ℓ "之亡") ⟫ʷ
lem-comm-TOFF034-CX12 c4 = derive (ℓ "亡之") (ℓ "之亡")
  (re 0 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乒") ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乭") ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q93 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   re 3 1 (ℓ "乼书乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   re 1 1 (ℓ "乥之乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亡") ∷ []) Eq.refl

-- comm CCZ014 CX23: 9 steps
lem-comm-CCZ014-CX23 : WsL → ⟪ (ℓ "五书") ⟫ʷ ≈ ⟪ (ℓ "书五") ⟫ʷ
lem-comm-CCZ014-CX23 c4 = derive (ℓ "五书") (ℓ "书五")
  (re 0 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乭") ∷
   rw⁻ 3 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   re 1 1 (ℓ "乼书乼") ∷
   rw 0 (q3 c4) ∷
   re 1 5 (ℓ "五") ∷ []) Eq.refl

-- comm CX23 TOFF014: 9 steps
lem-comm-CX23-TOFF014 : WsL → ⟪ (ℓ "书井") ⟫ʷ ≈ ⟪ (ℓ "井书") ⟫ʷ
lem-comm-CX23-TOFF014 c4 = derive (ℓ "书井") (ℓ "井书")
  (re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "乭") ∷
   rw 1 (q78 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q76 c4) ∷
   re 4 1 (ℓ "乼书乼") ∷
   rw 6 (q3 c4) ∷
   re 0 5 (ℓ "井") ∷ []) Eq.refl

-- comm CCZ034 CS12: 15 steps
lem-comm-CCZ034-CS12 : WsL → ⟪ (ℓ "亠乇") ⟫ʷ ≈ ⟪ (ℓ "乇亠") ⟫ʷ
lem-comm-CCZ034-CS12 c4 = derive (ℓ "亠乇") (ℓ "乇亠")
  (re 0 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乎") ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乩") ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   re 3 1 (ℓ "乼乢乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   re 1 1 (ℓ "乥乇乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亠") ∷ []) Eq.refl

-- comm TOFF013 CS24: 15 steps
lem-comm-TOFF013-CS24 : WsL → ⟪ (ℓ "云乩") ⟫ʷ ≈ ⟪ (ℓ "乩云") ⟫ʷ
lem-comm-TOFF013-CS24 c4 = derive (ℓ "云乩") (ℓ "乩云")
  (re 1 1 (ℓ "乼乢乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "井") ∷
   re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乩") ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (ℓ "乼乢乼") ∷
   rw 1 (q3 c4) ∷
   re 2 5 (ℓ "井") ∷
   re 2 1 (ℓ "乼云乼") ∷
   rw 4 (q3 c4) ∷
   re 0 3 (ℓ "乩") ∷ []) Eq.refl

-- comm TOFF014 CX23: 9 steps
lem-comm-TOFF014-CX23 : WsL → ⟪ (ℓ "井书") ⟫ʷ ≈ ⟪ (ℓ "书井") ⟫ʷ
lem-comm-TOFF014-CX23 c4 = derive (ℓ "井书") (ℓ "书井")
  (re 0 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (ℓ "乭") ∷
   rw⁻ 3 (q76 c4) ∷
   rw 2 (q93 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   re 1 1 (ℓ "乼书乼") ∷
   rw 0 (q3 c4) ∷
   re 1 5 (ℓ "井") ∷ []) Eq.refl

-- comm CCZ024 CS13: 11 steps
lem-comm-CCZ024-CS13 : WsL → ⟪ (ℓ "亜乎") ⟫ʷ ≈ ⟪ (ℓ "乎亜") ⟫ʷ
lem-comm-CCZ024-CS13 c4 = derive (ℓ "亜乎") (ℓ "乎亜")
  (re 0 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw⁻ 6 (q50 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乩") ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q39 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (ℓ "乼乢乼") ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   re 1 7 (ℓ "亜") ∷ []) Eq.refl

-- comm CCZ024 CSd13: 11 steps
lem-comm-CCZ024-CSd13 : WsL → ⟪ (ℓ "亜乏") ⟫ʷ ≈ ⟪ (ℓ "乏亜") ⟫ʷ
lem-comm-CCZ024-CSd13 c4 = derive (ℓ "亜乏") (ℓ "乏亜")
  (re 0 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q6 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 7 (ℓ "亜") ∷ []) Eq.refl

-- comm TOFF013 CX24: 15 steps
lem-comm-TOFF013-CX24 : WsL → ⟪ (ℓ "云乭") ⟫ʷ ≈ ⟪ (ℓ "乭云") ⟫ʷ
lem-comm-TOFF013-CX24 c4 = derive (ℓ "云乭") (ℓ "乭云")
  (re 1 1 (ℓ "乼书乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "井") ∷
   re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乭") ∷
   rw⁻ 4 (q76 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 2 (q78 c4) ∷
   re 2 1 (ℓ "乼书乼") ∷
   rw 1 (q3 c4) ∷
   re 2 5 (ℓ "井") ∷
   re 2 1 (ℓ "乼云乼") ∷
   rw 4 (q3 c4) ∷
   re 0 3 (ℓ "乭") ∷ []) Eq.refl

-- comm CCZ034 CX12: 15 steps
lem-comm-CCZ034-CX12 : WsL → ⟪ (ℓ "亠之") ⟫ʷ ≈ ⟪ (ℓ "之亠") ⟫ʷ
lem-comm-CCZ034-CX12 c4 = derive (ℓ "亠之") (ℓ "之亠")
  (re 0 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乒") ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乭") ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   re 3 1 (ℓ "乼书乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   re 1 1 (ℓ "乥之乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亠") ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = wlE 75 c4
  q95 : WsL → Eqn
  q95 c4 = eqn (ℓ "个乥") (ℓ "乥个") (c₂ (CZ) (Swap))
  q96 : WsL → Eqn
  q96 c4 = wlE 96 c4

-- comm SWAP12 BOX(3;04): 13 steps
lem-comm-SWAP12-BOX⟨3·04⟩ : WsL → ⟪ (ℓ "乊以") ⟫ʷ ≈ ⟪ (ℓ "以乊") ⟫ʷ
lem-comm-SWAP12-BOX⟨3·04⟩ c4 = derive (ℓ "乊以") (ℓ "以乊")
  (re 1 1 (ℓ "丿") ∷
   re 1 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乑") ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   re 5 1 (ℓ "乥乊乥") ∷
   rw 7 (q1 c4) ∷
   rw 6 (q41 c4) ∷
   re 0 7 (ℓ "丿") ∷
   re 0 1 (ℓ "以") ∷ []) Eq.refl

-- comm TOFF213 CS04: 13 steps
lem-comm-TOFF213-CS04 : WsL → ⟪ (ℓ "亦丽") ⟫ʷ ≈ ⟪ (ℓ "丽亦") ⟫ʷ
lem-comm-TOFF213-CS04 c4 = derive (ℓ "亦丽") (ℓ "丽亦")
  (re 1 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (ℓ "亪") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亮") ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 1 (ℓ "乥亪乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼亦乼") ∷
   rw 8 (q3 c4) ∷
   re 0 7 (ℓ "丽") ∷ []) Eq.refl

-- comm CS14 TOFF203: 7 steps
lem-comm-CS14-TOFF203 : WsL → ⟪ (ℓ "乕亚") ⟫ʷ ≈ ⟪ (ℓ "亚乕") ⟫ʷ
lem-comm-CS14-TOFF203 c4 = derive (ℓ "乕亚") (ℓ "亚乕")
  (re 1 1 (ℓ "乊乥于乥乊") ∷
   rw 0 (q38 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q40 c4) ∷
   re 0 5 (ℓ "亚") ∷ []) Eq.refl

-- comm CCZ124 CX03: 9 steps
lem-comm-CCZ124-CX03 : WsL → ⟪ (ℓ "亨为") ⟫ʷ ≈ ⟪ (ℓ "为亨") ⟫ʷ
lem-comm-CCZ124-CX03 c4 = derive (ℓ "亨为") (ℓ "为亨")
  (re 1 1 (ℓ "乥乊丬乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "京") ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 3 (q8 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "为") ∷ []) Eq.refl

-- comm CCZ034 CX21: 15 steps
lem-comm-CCZ034-CX21 : WsL → ⟪ (ℓ "亠也") ⟫ʷ ≈ ⟪ (ℓ "也亠") ⟫ʷ
lem-comm-CCZ034-CX21 c4 = derive (ℓ "亠也") (ℓ "也亠")
  (re 0 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乳") ∷
   rw⁻ 7 (q90 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "了") ∷
   rw⁻ 5 (q54 c4) ∷
   rw 4 (q53 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   re 3 1 (ℓ "乼乶乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q88 c4) ∷
   re 1 1 (ℓ "乥也乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亠") ∷ []) Eq.refl

-- comm SWAP12 BOX(3;40): 13 steps
lem-comm-SWAP12-BOX⟨3·40⟩ : WsL → ⟪ (ℓ "乊佶") ⟫ʷ ≈ ⟪ (ℓ "佶乊") ⟫ʷ
lem-comm-SWAP12-BOX⟨3·40⟩ c4 = derive (ℓ "乊佶") (ℓ "佶乊")
  (re 1 1 (ℓ "丿") ∷
   re 1 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "乑") ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   re 5 1 (ℓ "乥乊乥") ∷
   rw 7 (q1 c4) ∷
   rw 6 (q41 c4) ∷
   re 0 7 (ℓ "丿") ∷
   re 0 1 (ℓ "佶") ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = wlE 50 c4
  q98 : WsL → Eqn
  q98 c4 = eqn (ℓ "亏乽") (ℓ "乽亏") (c₃ (Toffᵗ) (CX₀₁))
  q99 : WsL → Eqn
  q99 c4 = wlE 51 c4

-- comm CX14 TOFF302: 7 steps
lem-comm-CX14-TOFF302 : WsL → ⟪ (ℓ "乙些") ⟫ʷ ≈ ⟪ (ℓ "些乙") ⟫ʷ
lem-comm-CX14-TOFF302 c4 = derive (ℓ "乙些") (ℓ "些乙")
  (re 1 1 (ℓ "乊乥亏乥乊") ∷
   rw 0 (q97 c4) ∷
   rw 1 (q78 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q99 c4) ∷
   re 0 5 (ℓ "些") ∷ []) Eq.refl

-- comm TOFF024 CS13: 11 steps
lem-comm-TOFF024-CS13 : WsL → ⟪ (ℓ "亝乎") ⟫ʷ ≈ ⟪ (ℓ "乎亝") ⟫ʷ
lem-comm-TOFF024-CS13 c4 = derive (ℓ "亝乎") (ℓ "乎亝")
  (re 0 1 (ℓ "乊乼乥亍乥乼乊") ∷
   rw⁻ 6 (q50 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (ℓ "乩") ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   re 2 1 (ℓ "乼乢乼") ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   re 1 7 (ℓ "亝") ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = wlE 97 c4
  q101 : WsL → Eqn
  q101 c4 = wlE 98 c4

-- resp SWAP03 at 2: 4 steps
lem-resp-SWAP03-at-2 : WsL → ⟪ (ℓ "丹") ⟫ʷ ≈ ⟪ (ℓ "乊丫乑丫乊") ⟫ʷ
lem-resp-SWAP03-at-2 c4 = derive (ℓ "丹") (ℓ "乊丫乑丫乊")
  (rw⁻ 1 (q28 c4) ∷
   rw 0 (q100 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q101 c4) ∷ []) Eq.refl

-- resp SWAP03 at 1: 2 steps
lem-resp-SWAP03-at-1 : WsL → ⟪ (ℓ "丹") ⟫ʷ ≈ ⟪ (ℓ "丫乑丫") ⟫ʷ
lem-resp-SWAP03-at-1 c4 = derive (ℓ "丹") (ℓ "丫乑丫")
  (rw⁻ 1 (q30 c4) ∷
   rw⁻ 0 (q101 c4) ∷ []) Eq.refl

-- comm CCZ134 CX02: 23 steps
lem-comm-CCZ134-CX02 : WsL → ⟪ (ℓ "京丳") ⟫ʷ ≈ ⟪ (ℓ "丳京") ⟫ʷ
lem-comm-CCZ134-CX02 c4 = derive (ℓ "京丳") (ℓ "丳京")
  (re 0 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "为") ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (ℓ "乁") ∷
   re 3 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (ℓ "亨") ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 6 (q8 c4) ∷
   re 7 1 (ℓ "乥亨乥") ∷
   rw 9 (q1 c4) ∷
   re 8 1 (ℓ "乼交乼") ∷
   rw 10 (q3 c4) ∷
   re 2 7 (ℓ "乁") ∷
   re 2 1 (ℓ "乼为乼") ∷
   rw 1 (q3 c4) ∷
   re 1 1 (ℓ "乥丳乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "京") ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (ℓ "于乽") (ℓ "乽于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₀₁))

-- comm TOFF304 CX12: 15 steps
lem-comm-TOFF304-CX12 : WsL → ⟪ (ℓ "亢之") ⟫ʷ ≈ ⟪ (ℓ "之亢") ⟫ʷ
lem-comm-TOFF304-CX12 c4 = derive (ℓ "亢之") (ℓ "之亢")
  (re 0 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乒") ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (ℓ "乭") ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   re 3 1 (ℓ "乼书乼") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   re 1 1 (ℓ "乥之乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亢") ∷ []) Eq.refl
