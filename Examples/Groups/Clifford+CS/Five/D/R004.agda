{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)

module Examples.Groups.Clifford+CS.Five.D.R004 where

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
  q2 c4 = wlE 4 c4
  q3 : WsL → Eqn
  q3 c4 = wlE 84 c4
  q4 : WsL → Eqn
  q4 c4 = eqn (ℓ "乄亳") (ℓ "亳乄") (c₂ (CX₁₀) (Toffᵗ))
  q5 : WsL → Eqn
  q5 c4 = wlE 85 c4

-- comm CX20 TOFF413: 23 steps
lem-comm-CX20-TOFF413 : WsL → ⟪ (ℓ "乜亯") ⟫ʷ ≈ ⟪ (ℓ "亯乜") ⟫ʷ
lem-comm-CX20-TOFF413 c4 = derive (ℓ "乜亯") (ℓ "亯乜")
  (re 1 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "买") ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "亀") ∷
   re 2 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "享") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "亯") ∷
   rw 6 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼产乼") ∷
   rw 2 (q2 c4) ∷
   re 3 7 (ℓ "亀") ∷
   re 3 1 (ℓ "乼买乼") ∷
   rw 5 (q2 c4) ∷
   re 4 1 (ℓ "乥乜乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亯") ∷ []) Eq.refl

-- comm TOFF413 CX20: 23 steps
lem-comm-TOFF413-CX20 : WsL → ⟪ (ℓ "亯乜") ⟫ʷ ≈ ⟪ (ℓ "乜亯") ⟫ʷ
lem-comm-TOFF413-CX20 c4 = derive (ℓ "亯乜") (ℓ "乜亯")
  (re 0 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "买") ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "亀") ∷
   re 3 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (ℓ "享") ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 7 1 (ℓ "乥享乥") ∷
   rw 9 (q1 c4) ∷
   re 8 1 (ℓ "乼产乼") ∷
   rw 10 (q2 c4) ∷
   re 2 7 (ℓ "亀") ∷
   re 2 1 (ℓ "乼买乼") ∷
   rw 1 (q2 c4) ∷
   re 1 1 (ℓ "乥乜乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "亯") ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = wlE 44 c4
  q7 : WsL → Eqn
  q7 c4 = eqn (ℓ "中亰") (ℓ "亰中") (c₂ (CK₀₁) (CCZ))
  q8 : WsL → Eqn
  q8 c4 = wlE 37 c4

-- comm CK03 CCZ124: 9 steps
lem-comm-CK03-CCZ124 : WsL → ⟪ (ℓ "主亨") ⟫ʷ ≈ ⟪ (ℓ "亨主") ⟫ʷ
lem-comm-CK03-CCZ124 c4 = derive (ℓ "主亨") (ℓ "亨主")
  (re 0 1 (ℓ "乥乊中乊乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 3 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 1 (q8 c4) ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "主") ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = wlE 18 c4
  q10 : WsL → Eqn
  q10 c4 = wlE 152 c4

-- resp CK03 at 1: 2 steps
lem-resp-CK03-at-1 : WsL → ⟪ (ℓ "主") ⟫ʷ ≈ ⟪ (ℓ "丫乓丫") ⟫ʷ
lem-resp-CK03-at-1 c4 = derive (ℓ "主") (ℓ "丫乓丫")
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q10 c4) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = wlE 29 c4
  q12 : WsL → Eqn
  q12 c4 = wlE 9 c4
  q13 : WsL → Eqn
  q13 c4 = eqn (ℓ "亏乺") (ℓ "乺亏") (c₃ (Toffᵗ) (CS • CS • CS))
  q14 : WsL → Eqn
  q14 c4 = wlE 12 c4
  q15 : WsL → Eqn
  q15 c4 = wlE 28 c4

-- comm TOFF403 CSd12: 15 steps
lem-comm-TOFF403-CSd12 : WsL → ⟪ (ℓ "亣么") ⟫ʷ ≈ ⟪ (ℓ "么亣") ⟫ʷ
lem-comm-TOFF403-CSd12 c4 = derive (ℓ "亣么") (ℓ "么亣")
  (re 0 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乏") ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "乪") ∷
   rw⁻ 5 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 2 (q2 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   re 1 1 (ℓ "乥么乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亣") ∷ []) Eq.refl

-- comm CCZ124 CK03: 9 steps
lem-comm-CCZ124-CK03 : WsL → ⟪ (ℓ "亨主") ⟫ʷ ≈ ⟪ (ℓ "主亨") ⟫ʷ
lem-comm-CCZ124-CK03 c4 = derive (ℓ "亨主") (ℓ "主亨")
  (re 1 1 (ℓ "乥乊中乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "京") ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw 3 (q6 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "主") ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (ℓ "丨亳") (ℓ "亳丨") (c₂ (CS) (Toffᵗ))

-- comm CS02 TOFF413: 23 steps
lem-comm-CS02-TOFF413 : WsL → ⟪ (ℓ "丯亯") ⟫ʷ ≈ ⟪ (ℓ "亯丯") ⟫ʷ
lem-comm-CS02-TOFF413 c4 = derive (ℓ "丯亯") (ℓ "亯丯")
  (re 1 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丶") ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "享") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "亯") ∷
   rw 6 (q3 c4) ∷
   rw 5 (q16 c4) ∷
   rw 4 (q5 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼产乼") ∷
   rw 2 (q2 c4) ∷
   re 3 7 (ℓ "丽") ∷
   re 3 1 (ℓ "乼丶乼") ∷
   rw 5 (q2 c4) ∷
   re 4 1 (ℓ "乥丯乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亯") ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = wlE 46 c4
  q18 : WsL → Eqn
  q18 c4 = wlE 11 c4
  q19 : WsL → Eqn
  q19 c4 = eqn (ℓ "亏乹") (ℓ "乹亏") (c₃ (Toffᵗ) (CS))
  q20 : WsL → Eqn
  q20 c4 = wlE 8 c4
  q21 : WsL → Eqn
  q21 c4 = wlE 47 c4

-- comm CS12 TOFF403: 15 steps
lem-comm-CS12-TOFF403 : WsL → ⟪ (ℓ "乇亣") ⟫ʷ ≈ ⟪ (ℓ "亣乇") ⟫ʷ
lem-comm-CS12-TOFF403 c4 = derive (ℓ "乇亣") (ℓ "亣乇")
  (re 1 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (ℓ "乩") ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (ℓ "乼乢乼") ∷
   rw 8 (q2 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亣") ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = wlE 69 c4
  q23 : WsL → Eqn
  q23 c4 = wlE 58 c4
  q24 : WsL → Eqn
  q24 c4 = eqn (ℓ "于争") (ℓ "争于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))
  q25 : WsL → Eqn
  q25 c4 = wlE 59 c4
  q26 : WsL → Eqn
  q26 c4 = wlE 89 c4

-- comm CX41 TOFF203: 7 steps
lem-comm-CX41-TOFF203 : WsL → ⟪ (ℓ "亃亚") ⟫ʷ ≈ ⟪ (ℓ "亚亃") ⟫ʷ
lem-comm-CX41-TOFF203 c4 = derive (ℓ "亃亚") (ℓ "亚亃")
  (re 1 1 (ℓ "乊乥于乥乊") ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   re 0 5 (ℓ "亚") ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (ℓ "个亳") (ℓ "亳个") (c₂ (CZ) (Toffᵗ))

-- comm CZ02 TOFF413: 23 steps
lem-comm-CZ02-TOFF413 : WsL → ⟪ (ℓ "丱亯") ⟫ʷ ≈ ⟪ (ℓ "亯丱") ⟫ʷ
lem-comm-CZ02-TOFF413 c4 = derive (ℓ "丱亯") (ℓ "亯丱")
  (re 1 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丸") ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "丿") ∷
   re 2 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (ℓ "享") ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (ℓ "亯") ∷
   rw 6 (q3 c4) ∷
   rw 5 (q27 c4) ∷
   rw 4 (q5 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 3 (q1 c4) ∷
   re 3 1 (ℓ "乼产乼") ∷
   rw 2 (q2 c4) ∷
   re 3 7 (ℓ "丿") ∷
   re 3 1 (ℓ "乼丸乼") ∷
   rw 5 (q2 c4) ∷
   re 4 1 (ℓ "乥丱乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "亯") ∷ []) Eq.refl

-- comm TOFF413 CS02: 23 steps
lem-comm-TOFF413-CS02 : WsL → ⟪ (ℓ "亯丯") ⟫ʷ ≈ ⟪ (ℓ "丯亯") ⟫ʷ
lem-comm-TOFF413-CS02 c4 = derive (ℓ "亯丯") (ℓ "丯亯")
  (re 0 1 (ℓ "乥乼产乼乥") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "丶") ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (ℓ "享") ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 7 1 (ℓ "乥享乥") ∷
   rw 9 (q1 c4) ∷
   re 8 1 (ℓ "乼产乼") ∷
   rw 10 (q2 c4) ∷
   re 2 7 (ℓ "丽") ∷
   re 2 1 (ℓ "乼丶乼") ∷
   rw 1 (q2 c4) ∷
   re 1 1 (ℓ "乥丯乥") ∷
   rw 0 (q1 c4) ∷
   re 1 5 (ℓ "亯") ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = wlE 153 c4

-- resp CK02 at 1: 2 steps
lem-resp-CK02-at-1 : WsL → ⟪ (ℓ "临") ⟫ʷ ≈ ⟪ (ℓ "丫乌丫") ⟫ʷ
lem-resp-CK02-at-1 c4 = derive (ℓ "临") (ℓ "丫乌丫")
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = wlE 75 c4
  q30 : WsL → Eqn
  q30 c4 = eqn (ℓ "个乥") (ℓ "乥个") (c₂ (CZ) (Swap))
  q31 : WsL → Eqn
  q31 c4 = wlE 96 c4

-- comm SWAP13 BOX(4;20): 7 steps
lem-comm-SWAP13-BOX⟨4·20⟩ : WsL → ⟪ (ℓ "乑佚") ⟫ʷ ≈ ⟪ (ℓ "佚乑") ⟫ʷ
lem-comm-SWAP13-BOX⟨4·20⟩ c4 = derive (ℓ "乑佚") (ℓ "佚乑")
  (re 1 1 (ℓ "丱") ∷
   re 1 1 (ℓ "乊个乊") ∷
   rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   re 0 3 (ℓ "丱") ∷
   re 0 1 (ℓ "佚") ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (ℓ "亏争") (ℓ "争亏") (c₃ (Toffᵗ) (CX₁₀))

-- comm CX41 TOFF302: 7 steps
lem-comm-CX41-TOFF302 : WsL → ⟪ (ℓ "亃些") ⟫ʷ ≈ ⟪ (ℓ "些亃") ⟫ʷ
lem-comm-CX41-TOFF302 c4 = derive (ℓ "亃些") (ℓ "些亃")
  (re 1 1 (ℓ "乊乥亏乥乊") ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   re 0 5 (ℓ "些") ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = wlE 22 c4
  q34 : WsL → Eqn
  q34 c4 = wlE 21 c4
  q35 : WsL → Eqn
  q35 c4 = eqn (ℓ "亏乽") (ℓ "乽亏") (c₃ (Toffᵗ) (CX₀₁))
  q36 : WsL → Eqn
  q36 c4 = wlE 20 c4
  q37 : WsL → Eqn
  q37 c4 = wlE 19 c4

-- comm TOFF403 CX12: 15 steps
lem-comm-TOFF403-CX12 : WsL → ⟪ (ℓ "亣之") ⟫ʷ ≈ ⟪ (ℓ "之亣") ⟫ʷ
lem-comm-TOFF403-CX12 c4 = derive (ℓ "亣之") (ℓ "之亣")
  (re 0 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (ℓ "乒") ∷
   rw⁻ 7 (q33 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (ℓ "乭") ∷
   rw⁻ 5 (q34 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (ℓ "乼书乼") ∷
   rw 2 (q2 c4) ∷
   rw⁻ 1 (q37 c4) ∷
   re 1 1 (ℓ "乥之乥") ∷
   rw 0 (q1 c4) ∷
   re 1 9 (ℓ "亣") ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = wlE 6 c4
  q39 : WsL → Eqn
  q39 c4 = wlE 154 c4

-- resp CK03 at 2: 4 steps
lem-resp-CK03-at-2 : WsL → ⟪ (ℓ "主") ⟫ʷ ≈ ⟪ (ℓ "乊丫乓丫乊") ⟫ʷ
lem-resp-CK03-at-2 c4 = derive (ℓ "主") (ℓ "乊丫乓丫乊")
  (rw⁻ 1 (q38 c4) ∷
   rw 0 (q39 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = wlE 57 c4
  q41 : WsL → Eqn
  q41 c4 = wlE 60 c4

-- comm CX21 TOFF403: 15 steps
lem-comm-CX21-TOFF403 : WsL → ⟪ (ℓ "也亣") ⟫ʷ ≈ ⟪ (ℓ "亣也") ⟫ʷ
lem-comm-CX21-TOFF403 c4 = derive (ℓ "也亣") (ℓ "亣也")
  (re 1 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乳") ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (ℓ "了") ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q25 c4) ∷
   re 6 1 (ℓ "乼乶乼") ∷
   rw 8 (q2 c4) ∷
   rw 7 (q41 c4) ∷
   re 8 1 (ℓ "乥也乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亣") ∷ []) Eq.refl

-- comm CX12 TOFF403: 15 steps
lem-comm-CX12-TOFF403 : WsL → ⟪ (ℓ "之亣") ⟫ʷ ≈ ⟪ (ℓ "亣之") ⟫ʷ
lem-comm-CX12-TOFF403 c4 = derive (ℓ "之亣") (ℓ "亣之")
  (re 1 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乒") ∷
   rw 1 (q37 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 3 3 (ℓ "乭") ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 5 (q34 c4) ∷
   re 6 1 (ℓ "乼书乼") ∷
   rw 8 (q2 c4) ∷
   rw 7 (q33 c4) ∷
   re 8 1 (ℓ "乥之乥") ∷
   rw 10 (q1 c4) ∷
   re 0 9 (ℓ "亣") ∷ []) Eq.refl

-- comm SWAP12 BOX(4;30): 11 steps
lem-comm-SWAP12-BOX⟨4·30⟩ : WsL → ⟪ (ℓ "乊使") ⟫ʷ ≈ ⟪ (ℓ "使乊") ⟫ʷ
lem-comm-SWAP12-BOX⟨4·30⟩ c4 = derive (ℓ "乊使") (ℓ "使乊")
  (re 1 1 (ℓ "丸") ∷
   re 1 1 (ℓ "乥乊个乊乥") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乑") ∷
   rw⁻ 1 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   re 4 1 (ℓ "乥乊乥") ∷
   rw 6 (q1 c4) ∷
   re 0 5 (ℓ "丸") ∷
   re 0 1 (ℓ "使") ∷ []) Eq.refl

-- comm CX31 TOFF402: 11 steps
lem-comm-CX31-TOFF402 : WsL → ⟪ (ℓ "乳亟") ⟫ʷ ≈ ⟪ (ℓ "亟乳") ⟫ʷ
lem-comm-CX31-TOFF402 c4 = derive (ℓ "乳亟") (ℓ "亟乳")
  (re 1 1 (ℓ "乊乼乥亏乥乼乊") ∷
   rw 0 (q40 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (ℓ "了") ∷
   rw 2 (q23 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q25 c4) ∷
   re 5 1 (ℓ "乼乶乼") ∷
   rw 7 (q2 c4) ∷
   rw 6 (q41 c4) ∷
   re 0 7 (ℓ "亟") ∷ []) Eq.refl

-- comm TOFF312 CX40: 13 steps
lem-comm-TOFF312-CX40 : WsL → ⟪ (ℓ "产亀") ⟫ʷ ≈ ⟪ (ℓ "亀产") ⟫ʷ
lem-comm-TOFF312-CX40 c4 = derive (ℓ "产亀") (ℓ "亀产")
  (re 1 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (ℓ "享") ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亯") ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 5 1 (ℓ "乥享乥") ∷
   rw 7 (q1 c4) ∷
   re 6 1 (ℓ "乼产乼") ∷
   rw 8 (q2 c4) ∷
   re 0 7 (ℓ "亀") ∷ []) Eq.refl
