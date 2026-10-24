{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)

module Examples.Groups.Clifford+CS.Five.D.R001 where

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
  q1 c4 = eqn (ℓ "乊乼") (ℓ "乼乊") (c₃ (Swap ↑) (Swap))
  q2 : WsL → Eqn
  q2 c4 = wlE 1 c4

-- comm push CS04 sw1 R: 5 steps
lem-comm-push-CS04-sw1-R : WsL → ⟪ (ℓ "乊丽") ⟫ʷ ≈ ⟪ (ℓ "丽乊") ⟫ʷ
lem-comm-push-CS04-sw1-R c4 = derive (ℓ "乊丽") (ℓ "丽乊")
  (re 1 1 (ℓ "乼丶乼") ∷
   rw 0 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 2 (q1 c4) ∷
   re 0 3 (ℓ "丽") ∷ []) Eq.refl

private
  q3 : WsL → Eqn
  q3 c4 = wlE 2 c4
  q4 : WsL → Eqn
  q4 c4 = eqn (ℓ "丨乼") (ℓ "乼丨") (c₂ (CS) (Swap ↑))

-- comm push CS04 sw2 R: 7 steps
lem-comm-push-CS04-sw2-R : WsL → ⟪ (ℓ "乥丽") ⟫ʷ ≈ ⟪ (ℓ "丽乥") ⟫ʷ
lem-comm-push-CS04-sw2-R c4 = derive (ℓ "乥丽") (ℓ "丽乥")
  (re 1 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw 0 (q3 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 0 7 (ℓ "丽") ∷ []) Eq.refl

-- comm push CS04 sw1 L: 5 steps
lem-comm-push-CS04-sw1-L : WsL → ⟪ (ℓ "丽乊") ⟫ʷ ≈ ⟪ (ℓ "乊丽") ⟫ʷ
lem-comm-push-CS04-sw1-L c4 = derive (ℓ "丽乊") (ℓ "乊丽")
  (re 0 1 (ℓ "乼丶乼") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丽") ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (ℓ "丫乼") (ℓ "乼丫") (c₂ (Swap) (Swap ↑))
  q6 : WsL → Eqn
  q6 c4 = wlE 15 c4

-- comm push CS04 sw0 L: 5 steps
lem-comm-push-CS04-sw0-L : WsL → ⟪ (ℓ "丽丫") ⟫ʷ ≈ ⟪ (ℓ "丫乕") ⟫ʷ
lem-comm-push-CS04-sw0-L c4 = derive (ℓ "丽丫") (ℓ "丫乕")
  (re 0 1 (ℓ "乼丶乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "乕") ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = wlE 3 c4
  q8 : WsL → Eqn
  q8 c4 = wlE 19 c4
  q9 : WsL → Eqn
  q9 c4 = wlE 4 c4
  q10 : WsL → Eqn
  q10 c4 = wlE 20 c4
  q11 : WsL → Eqn
  q11 c4 = eqn (ℓ "二乽") (ℓ "乽二") (c₃ (CCZ) (CX₀₁))
  q12 : WsL → Eqn
  q12 c4 = wlE 21 c4
  q13 : WsL → Eqn
  q13 c4 = wlE 22 c4

-- comm CX12 CCZ034: 15 steps
lem-comm-CX12-CCZ034 : WsL → ⟪ (ℓ "之亠") ⟫ʷ ≈ ⟪ (ℓ "亠之") ⟫ʷ
lem-comm-CX12-CCZ034 c4 = derive (ℓ "之亠") (ℓ "亠之")
  (re 1 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乒") ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乭") ∷
   rw 3 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 5 (q12 c4) ∷
   re 6 1 (ℓ "乼书乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q13 c4) ∷
   re 8 1 (ℓ "乥之乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亠") ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = wlE 18 c4
  q15 : WsL → Eqn
  q15 c4 = wlE 23 c4

-- resp CSd02 at 1: 2 steps
lem-resp-CSd02-at-1 : WsL → ⟪ (ℓ "丰") ⟫ʷ ≈ ⟪ (ℓ "丫么丫") ⟫ʷ
lem-resp-CSd02-at-1 c4 = derive (ℓ "丰") (ℓ "丫么丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q15 c4) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = wlE 24 c4

-- resp CS02 at 1: 2 steps
lem-resp-CS02-at-1 : WsL → ⟪ (ℓ "丯") ⟫ʷ ≈ ⟪ (ℓ "丫乇丫") ⟫ʷ
lem-resp-CS02-at-1 c4 = derive (ℓ "丯") (ℓ "丫乇丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = wlE 28 c4
  q18 : WsL → Eqn
  q18 c4 = wlE 12 c4
  q19 : WsL → Eqn
  q19 c4 = eqn (ℓ "亍乺") (ℓ "乺亍") (c₃ (Toff) (CS • CS • CS))
  q20 : WsL → Eqn
  q20 c4 = wlE 9 c4
  q21 : WsL → Eqn
  q21 c4 = wlE 29 c4

-- comm CSd12 TOFF034: 15 steps
lem-comm-CSd12-TOFF034 : WsL → ⟪ (ℓ "么亡") ⟫ʷ ≈ ⟪ (ℓ "亡么") ⟫ʷ
lem-comm-CSd12-TOFF034 c4 = derive (ℓ "么亡") (ℓ "亡么")
  (re 1 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乏") ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亡") ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = wlE 6 c4
  q23 : WsL → Eqn
  q23 c4 = wlE 30 c4

-- resp CCZ013 at 2: 5 steps
lem-resp-CCZ013-at-2 : WsL → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "乊丫交丫乊") ⟫ʷ
lem-resp-CCZ013-at-2 c4 = derive (ℓ "亐") (ℓ "乊丫交丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (ℓ "亘") ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = wlE 31 c4

-- resp TOFF103 at 2: 5 steps
lem-resp-TOFF103-at-2 : WsL → ⟪ (ℓ "互") ⟫ʷ ≈ ⟪ (ℓ "乊丫亦丫乊") ⟫ʷ
lem-resp-TOFF103-at-2 c4 = derive (ℓ "互") (ℓ "乊丫亦丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (ℓ "亚") ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q24 c4) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = wlE 32 c4
  q26 : WsL → Eqn
  q26 c4 = eqn (ℓ "丫乫") (ℓ "乫丫") (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- resp CZ14 at 2: 4 steps
lem-resp-CZ14-at-2 : WsL → ⟪ (ℓ "乗") ⟫ʷ ≈ ⟪ (ℓ "乊丫乫丫乊") ⟫ʷ
lem-resp-CZ14-at-2 c4 = derive (ℓ "乗") (ℓ "乊丫乫丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q26 c4) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = wlE 33 c4
  q28 : WsL → Eqn
  q28 c4 = wlE 34 c4
  q29 : WsL → Eqn
  q29 c4 = eqn (ℓ "二乻") (ℓ "乻二") (c₃ (CCZ) (CZ))
  q30 : WsL → Eqn
  q30 c4 = wlE 35 c4
  q31 : WsL → Eqn
  q31 c4 = wlE 36 c4

-- comm CZ12 CCZ034: 15 steps
lem-comm-CZ12-CCZ034 : WsL → ⟪ (ℓ "义亠") ⟫ʷ ≈ ⟪ (ℓ "亠义") ⟫ʷ
lem-comm-CZ12-CCZ034 c4 = derive (ℓ "义亠") (ℓ "亠义")
  (re 1 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乐") ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乫") ∷
   rw 3 (q28 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 5 (q30 c4) ∷
   re 6 1 (ℓ "乼乤乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q31 c4) ∷
   re 8 1 (ℓ "乥义乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亠") ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (ℓ "亍乻") (ℓ "乻亍") (c₃ (Toff) (CZ))

-- comm CZ12 TOFF034: 15 steps
lem-comm-CZ12-TOFF034 : WsL → ⟪ (ℓ "义亡") ⟫ʷ ≈ ⟪ (ℓ "亡义") ⟫ʷ
lem-comm-CZ12-TOFF034 c4 = derive (ℓ "义亡") (ℓ "亡义")
  (re 1 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乐") ∷
   rw 1 (q27 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乫") ∷
   rw 3 (q28 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q30 c4) ∷
   re 6 1 (ℓ "乼乤乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q31 c4) ∷
   re 8 1 (ℓ "乥义乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亡") ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = wlE 37 c4
  q34 : WsL → Eqn
  q34 c4 = eqn (ℓ "丫亰") (ℓ "亰丫") (c₂ (Swap) (CCZ))

-- resp CCZ134 at 2: 4 steps
lem-resp-CCZ134-at-2 : WsL → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乊丫亰丫乊") ⟫ʷ
lem-resp-CCZ134-at-2 c4 = derive (ℓ "京") (ℓ "乊丫亰丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q34 c4) ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = wlE 17 c4
  q36 : WsL → Eqn
  q36 c4 = wlE 13 c4
  q37 : WsL → Eqn
  q37 c4 = eqn (ℓ "丫乩") (ℓ "乩丫") (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- resp CS14 at 3: 6 steps
lem-resp-CS14-at-3 : WsL → ⟪ (ℓ "乕") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乩丫乊乥") ⟫ʷ
lem-resp-CS14-at-3 c4 = derive (ℓ "乕") (ℓ "乥乊丫乩丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q35 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q37 c4) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = wlE 38 c4
  q39 : WsL → Eqn
  q39 c4 = eqn (ℓ "丫亲") (ℓ "亲丫") (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))

-- resp TOFF314 at 2: 4 steps
lem-resp-TOFF314-at-2 : WsL → ⟪ (ℓ "亮") ⟫ʷ ≈ ⟪ (ℓ "乊丫亲丫乊") ⟫ʷ
lem-resp-TOFF314-at-2 c4 = derive (ℓ "亮") (ℓ "乊丫亲丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q39 c4) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (ℓ "丫书") (ℓ "书丫") (c₂ (Swap) (CX₀₁))

-- resp CX13 at 2: 4 steps
lem-resp-CX13-at-2 : WsL → ⟪ (ℓ "乒") ⟫ʷ ≈ ⟪ (ℓ "乊丫书丫乊") ⟫ʷ
lem-resp-CX13-at-2 c4 = derive (ℓ "乒") (ℓ "乊丫书丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q8 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q40 c4) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = wlE 42 c4

-- comm push CSd04 sw0 L: 5 steps
lem-comm-push-CSd04-sw0-L : WsL → ⟪ (ℓ "举丫") ⟫ʷ ≈ ⟪ (ℓ "丫乖") ⟫ʷ
lem-comm-push-CSd04-sw0-L c4 = derive (ℓ "举丫") (ℓ "丫乖")
  (re 0 1 (ℓ "乼丷乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "乖") ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (ℓ "于乺") (ℓ "乺于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))

-- comm TOFF204 CSd13: 11 steps
lem-comm-TOFF204-CSd13 : WsL → ⟪ (ℓ "亞乏") ⟫ʷ ≈ ⟪ (ℓ "乏亞") ⟫ʷ
lem-comm-TOFF204-CSd13 c4 = derive (ℓ "亞乏") (ℓ "乏亞")
  (re 0 1 (ℓ "乊乼乥于乥乼乊") ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q42 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   re 1 7 (ℓ "亞") ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = wlE 43 c4

-- comm push CSd04 sw1 L: 5 steps
lem-comm-push-CSd04-sw1-L : WsL → ⟪ (ℓ "举乊") ⟫ʷ ≈ ⟪ (ℓ "乊举") ⟫ʷ
lem-comm-push-CSd04-sw1-L c4 = derive (ℓ "举乊") (ℓ "乊举")
  (re 0 1 (ℓ "乼丷乼") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q43 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "举") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (ℓ "丫乣") (ℓ "乣丫") (c₂ (Swap) (CS • CS • CS))

-- resp CSd13 at 2: 4 steps
lem-resp-CSd13-at-2 : WsL → ⟪ (ℓ "乏") ⟫ʷ ≈ ⟪ (ℓ "乊丫乣丫乊") ⟫ʷ
lem-resp-CSd13-at-2 c4 = derive (ℓ "乏") (ℓ "乊丫乣丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q17 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q44 c4) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = wlE 16 c4

-- comm push CX04 sw0 L: 5 steps
lem-comm-push-CX04-sw0-L : WsL → ⟪ (ℓ "乁丫") ⟫ʷ ≈ ⟪ (ℓ "丫乙") ⟫ʷ
lem-comm-push-CX04-sw0-L c4 = derive (ℓ "乁丫") (ℓ "丫乙")
  (re 0 1 (ℓ "乼为乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q45 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "乙") ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = wlE 44 c4
  q47 : WsL → Eqn
  q47 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))

-- comm CX04 CCZ123: 13 steps
lem-comm-CX04-CCZ123 : WsL → ⟪ (ℓ "乁交") ⟫ʷ ≈ ⟪ (ℓ "交乁") ⟫ʷ
lem-comm-CX04-CCZ123 c4 = derive (ℓ "乁交") (ℓ "交乁")
  (re 0 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "亨") ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (ℓ "京") ∷
   rw⁻ 4 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 2 1 (ℓ "乥亨乥") ∷
   rw 1 (q7 c4) ∷
   re 1 1 (ℓ "乼交乼") ∷
   rw 0 (q9 c4) ∷
   re 1 7 (ℓ "乁") ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = wlE 45 c4
  q49 : WsL → Eqn
  q49 c4 = eqn (ℓ "丩亲") (ℓ "亲丩") (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))

-- comm CSd04 TOFF213: 13 steps
lem-comm-CSd04-TOFF213 : WsL → ⟪ (ℓ "举亦") ⟫ʷ ≈ ⟪ (ℓ "亦举") ⟫ʷ
lem-comm-CSd04-TOFF213 c4 = derive (ℓ "举亦") (ℓ "亦举")
  (re 0 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "亪") ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (ℓ "亮") ∷
   rw 4 (q48 c4) ∷
   rw 3 (q49 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q7 c4) ∷
   re 1 1 (ℓ "乼亦乼") ∷
   rw 0 (q9 c4) ∷
   re 1 7 (ℓ "举") ∷ []) Eq.refl

-- resp CS03 at 1: 2 steps
lem-resp-CS03-at-1 : WsL → ⟪ (ℓ "丶") ⟫ʷ ≈ ⟪ (ℓ "丫乎丫") ⟫ʷ
lem-resp-CS03-at-1 c4 = derive (ℓ "丶") (ℓ "丫乎丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (ℓ "二乺") (ℓ "乺二") (c₃ (CCZ) (CS • CS • CS))

-- comm CSd13 CCZ024: 11 steps
lem-comm-CSd13-CCZ024 : WsL → ⟪ (ℓ "乏亜") ⟫ʷ ≈ ⟪ (ℓ "亜乏") ⟫ʷ
lem-comm-CSd13-CCZ024 c4 = derive (ℓ "乏亜") (ℓ "亜乏")
  (re 1 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乪") ∷
   rw 2 (q18 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw 4 (q20 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q21 c4) ∷
   re 0 7 (ℓ "亜") ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = wlE 46 c4
  q52 : WsL → Eqn
  q52 c4 = wlE 11 c4
  q53 : WsL → Eqn
  q53 c4 = eqn (ℓ "二乹") (ℓ "乹二") (c₃ (CCZ) (CS))
  q54 : WsL → Eqn
  q54 c4 = wlE 8 c4
  q55 : WsL → Eqn
  q55 c4 = wlE 47 c4

-- comm CS13 CCZ024: 11 steps
lem-comm-CS13-CCZ024 : WsL → ⟪ (ℓ "乎亜") ⟫ʷ ≈ ⟪ (ℓ "亜乎") ⟫ʷ
lem-comm-CS13-CCZ024 c4 = derive (ℓ "乎亜") (ℓ "亜乎")
  (re 1 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q55 c4) ∷
   re 0 7 (ℓ "亜") ∷ []) Eq.refl

-- resp CSd03 at 1: 2 steps
lem-resp-CSd03-at-1 : WsL → ⟪ (ℓ "丷") ⟫ʷ ≈ ⟪ (ℓ "丫乏丫") ⟫ʷ
lem-resp-CSd03-at-1 c4 = derive (ℓ "丷") (ℓ "丫乏丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q41 c4) ∷ []) Eq.refl

-- comm CX13 CCZ024: 11 steps
lem-comm-CX13-CCZ024 : WsL → ⟪ (ℓ "乒亜") ⟫ʷ ≈ ⟪ (ℓ "亜乒") ⟫ʷ
lem-comm-CX13-CCZ024 c4 = derive (ℓ "乒亜") (ℓ "亜乒")
  (re 1 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw 0 (q8 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乭") ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   re 5 1 (ℓ "乼书乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q13 c4) ∷
   re 0 7 (ℓ "亜") ∷ []) Eq.refl

-- comm push CS04 sw2 L: 7 steps
lem-comm-push-CS04-sw2-L : WsL → ⟪ (ℓ "丽乥") ⟫ʷ ≈ ⟪ (ℓ "乥丽") ⟫ʷ
lem-comm-push-CS04-sw2-L c4 = derive (ℓ "丽乥") (ℓ "乥丽")
  (re 0 1 (ℓ "乼乥乊丨乊乥乼") ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q4 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (ℓ "丽") ∷ []) Eq.refl

-- resp CS03 at 2: 4 steps
lem-resp-CS03-at-2 : WsL → ⟪ (ℓ "丶") ⟫ʷ ≈ ⟪ (ℓ "乊丫乎丫乊") ⟫ʷ
lem-resp-CS03-at-2 c4 = derive (ℓ "丶") (ℓ "乊丫乎丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

-- resp CS14 at 2: 4 steps
lem-resp-CS14-at-2 : WsL → ⟪ (ℓ "乕") ⟫ʷ ≈ ⟪ (ℓ "乊丫乩丫乊") ⟫ʷ
lem-resp-CS14-at-2 c4 = derive (ℓ "乕") (ℓ "乊丫乩丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q36 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q37 c4) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = wlE 10 c4

-- comm push CX04 sw1 L: 5 steps
lem-comm-push-CX04-sw1-L : WsL → ⟪ (ℓ "乁乊") ⟫ʷ ≈ ⟪ (ℓ "乊乁") ⟫ʷ
lem-comm-push-CX04-sw1-L c4 = derive (ℓ "乁乊") (ℓ "乊乁")
  (re 0 1 (ℓ "乼为乼") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "乁") ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = wlE 14 c4
  q58 : WsL → Eqn
  q58 c4 = eqn (ℓ "丫乪") (ℓ "乪丫") (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- resp CSd14 at 2: 4 steps
lem-resp-CSd14-at-2 : WsL → ⟪ (ℓ "乖") ⟫ʷ ≈ ⟪ (ℓ "乊丫乪丫乊") ⟫ʷ
lem-resp-CSd14-at-2 c4 = derive (ℓ "乖") (ℓ "乊丫乪丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q58 c4) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (ℓ "丬亲") (ℓ "亲丬") (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))

-- comm CX04 TOFF213: 13 steps
lem-comm-CX04-TOFF213 : WsL → ⟪ (ℓ "乁亦") ⟫ʷ ≈ ⟪ (ℓ "亦乁") ⟫ʷ
lem-comm-CX04-TOFF213 c4 = derive (ℓ "乁亦") (ℓ "亦乁")
  (re 0 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "亪") ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (ℓ "亮") ∷
   rw 4 (q48 c4) ∷
   rw 3 (q59 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q7 c4) ∷
   re 1 1 (ℓ "乼亦乼") ∷
   rw 0 (q9 c4) ∷
   re 1 7 (ℓ "乁") ∷ []) Eq.refl

-- resp TOFF214 at 3: 7 steps
lem-resp-TOFF214-at-3 : WsL → ⟪ (ℓ "亪") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亲丫乊乥") ⟫ʷ
lem-resp-TOFF214-at-3 c4 = derive (ℓ "亪") (ℓ "乥乊丫亲丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "亮") ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q39 c4) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = wlE 49 c4

-- comm push CZ04 sw0 L: 5 steps
lem-comm-push-CZ04-sw0-L : WsL → ⟪ (ℓ "丿丫") ⟫ʷ ≈ ⟪ (ℓ "丫乗") ⟫ʷ
lem-comm-push-CZ04-sw0-L c4 = derive (ℓ "丿丫") (ℓ "丫乗")
  (re 0 1 (ℓ "乼丸乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "乗") ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (ℓ "个亰") (ℓ "亰个") (c₂ (CZ) (CCZ))

-- comm CZ04 CCZ123: 13 steps
lem-comm-CZ04-CCZ123 : WsL → ⟪ (ℓ "丿交") ⟫ʷ ≈ ⟪ (ℓ "交丿") ⟫ʷ
lem-comm-CZ04-CCZ123 c4 = derive (ℓ "丿交") (ℓ "交丿")
  (re 0 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "亨") ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (ℓ "京") ∷
   rw⁻ 4 (q46 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 2 1 (ℓ "乥亨乥") ∷
   rw 1 (q7 c4) ∷
   re 1 1 (ℓ "乼交乼") ∷
   rw 0 (q9 c4) ∷
   re 1 7 (ℓ "丿") ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (ℓ "个亲") (ℓ "亲个") (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))

-- comm CZ04 TOFF213: 13 steps
lem-comm-CZ04-TOFF213 : WsL → ⟪ (ℓ "丿亦") ⟫ʷ ≈ ⟪ (ℓ "亦丿") ⟫ʷ
lem-comm-CZ04-TOFF213 c4 = derive (ℓ "丿亦") (ℓ "亦丿")
  (re 0 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "亪") ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (ℓ "亮") ∷
   rw 4 (q48 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q7 c4) ∷
   re 1 1 (ℓ "乼亦乼") ∷
   rw 0 (q9 c4) ∷
   re 1 7 (ℓ "丿") ∷ []) Eq.refl

-- resp CSd03 at 2: 4 steps
lem-resp-CSd03-at-2 : WsL → ⟪ (ℓ "丷") ⟫ʷ ≈ ⟪ (ℓ "乊丫乏丫乊") ⟫ʷ
lem-resp-CSd03-at-2 c4 = derive (ℓ "丷") (ℓ "乊丫乏丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q43 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q41 c4) ∷ []) Eq.refl

-- comm TOFF014 CSd23: 9 steps
lem-comm-TOFF014-CSd23 : WsL → ⟪ (ℓ "井乣") ⟫ʷ ≈ ⟪ (ℓ "乣井") ⟫ʷ
lem-comm-TOFF014-CSd23 c4 = derive (ℓ "井乣") (ℓ "乣井")
  (re 0 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw⁻ 3 (q20 c4) ∷
   rw 2 (q19 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 1 1 (ℓ "乼乣乼") ∷
   rw 0 (q9 c4) ∷
   re 1 5 (ℓ "井") ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = wlE 50 c4
  q64 : WsL → Eqn
  q64 c4 = eqn (ℓ "丫乭") (ℓ "乭丫") (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))

-- resp CX14 at 2: 4 steps
lem-resp-CX14-at-2 : WsL → ⟪ (ℓ "乙") ⟫ʷ ≈ ⟪ (ℓ "乊丫乭丫乊") ⟫ʷ
lem-resp-CX14-at-2 c4 = derive (ℓ "乙") (ℓ "乊丫乭丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q63 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q64 c4) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = wlE 51 c4

-- comm CX14 CCZ023: 7 steps
lem-comm-CX14-CCZ023 : WsL → ⟪ (ℓ "乙亘") ⟫ʷ ≈ ⟪ (ℓ "亘乙") ⟫ʷ
lem-comm-CX14-CCZ023 c4 = derive (ℓ "乙亘") (ℓ "亘乙")
  (re 1 1 (ℓ "乊乥二乥乊") ∷
   rw 0 (q63 c4) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q65 c4) ∷
   re 0 5 (ℓ "亘") ∷ []) Eq.refl

-- resp CCZ023 at 1: 2 steps
lem-resp-CCZ023-at-1 : WsL → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丫交丫") ⟫ʷ
lem-resp-CCZ023-at-1 c4 = derive (ℓ "亘") (ℓ "丫交丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = wlE 7 c4

-- comm CSd14 TOFF023: 7 steps
lem-comm-CSd14-TOFF023 : WsL → ⟪ (ℓ "乖亙") ⟫ʷ ≈ ⟪ (ℓ "亙乖") ⟫ʷ
lem-comm-CSd14-TOFF023 c4 = derive (ℓ "乖亙") (ℓ "亙乖")
  (re 1 1 (ℓ "乊乥亍乥乊") ∷
   rw 0 (q57 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q66 c4) ∷
   re 0 5 (ℓ "亙") ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))

-- resp CS13 at 2: 4 steps
lem-resp-CS13-at-2 : WsL → ⟪ (ℓ "乎") ⟫ʷ ≈ ⟪ (ℓ "乊丫乢丫乊") ⟫ʷ
lem-resp-CS13-at-2 c4 = derive (ℓ "乎") (ℓ "乊丫乢丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q51 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q67 c4) ∷ []) Eq.refl

-- comm CSd23 CCZ014: 9 steps
lem-comm-CSd23-CCZ014 : WsL → ⟪ (ℓ "乣五") ⟫ʷ ≈ ⟪ (ℓ "五乣") ⟫ʷ
lem-comm-CSd23-CCZ014 c4 = derive (ℓ "乣五") (ℓ "五乣")
  (re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乪") ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 3 (q20 c4) ∷
   re 4 1 (ℓ "乼乣乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "五") ∷ []) Eq.refl

-- comm CS23 CCZ014: 9 steps
lem-comm-CS23-CCZ014 : WsL → ⟪ (ℓ "乢五") ⟫ʷ ≈ ⟪ (ℓ "五乢") ⟫ʷ
lem-comm-CS23-CCZ014 c4 = derive (ℓ "乢五") (ℓ "五乢")
  (re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乩") ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   re 4 1 (ℓ "乼乢乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "五") ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (ℓ "乊乹") (ℓ "乹乊") (c₃ (Swap ↑) (CS))
  q69 : WsL → Eqn
  q69 c4 = eqn (ℓ "丫乹") (ℓ "乹丫") (c₂ (Swap) (CS ↑))

-- resp CS24 at 3: 6 steps
lem-resp-CS24-at-3 : WsL → ⟪ (ℓ "乩") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乹丫乊乥") ⟫ʷ
lem-resp-CS24-at-3 c4 = derive (ℓ "乩") (ℓ "乥乊丫乹丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q69 c4) ∷ []) Eq.refl

-- comm CX23 CCZ014: 9 steps
lem-comm-CX23-CCZ014 : WsL → ⟪ (ℓ "书五") ⟫ʷ ≈ ⟪ (ℓ "五书") ⟫ʷ
lem-comm-CX23-CCZ014 c4 = derive (ℓ "书五") (ℓ "五书")
  (re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乭") ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   re 4 1 (ℓ "乼书乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "五") ∷ []) Eq.refl

-- resp CCZ124 at 3: 7 steps
lem-resp-CCZ124-at-3 : WsL → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亰丫乊乥") ⟫ʷ
lem-resp-CCZ124-at-3 c4 = derive (ℓ "亨") (ℓ "乥乊丫亰丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "京") ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q34 c4) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = wlE 52 c4

-- resp TOFF023 at 1: 2 steps
lem-resp-TOFF023-at-1 : WsL → ⟪ (ℓ "亙") ⟫ʷ ≈ ⟪ (ℓ "丫亥丫") ⟫ʷ
lem-resp-TOFF023-at-1 c4 = derive (ℓ "亙") (ℓ "丫亥丫")
  (rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (ℓ "亍乽") (ℓ "乽亍") (c₃ (Toff) (CX₀₁))

-- comm CX14 TOFF023: 7 steps
lem-comm-CX14-TOFF023 : WsL → ⟪ (ℓ "乙亙") ⟫ʷ ≈ ⟪ (ℓ "亙乙") ⟫ʷ
lem-comm-CX14-TOFF023 c4 = derive (ℓ "乙亙") (ℓ "亙乙")
  (re 1 1 (ℓ "乊乥亍乥乊") ∷
   rw 0 (q63 c4) ∷
   rw 1 (q10 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q65 c4) ∷
   re 0 5 (ℓ "亙") ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = wlE 53 c4

-- comm CZ14 CCZ023: 7 steps
lem-comm-CZ14-CCZ023 : WsL → ⟪ (ℓ "乗亘") ⟫ʷ ≈ ⟪ (ℓ "亘乗") ⟫ʷ
lem-comm-CZ14-CCZ023 c4 = derive (ℓ "乗亘") (ℓ "亘乗")
  (re 1 1 (ℓ "乊乥二乥乊") ∷
   rw 0 (q25 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q72 c4) ∷
   re 0 5 (ℓ "亘") ∷ []) Eq.refl

-- comm CZ14 TOFF023: 7 steps
lem-comm-CZ14-TOFF023 : WsL → ⟪ (ℓ "乗亙") ⟫ʷ ≈ ⟪ (ℓ "亙乗") ⟫ʷ
lem-comm-CZ14-TOFF023 c4 = derive (ℓ "乗亙") (ℓ "亙乗")
  (re 1 1 (ℓ "乊乥亍乥乊") ∷
   rw 0 (q25 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q72 c4) ∷
   re 0 5 (ℓ "亙") ∷ []) Eq.refl

-- comm TOFF024 CSd13: 11 steps
lem-comm-TOFF024-CSd13 : WsL → ⟪ (ℓ "亝乏") ⟫ʷ ≈ ⟪ (ℓ "乏亝") ⟫ʷ
lem-comm-TOFF024-CSd13 c4 = derive (ℓ "亝乏") (ℓ "乏亝")
  (re 0 1 (ℓ "乊乼乥亍乥乼乊") ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   re 1 7 (ℓ "亝") ∷ []) Eq.refl

-- comm CX24 CCZ013: 5 steps
lem-comm-CX24-CCZ013 : WsL → ⟪ (ℓ "乭亐") ⟫ʷ ≈ ⟪ (ℓ "亐乭") ⟫ʷ
lem-comm-CX24-CCZ013 c4 = derive (ℓ "乭亐") (ℓ "亐乭")
  (re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   re 0 3 (ℓ "亐") ∷ []) Eq.refl

-- comm CSd24 TOFF013: 5 steps
lem-comm-CSd24-TOFF013 : WsL → ⟪ (ℓ "乪云") ⟫ʷ ≈ ⟪ (ℓ "云乪") ⟫ʷ
lem-comm-CSd24-TOFF013 c4 = derive (ℓ "乪云") (ℓ "云乪")
  (re 1 1 (ℓ "乥亍乥") ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   re 0 3 (ℓ "云") ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = wlE 54 c4
  q74 : WsL → Eqn
  q74 c4 = eqn (ℓ "丫亱") (ℓ "亱丫") (c₂ (Swap) (Toff))

-- resp TOFF134 at 2: 4 steps
lem-resp-TOFF134-at-2 : WsL → ⟪ (ℓ "亭") ⟫ʷ ≈ ⟪ (ℓ "乊丫亱丫乊") ⟫ʷ
lem-resp-TOFF134-at-2 c4 = derive (ℓ "亭") (ℓ "乊丫亱丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q73 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q74 c4) ∷ []) Eq.refl

-- resp TOFF013 at 2: 5 steps
lem-resp-TOFF013-at-2 : WsL → ⟪ (ℓ "云") ⟫ʷ ≈ ⟪ (ℓ "乊丫亥丫乊") ⟫ʷ
lem-resp-TOFF013-at-2 c4 = derive (ℓ "云") (ℓ "乊丫亥丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (ℓ "亙") ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q70 c4) ∷ []) Eq.refl

-- comm CX24 TOFF013: 5 steps
lem-comm-CX24-TOFF013 : WsL → ⟪ (ℓ "乭云") ⟫ʷ ≈ ⟪ (ℓ "云乭") ⟫ʷ
lem-comm-CX24-TOFF013 c4 = derive (ℓ "乭云") (ℓ "云乭")
  (re 1 1 (ℓ "乥亍乥") ∷
   rw 0 (q10 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q12 c4) ∷
   re 0 3 (ℓ "云") ∷ []) Eq.refl

-- comm CZ24 CCZ013: 5 steps
lem-comm-CZ24-CCZ013 : WsL → ⟪ (ℓ "乫亐") ⟫ʷ ≈ ⟪ (ℓ "亐乫") ⟫ʷ
lem-comm-CZ24-CCZ013 c4 = derive (ℓ "乫亐") (ℓ "亐乫")
  (re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (ℓ "亐") ∷ []) Eq.refl

-- comm CZ24 TOFF013: 5 steps
lem-comm-CZ24-TOFF013 : WsL → ⟪ (ℓ "乫云") ⟫ʷ ≈ ⟪ (ℓ "云乫") ⟫ʷ
lem-comm-CZ24-TOFF013 c4 = derive (ℓ "乫云") (ℓ "云乫")
  (re 1 1 (ℓ "乥亍乥") ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q30 c4) ∷
   re 0 3 (ℓ "云") ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = wlE 55 c4
  q76 : WsL → Eqn
  q76 c4 = eqn (ℓ "义乼") (ℓ "乼义") (c₃ (CZ ↑) (Swap))
  q77 : WsL → Eqn
  q77 c4 = wlE 56 c4

-- comm SWAP23 BOX(0;14): 11 steps
lem-comm-SWAP23-BOX⟨0·14⟩ : WsL → ⟪ (ℓ "乥亷") ⟫ʷ ≈ ⟪ (ℓ "亷乥") ⟫ʷ
lem-comm-SWAP23-BOX⟨0·14⟩ c4 = derive (ℓ "乥亷") (ℓ "亷乥")
  (re 1 1 (ℓ "乗") ∷
   re 1 1 (ℓ "乼乥义乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乬") ∷
   rw⁻ 1 (q75 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   re 4 1 (ℓ "乼乥乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "乗") ∷
   re 0 1 (ℓ "亷") ∷ []) Eq.refl

-- resp TOFF203 at 1: 2 steps
lem-resp-TOFF203-at-1 : WsL → ⟪ (ℓ "亚") ⟫ʷ ≈ ⟪ (ℓ "丫亦丫") ⟫ʷ
lem-resp-TOFF203-at-1 c4 = derive (ℓ "亚") (ℓ "丫亦丫")
  (rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q24 c4) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (ℓ "丩乼") (ℓ "乼丩") (c₂ (CS • CS • CS) (Swap ↑))

-- comm push CSd04 sw2 L: 7 steps
lem-comm-push-CSd04-sw2-L : WsL → ⟪ (ℓ "举乥") ⟫ʷ ≈ ⟪ (ℓ "乥举") ⟫ʷ
lem-comm-push-CSd04-sw2-L c4 = derive (ℓ "举乥") (ℓ "乥举")
  (re 0 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q78 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (ℓ "举") ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = wlE 57 c4
  q80 : WsL → Eqn
  q80 c4 = wlE 58 c4
  q81 : WsL → Eqn
  q81 c4 = eqn (ℓ "二争") (ℓ "争二") (c₃ (CCZ) (CX₁₀))
  q82 : WsL → Eqn
  q82 c4 = wlE 59 c4
  q83 : WsL → Eqn
  q83 c4 = wlE 60 c4

-- comm CX21 CCZ034: 15 steps
lem-comm-CX21-CCZ034 : WsL → ⟪ (ℓ "也亠") ⟫ʷ ≈ ⟪ (ℓ "亠也") ⟫ʷ
lem-comm-CX21-CCZ034 c4 = derive (ℓ "也亠") (ℓ "亠也")
  (re 1 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乳") ∷
   rw 1 (q79 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "了") ∷
   rw 3 (q80 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw 5 (q82 c4) ∷
   re 6 1 (ℓ "乼乶乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q83 c4) ∷
   re 8 1 (ℓ "乥也乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亠") ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (ℓ "丫乶") (ℓ "乶丫") (c₂ (Swap) (CX₁₀))

-- resp CX31 at 2: 4 steps
lem-resp-CX31-at-2 : WsL → ⟪ (ℓ "乳") ⟫ʷ ≈ ⟪ (ℓ "乊丫乶丫乊") ⟫ʷ
lem-resp-CX31-at-2 c4 = derive (ℓ "乳") (ℓ "乊丫乶丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q79 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q84 c4) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = wlE 61 c4

-- comm SWAP13 BOX(0;24): 9 steps
lem-comm-SWAP13-BOX⟨0·24⟩ : WsL → ⟪ (ℓ "乑今") ⟫ʷ ≈ ⟪ (ℓ "今乑") ⟫ʷ
lem-comm-SWAP13-BOX⟨0·24⟩ c4 = derive (ℓ "乑今") (ℓ "今乑")
  (re 1 1 (ℓ "乫") ∷
   re 1 1 (ℓ "乼乤乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乘") ∷
   rw⁻ 1 (q85 c4) ∷
   re 2 1 (ℓ "乼乑乼") ∷
   rw 4 (q9 c4) ∷
   re 0 3 (ℓ "乫") ∷
   re 0 1 (ℓ "今") ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = wlE 62 c4

-- resp CZ14 at 3: 6 steps
lem-resp-CZ14-at-3 : WsL → ⟪ (ℓ "乗") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乫丫乊乥") ⟫ʷ
lem-resp-CZ14-at-3 c4 = derive (ℓ "乗") (ℓ "乥乊丫乫丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q25 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q26 c4) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = wlE 63 c4

-- resp TOFF302 at 1: 2 steps
lem-resp-TOFF302-at-1 : WsL → ⟪ (ℓ "些") ⟫ʷ ≈ ⟪ (ℓ "丫产丫") ⟫ʷ
lem-resp-TOFF302-at-1 c4 = derive (ℓ "些") (ℓ "丫产丫")
  (rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q87 c4) ∷ []) Eq.refl

-- comm CZ13 CCZ024: 11 steps
lem-comm-CZ13-CCZ024 : WsL → ⟪ (ℓ "乐亜") ⟫ʷ ≈ ⟪ (ℓ "亜乐") ⟫ʷ
lem-comm-CZ13-CCZ024 c4 = derive (ℓ "乐亜") (ℓ "亜乐")
  (re 1 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乫") ∷
   rw 2 (q28 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   re 5 1 (ℓ "乼乤乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q31 c4) ∷
   re 0 7 (ℓ "亜") ∷ []) Eq.refl

-- comm TOFF013 CSd24: 15 steps
lem-comm-TOFF013-CSd24 : WsL → ⟪ (ℓ "云乪") ⟫ʷ ≈ ⟪ (ℓ "乪云") ⟫ʷ
lem-comm-TOFF013-CSd24 c4 = derive (ℓ "云乪") (ℓ "乪云")
  (re 1 1 (ℓ "乼乣乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "井") ∷
   re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q9 c4) ∷
   re 2 5 (ℓ "井") ∷
   re 2 1 (ℓ "乼云乼") ∷
   rw 4 (q9 c4) ∷
   re 0 3 (ℓ "乪") ∷ []) Eq.refl

-- comm CSd13 TOFF024: 11 steps
lem-comm-CSd13-TOFF024 : WsL → ⟪ (ℓ "乏亝") ⟫ʷ ≈ ⟪ (ℓ "亝乏") ⟫ʷ
lem-comm-CSd13-TOFF024 c4 = derive (ℓ "乏亝") (ℓ "亝乏")
  (re 1 1 (ℓ "乊乼乥亍乥乼乊") ∷
   rw 0 (q17 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乪") ∷
   rw 2 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q21 c4) ∷
   re 0 7 (ℓ "亝") ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (ℓ "乊乻") (ℓ "乻乊") (c₃ (Swap ↑) (CZ))
  q89 : WsL → Eqn
  q89 c4 = eqn (ℓ "丫乻") (ℓ "乻丫") (c₂ (Swap) (CZ ↑))

-- resp CZ24 at 3: 6 steps
lem-resp-CZ24-at-3 : WsL → ⟪ (ℓ "乫") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乻丫乊乥") ⟫ʷ
lem-resp-CZ24-at-3 c4 = derive (ℓ "乫") (ℓ "乥乊丫乻丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q88 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q89 c4) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = wlE 69 c4
  q91 : WsL → Eqn
  q91 c4 = eqn (ℓ "丫了") (ℓ "了丫") (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))

-- resp CX41 at 2: 4 steps
lem-resp-CX41-at-2 : WsL → ⟪ (ℓ "亃") ⟫ʷ ≈ ⟪ (ℓ "乊丫了丫乊") ⟫ʷ
lem-resp-CX41-at-2 c4 = derive (ℓ "亃") (ℓ "乊丫了丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q90 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q91 c4) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = wlE 70 c4

-- resp CX41 at 3: 6 steps
lem-resp-CX41-at-3 : WsL → ⟪ (ℓ "亃") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫了丫乊乥") ⟫ʷ
lem-resp-CX41-at-3 c4 = derive (ℓ "亃") (ℓ "乥乊丫了丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q92 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q91 c4) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (ℓ "乊乺") (ℓ "乺乊") (c₃ (Swap ↑) (CS • CS • CS))
  q94 : WsL → Eqn
  q94 c4 = eqn (ℓ "丫乺") (ℓ "乺丫") (c₂ (Swap) ((CS • CS • CS) ↑))

-- resp CSd24 at 3: 6 steps
lem-resp-CSd24-at-3 : WsL → ⟪ (ℓ "乪") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乺丫乊乥") ⟫ʷ
lem-resp-CSd24-at-3 c4 = derive (ℓ "乪") (ℓ "乥乊丫乺丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q94 c4) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = wlE 71 c4

-- resp CX14 at 3: 6 steps
lem-resp-CX14-at-3 : WsL → ⟪ (ℓ "乙") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乭丫乊乥") ⟫ʷ
lem-resp-CX14-at-3 c4 = derive (ℓ "乙") (ℓ "乥乊丫乭丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q95 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q63 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q64 c4) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (ℓ "亍乹") (ℓ "乹亍") (c₃ (Toff) (CS))

-- comm CS12 TOFF034: 15 steps
lem-comm-CS12-TOFF034 : WsL → ⟪ (ℓ "乇亡") ⟫ʷ ≈ ⟪ (ℓ "亡乇") ⟫ʷ
lem-comm-CS12-TOFF034 c4 = derive (ℓ "乇亡") (ℓ "亡乇")
  (re 1 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乩") ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (ℓ "乼乢乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q55 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亡") ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = wlE 72 c4
  q98 : WsL → Eqn
  q98 c4 = eqn (ℓ "丫乬") (ℓ "乬丫") (c₂ (Swap) (Swap ↑ • Swap • Swap ↑))

-- resp SWAP14 at 2: 4 steps
lem-resp-SWAP14-at-2 : WsL → ⟪ (ℓ "乘") ⟫ʷ ≈ ⟪ (ℓ "乊丫乬丫乊") ⟫ʷ
lem-resp-SWAP14-at-2 c4 = derive (ℓ "乘") (ℓ "乊丫乬丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q97 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q98 c4) ∷ []) Eq.refl

-- resp TOFF301 at 2: 5 steps
lem-resp-TOFF301-at-2 : WsL → ⟪ (ℓ "亓") ⟫ʷ ≈ ⟪ (ℓ "乊丫产丫乊") ⟫ʷ
lem-resp-TOFF301-at-2 c4 = derive (ℓ "亓") (ℓ "乊丫产丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q22 c4) ∷
   re 1 3 (ℓ "些") ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

-- comm SWAP14 BOX(0;32): 3 steps
lem-comm-SWAP14-BOX⟨0·32⟩ : WsL → ⟪ (ℓ "乘仧") ⟫ʷ ≈ ⟪ (ℓ "仧乘") ⟫ʷ
lem-comm-SWAP14-BOX⟨0·32⟩ c4 = derive (ℓ "乘仧") (ℓ "仧乘")
  (re 1 1 (ℓ "乤") ∷
   rw⁻ 0 (q85 c4) ∷
   re 0 1 (ℓ "仧") ∷ []) Eq.refl

-- comm CZ23 CCZ014: 9 steps
lem-comm-CZ23-CCZ014 : WsL → ⟪ (ℓ "乤五") ⟫ʷ ≈ ⟪ (ℓ "五乤") ⟫ʷ
lem-comm-CZ23-CCZ014 c4 = derive (ℓ "乤五") (ℓ "五乤")
  (re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乫") ∷
   rw 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q30 c4) ∷
   re 4 1 (ℓ "乼乤乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "五") ∷ []) Eq.refl

-- comm CSd23 TOFF014: 9 steps
lem-comm-CSd23-TOFF014 : WsL → ⟪ (ℓ "乣井") ⟫ʷ ≈ ⟪ (ℓ "井乣") ⟫ʷ
lem-comm-CSd23-TOFF014 c4 = derive (ℓ "乣井") (ℓ "井乣")
  (re 1 1 (ℓ "乼乥亍乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乪") ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   re 4 1 (ℓ "乼乣乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "井") ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (ℓ "乊争") (ℓ "争乊") (c₃ (Swap ↑) (CX₁₀))
  q100 : WsL → Eqn
  q100 c4 = eqn (ℓ "丫争") (ℓ "争丫") (c₂ (Swap) (CX₁₀ ↑))

-- resp CX42 at 3: 6 steps
lem-resp-CX42-at-3 : WsL → ⟪ (ℓ "了") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫争丫乊乥") ⟫ʷ
lem-resp-CX42-at-3 c4 = derive (ℓ "了") (ℓ "乥乊丫争丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q99 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q100 c4) ∷ []) Eq.refl

private
  q101 : WsL → Eqn
  q101 c4 = wlE 48 c4

-- resp CSd14 at 3: 6 steps
lem-resp-CSd14-at-3 : WsL → ⟪ (ℓ "乖") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乪丫乊乥") ⟫ʷ
lem-resp-CSd14-at-3 c4 = derive (ℓ "乖") (ℓ "乥乊丫乪丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q58 c4) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (ℓ "乊乽") (ℓ "乽乊") (c₃ (Swap ↑) (CX₀₁))
  q103 : WsL → Eqn
  q103 c4 = eqn (ℓ "丫乽") (ℓ "乽丫") (c₂ (Swap) (CX₀₁ ↑))

-- resp CX24 at 3: 6 steps
lem-resp-CX24-at-3 : WsL → ⟪ (ℓ "乭") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乽丫乊乥") ⟫ʷ
lem-resp-CX24-at-3 c4 = derive (ℓ "乭") (ℓ "乥乊丫乽丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q102 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q103 c4) ∷ []) Eq.refl

-- comm SWAP24 BOX(0;31): 7 steps
lem-comm-SWAP24-BOX⟨0·31⟩ : WsL → ⟪ (ℓ "乬仟") ⟫ʷ ≈ ⟪ (ℓ "仟乬") ⟫ʷ
lem-comm-SWAP24-BOX⟨0·31⟩ c4 = derive (ℓ "乬仟") (ℓ "仟乬")
  (re 1 1 (ℓ "乐") ∷
   re 1 1 (ℓ "乥义乥") ∷
   rw⁻ 0 (q75 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   re 0 3 (ℓ "乐") ∷
   re 0 1 (ℓ "仟") ∷ []) Eq.refl

-- comm CX31 CCZ024: 11 steps
lem-comm-CX31-CCZ024 : WsL → ⟪ (ℓ "乳亜") ⟫ʷ ≈ ⟪ (ℓ "亜乳") ⟫ʷ
lem-comm-CX31-CCZ024 c4 = derive (ℓ "乳亜") (ℓ "亜乳")
  (re 1 1 (ℓ "乊乼乥二乥乼乊") ∷
   rw 0 (q79 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "了") ∷
   rw 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   re 5 1 (ℓ "乼乶乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q83 c4) ∷
   re 0 7 (ℓ "亜") ∷ []) Eq.refl

-- comm CS13 TOFF024: 11 steps
lem-comm-CS13-TOFF024 : WsL → ⟪ (ℓ "乎亝") ⟫ʷ ≈ ⟪ (ℓ "亝乎") ⟫ʷ
lem-comm-CS13-TOFF024 c4 = derive (ℓ "乎亝") (ℓ "亝乎")
  (re 1 1 (ℓ "乊乼乥亍乥乼乊") ∷
   rw 0 (q51 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乩") ∷
   rw 2 (q52 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw 4 (q54 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 7 (q9 c4) ∷
   rw 6 (q55 c4) ∷
   re 0 7 (ℓ "亝") ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = wlE 74 c4

-- resp SWAP14 at 3: 6 steps
lem-resp-SWAP14-at-3 : WsL → ⟪ (ℓ "乘") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫乬丫乊乥") ⟫ʷ
lem-resp-SWAP14-at-3 c4 = derive (ℓ "乘") (ℓ "乥乊丫乬丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw 0 (q104 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q97 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q98 c4) ∷ []) Eq.refl

-- comm SWAP14 BOX(0;23): 3 steps
lem-comm-SWAP14-BOX⟨0·23⟩ : WsL → ⟪ (ℓ "乘仏") ⟫ʷ ≈ ⟪ (ℓ "仏乘") ⟫ʷ
lem-comm-SWAP14-BOX⟨0·23⟩ c4 = derive (ℓ "乘仏") (ℓ "仏乘")
  (re 1 1 (ℓ "乤") ∷
   rw⁻ 0 (q85 c4) ∷
   re 0 1 (ℓ "仏") ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = wlE 75 c4
  q106 : WsL → Eqn
  q106 c4 = eqn (ℓ "丫乥") (ℓ "乥丫") (c₂ (Swap) (Swap))

-- resp SWAP13 at 2: 4 steps
lem-resp-SWAP13-at-2 : WsL → ⟪ (ℓ "乑") ⟫ʷ ≈ ⟪ (ℓ "乊丫乥丫乊") ⟫ʷ
lem-resp-SWAP13-at-2 c4 = derive (ℓ "乑") (ℓ "乊丫乥丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q105 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q106 c4) ∷ []) Eq.refl

-- comm SWAP13 BOX(0;42): 9 steps
lem-comm-SWAP13-BOX⟨0·42⟩ : WsL → ⟪ (ℓ "乑仿") ⟫ʷ ≈ ⟪ (ℓ "仿乑") ⟫ʷ
lem-comm-SWAP13-BOX⟨0·42⟩ c4 = derive (ℓ "乑仿") (ℓ "仿乑")
  (re 1 1 (ℓ "乫") ∷
   re 1 1 (ℓ "乼乤乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "乘") ∷
   rw⁻ 1 (q85 c4) ∷
   re 2 1 (ℓ "乼乑乼") ∷
   rw 4 (q9 c4) ∷
   re 0 3 (ℓ "乫") ∷
   re 0 1 (ℓ "仿") ∷ []) Eq.refl

-- comm TOFF034 CSd12: 15 steps
lem-comm-TOFF034-CSd12 : WsL → ⟪ (ℓ "亡么") ⟫ʷ ≈ ⟪ (ℓ "么亡") ⟫ʷ
lem-comm-TOFF034-CSd12 c4 = derive (ℓ "亡么") (ℓ "么亡")
  (re 0 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (ℓ "乏") ∷
   rw⁻ 7 (q21 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "乪") ∷
   rw⁻ 5 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 3 1 (ℓ "乼乣乼") ∷
   rw 2 (q9 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   re 1 1 (ℓ "乥么乥") ∷
   rw 0 (q7 c4) ∷
   re 1 9 (ℓ "亡") ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = eqn (ℓ "丫乤") (ℓ "乤丫") (c₂ (Swap) (CZ))

-- resp CZ13 at 2: 4 steps
lem-resp-CZ13-at-2 : WsL → ⟪ (ℓ "乐") ⟫ʷ ≈ ⟪ (ℓ "乊丫乤丫乊") ⟫ʷ
lem-resp-CZ13-at-2 c4 = derive (ℓ "乐") (ℓ "乊丫乤丫乊")
  (rw⁻ 1 (q22 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 1 (q107 c4) ∷ []) Eq.refl

-- comm CX42 CCZ013: 5 steps
lem-comm-CX42-CCZ013 : WsL → ⟪ (ℓ "了亐") ⟫ʷ ≈ ⟪ (ℓ "亐了") ⟫ʷ
lem-comm-CX42-CCZ013 c4 = derive (ℓ "了亐") (ℓ "亐了")
  (re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q80 c4) ∷
   rw⁻ 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   re 0 3 (ℓ "亐") ∷ []) Eq.refl

-- comm CX32 CCZ014: 9 steps
lem-comm-CX32-CCZ014 : WsL → ⟪ (ℓ "乶五") ⟫ʷ ≈ ⟪ (ℓ "五乶") ⟫ʷ
lem-comm-CX32-CCZ014 c4 = derive (ℓ "乶五") (ℓ "五乶")
  (re 1 1 (ℓ "乼乥二乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "了") ∷
   rw 1 (q80 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q82 c4) ∷
   re 4 1 (ℓ "乼乶乼") ∷
   rw 6 (q9 c4) ∷
   re 0 5 (ℓ "五") ∷ []) Eq.refl

-- comm CSd12 CCZ034: 15 steps
lem-comm-CSd12-CCZ034 : WsL → ⟪ (ℓ "么亠") ⟫ʷ ≈ ⟪ (ℓ "亠么") ⟫ʷ
lem-comm-CSd12-CCZ034 c4 = derive (ℓ "么亠") (ℓ "亠么")
  (re 1 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乏") ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亠") ∷ []) Eq.refl

-- comm CS12 CCZ034: 15 steps
lem-comm-CS12-CCZ034 : WsL → ⟪ (ℓ "乇亠") ⟫ʷ ≈ ⟪ (ℓ "亠乇") ⟫ʷ
lem-comm-CS12-CCZ034 c4 = derive (ℓ "乇亠") (ℓ "亠乇")
  (re 1 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乎") ∷
   rw 1 (q51 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乩") ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   re 6 1 (ℓ "乼乢乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q55 c4) ∷
   re 8 1 (ℓ "乥乇乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亠") ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = wlE 76 c4

-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : WsL → ⟪ (ℓ "丱") ⟫ʷ ≈ ⟪ (ℓ "丫义丫") ⟫ʷ
lem-resp-CZ02-at-1 c4 = derive (ℓ "丱") (ℓ "丫义丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = wlE 77 c4

-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : WsL → ⟪ (ℓ "乜") ⟫ʷ ≈ ⟪ (ℓ "丫也丫") ⟫ʷ
lem-resp-CX20-at-1 c4 = derive (ℓ "乜") (ℓ "丫也丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q109 c4) ∷ []) Eq.refl

-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : WsL → ⟪ (ℓ "为") ⟫ʷ ≈ ⟪ (ℓ "丫乒丫") ⟫ʷ
lem-resp-CX03-at-1 c4 = derive (ℓ "为") (ℓ "丫乒丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q45 c4) ∷ []) Eq.refl

-- resp CZ03 at 1: 2 steps
lem-resp-CZ03-at-1 : WsL → ⟪ (ℓ "丸") ⟫ʷ ≈ ⟪ (ℓ "丫乐丫") ⟫ʷ
lem-resp-CZ03-at-1 c4 = derive (ℓ "丸") (ℓ "丫乐丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q60 c4) ∷ []) Eq.refl

-- comm CX12 TOFF034: 15 steps
lem-comm-CX12-TOFF034 : WsL → ⟪ (ℓ "之亡") ⟫ʷ ≈ ⟪ (ℓ "亡之") ⟫ʷ
lem-comm-CX12-TOFF034 c4 = derive (ℓ "之亡") (ℓ "亡之")
  (re 1 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乒") ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乭") ∷
   rw 3 (q10 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 5 (q12 c4) ∷
   re 6 1 (ℓ "乼书乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q13 c4) ∷
   re 8 1 (ℓ "乥之乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亡") ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = wlE 78 c4

-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : WsL → ⟪ (ℓ "买") ⟫ʷ ≈ ⟪ (ℓ "丫乳丫") ⟫ʷ
lem-resp-CX30-at-1 c4 = derive (ℓ "买") (ℓ "丫乳丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q110 c4) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (ℓ "个乼") (ℓ "乼个") (c₂ (CZ) (Swap ↑))

-- comm push CZ04 sw2 L: 7 steps
lem-comm-push-CZ04-sw2-L : WsL → ⟪ (ℓ "丿乥") ⟫ʷ ≈ ⟪ (ℓ "乥丿") ⟫ʷ
lem-comm-push-CZ04-sw2-L c4 = derive (ℓ "丿乥") (ℓ "乥丿")
  (re 0 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q111 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (ℓ "丿") ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = wlE 79 c4

-- comm push CZ04 sw1 L: 5 steps
lem-comm-push-CZ04-sw1-L : WsL → ⟪ (ℓ "丿乊") ⟫ʷ ≈ ⟪ (ℓ "乊丿") ⟫ʷ
lem-comm-push-CZ04-sw1-L c4 = derive (ℓ "丿乊") (ℓ "乊丿")
  (re 0 1 (ℓ "乼丸乼") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "丿") ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (ℓ "乄乼") (ℓ "乼乄") (c₂ (CX₁₀) (Swap ↑))

-- comm push CX40 sw2 L: 7 steps
lem-comm-push-CX40-sw2-L : WsL → ⟪ (ℓ "亀乥") ⟫ʷ ≈ ⟪ (ℓ "乥亀") ⟫ʷ
lem-comm-push-CX40-sw2-L c4 = derive (ℓ "亀乥") (ℓ "乥亀")
  (re 0 1 (ℓ "乼乥乊乄乊乥乼") ∷
   rw 5 (q3 c4) ∷
   rw 4 (q1 c4) ∷
   rw 3 (q113 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 7 (ℓ "亀") ∷ []) Eq.refl

private
  q114 : WsL → Eqn
  q114 c4 = wlE 80 c4

-- comm push CX40 sw1 L: 5 steps
lem-comm-push-CX40-sw1-L : WsL → ⟪ (ℓ "亀乊") ⟫ʷ ≈ ⟪ (ℓ "乊亀") ⟫ʷ
lem-comm-push-CX40-sw1-L c4 = derive (ℓ "亀乊") (ℓ "乊亀")
  (re 0 1 (ℓ "乼买乼") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亀") ∷ []) Eq.refl

-- comm push CX40 sw0 L: 5 steps
lem-comm-push-CX40-sw0-L : WsL → ⟪ (ℓ "亀丫") ⟫ʷ ≈ ⟪ (ℓ "丫亃") ⟫ʷ
lem-comm-push-CX40-sw0-L c4 = derive (ℓ "亀丫") (ℓ "丫亃")
  (re 0 1 (ℓ "乼买乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q110 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "亃") ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = wlE 81 c4

-- comm push CK40 sw0 L: 5 steps
lem-comm-push-CK40-sw0-L : WsL → ⟪ (ℓ "亁丫") ⟫ʷ ≈ ⟪ (ℓ "丫亄") ⟫ʷ
lem-comm-push-CK40-sw0-L c4 = derive (ℓ "亁丫") (ℓ "丫亄")
  (re 0 1 (ℓ "乼乱乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q115 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "亄") ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = wlE 82 c4

-- comm push CKd40 sw0 L: 5 steps
lem-comm-push-CKd40-sw0-L : WsL → ⟪ (ℓ "亂丫") ⟫ʷ ≈ ⟪ (ℓ "丫亅") ⟫ʷ
lem-comm-push-CKd40-sw0-L c4 = derive (ℓ "亂丫") (ℓ "丫亅")
  (re 0 1 (ℓ "乼乲乼") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 1 (q116 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 1 3 (ℓ "亅") ∷ []) Eq.refl

-- comm CX02 CCZ134: 23 steps
lem-comm-CX02-CCZ134 : WsL → ⟪ (ℓ "丳京") ⟫ʷ ≈ ⟪ (ℓ "京丳") ⟫ʷ
lem-comm-CX02-CCZ134 c4 = derive (ℓ "丳京") (ℓ "京丳")
  (re 1 1 (ℓ "乥乼交乼乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "为") ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乁") ∷
   re 2 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 10 (q9 c4) ∷
   re 8 3 (ℓ "亨") ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (ℓ "京") ∷
   rw⁻ 6 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   re 4 1 (ℓ "乥亨乥") ∷
   rw 3 (q7 c4) ∷
   re 3 1 (ℓ "乼交乼") ∷
   rw 2 (q9 c4) ∷
   re 3 7 (ℓ "乁") ∷
   re 3 1 (ℓ "乼为乼") ∷
   rw 5 (q9 c4) ∷
   re 4 1 (ℓ "乥丳乥") ∷
   rw 6 (q7 c4) ∷
   re 0 5 (ℓ "京") ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = wlE 83 c4
  q118 : WsL → Eqn
  q118 c4 = eqn (ℓ "丩亱") (ℓ "亱丩") (c₂ (CS • CS • CS) (Toff))

-- comm CSd02 TOFF134: 23 steps
lem-comm-CSd02-TOFF134 : WsL → ⟪ (ℓ "丰亭") ⟫ʷ ≈ ⟪ (ℓ "亭丰") ⟫ʷ
lem-comm-CSd02-TOFF134 c4 = derive (ℓ "丰亭") (ℓ "亭丰")
  (re 1 1 (ℓ "乥乼亥乼乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "丷") ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "举") ∷
   re 2 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 10 (q9 c4) ∷
   re 8 3 (ℓ "亩") ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (ℓ "亭") ∷
   rw 6 (q117 c4) ∷
   rw 5 (q118 c4) ∷
   rw 4 (q73 c4) ∷
   re 4 1 (ℓ "乥亩乥") ∷
   rw 3 (q7 c4) ∷
   re 3 1 (ℓ "乼亥乼") ∷
   rw 2 (q9 c4) ∷
   re 3 7 (ℓ "举") ∷
   re 3 1 (ℓ "乼丷乼") ∷
   rw 5 (q9 c4) ∷
   re 4 1 (ℓ "乥丰乥") ∷
   rw 6 (q7 c4) ∷
   re 0 5 (ℓ "亭") ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (ℓ "丬亱") (ℓ "亱丬") (c₂ (CX₀₁) (Toff))

-- comm CX02 TOFF134: 23 steps
lem-comm-CX02-TOFF134 : WsL → ⟪ (ℓ "丳亭") ⟫ʷ ≈ ⟪ (ℓ "亭丳") ⟫ʷ
lem-comm-CX02-TOFF134 c4 = derive (ℓ "丳亭") (ℓ "亭丳")
  (re 1 1 (ℓ "乥乼亥乼乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "为") ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "乁") ∷
   re 2 1 (ℓ "乼乥乊丬乊乥乼") ∷
   rw⁻ 10 (q9 c4) ∷
   re 8 3 (ℓ "亩") ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (ℓ "亭") ∷
   rw 6 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   rw 4 (q73 c4) ∷
   re 4 1 (ℓ "乥亩乥") ∷
   rw 3 (q7 c4) ∷
   re 3 1 (ℓ "乼亥乼") ∷
   rw 2 (q9 c4) ∷
   re 3 7 (ℓ "乁") ∷
   re 3 1 (ℓ "乼为乼") ∷
   rw 5 (q9 c4) ∷
   re 4 1 (ℓ "乥丳乥") ∷
   rw 6 (q7 c4) ∷
   re 0 5 (ℓ "亭") ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = wlE 5 c4

-- comm CS14 TOFF023: 7 steps
lem-comm-CS14-TOFF023 : WsL → ⟪ (ℓ "乕亙") ⟫ʷ ≈ ⟪ (ℓ "亙乕") ⟫ʷ
lem-comm-CS14-TOFF023 c4 = derive (ℓ "乕亙") (ℓ "亙乕")
  (re 1 1 (ℓ "乊乥亍乥乊") ∷
   rw 0 (q36 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 3 (q54 c4) ∷
   rw 4 (q120 c4) ∷
   re 0 5 (ℓ "亙") ∷ []) Eq.refl

-- comm CS24 TOFF013: 5 steps
lem-comm-CS24-TOFF013 : WsL → ⟪ (ℓ "乩云") ⟫ʷ ≈ ⟪ (ℓ "云乩") ⟫ʷ
lem-comm-CS24-TOFF013 c4 = derive (ℓ "乩云") (ℓ "云乩")
  (re 1 1 (ℓ "乥亍乥") ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q96 c4) ∷
   rw 2 (q54 c4) ∷
   re 0 3 (ℓ "云") ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (ℓ "亏乺") (ℓ "乺亏") (c₃ (Toffᵗ) (CS • CS • CS))

-- comm TOFF301 CSd24: 15 steps
lem-comm-TOFF301-CSd24 : WsL → ⟪ (ℓ "亓乪") ⟫ʷ ≈ ⟪ (ℓ "乪亓") ⟫ʷ
lem-comm-TOFF301-CSd24 c4 = derive (ℓ "亓乪") (ℓ "乪亓")
  (re 1 1 (ℓ "乼乣乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "亗") ∷
   re 1 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 7 (q9 c4) ∷
   re 5 3 (ℓ "乪") ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q121 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   re 2 1 (ℓ "乼乣乼") ∷
   rw 1 (q9 c4) ∷
   re 2 5 (ℓ "亗") ∷
   re 2 1 (ℓ "乼亓乼") ∷
   rw 4 (q9 c4) ∷
   re 0 3 (ℓ "乪") ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = wlE 39 c4

-- resp CX02 at 1: 2 steps
lem-resp-CX02-at-1 : WsL → ⟪ (ℓ "丳") ⟫ʷ ≈ ⟪ (ℓ "丫之丫") ⟫ʷ
lem-resp-CX02-at-1 c4 = derive (ℓ "丳") (ℓ "丫之丫")
  (rw⁻ 1 (q14 c4) ∷
   rw 0 (q122 c4) ∷ []) Eq.refl

-- comm CSd24 CCZ013: 5 steps
lem-comm-CSd24-CCZ013 : WsL → ⟪ (ℓ "乪亐") ⟫ʷ ≈ ⟪ (ℓ "亐乪") ⟫ʷ
lem-comm-CSd24-CCZ013 c4 = derive (ℓ "乪亐") (ℓ "亐乪")
  (re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q50 c4) ∷
   rw 2 (q20 c4) ∷
   re 0 3 (ℓ "亐") ∷ []) Eq.refl

-- comm CS24 CCZ013: 5 steps
lem-comm-CS24-CCZ013 : WsL → ⟪ (ℓ "乩亐") ⟫ʷ ≈ ⟪ (ℓ "亐乩") ⟫ʷ
lem-comm-CS24-CCZ013 c4 = derive (ℓ "乩亐") (ℓ "亐乩")
  (re 1 1 (ℓ "乥二乥") ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   re 0 3 (ℓ "亐") ∷ []) Eq.refl

-- comm TOFF401 CSd23: 9 steps
lem-comm-TOFF401-CSd23 : WsL → ⟪ (ℓ "亗乣") ⟫ʷ ≈ ⟪ (ℓ "乣亗") ⟫ʷ
lem-comm-TOFF401-CSd23 c4 = derive (ℓ "亗乣") (ℓ "乣亗")
  (re 0 1 (ℓ "乼乥亏乥乼") ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (ℓ "乪") ∷
   rw⁻ 3 (q20 c4) ∷
   rw 2 (q121 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 1 1 (ℓ "乼乣乼") ∷
   rw 0 (q9 c4) ∷
   re 1 5 (ℓ "亗") ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = wlE 84 c4
  q124 : WsL → Eqn
  q124 c4 = eqn (ℓ "丨亳") (ℓ "亳丨") (c₂ (CS) (Toffᵗ))
  q125 : WsL → Eqn
  q125 c4 = wlE 85 c4

-- comm CS03 TOFF412: 9 steps
lem-comm-CS03-TOFF412 : WsL → ⟪ (ℓ "丶享") ⟫ʷ ≈ ⟪ (ℓ "享丶") ⟫ʷ
lem-comm-CS03-TOFF412 c4 = derive (ℓ "丶享") (ℓ "享丶")
  (re 0 1 (ℓ "乥乊丨乊乥") ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw 3 (q123 c4) ∷
   rw 2 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   re 1 1 (ℓ "乥享乥") ∷
   rw 0 (q7 c4) ∷
   re 1 5 (ℓ "丶") ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (ℓ "丩亳") (ℓ "亳丩") (c₂ (CS • CS • CS) (Toffᵗ))

-- comm TOFF412 CSd03: 9 steps
lem-comm-TOFF412-CSd03 : WsL → ⟪ (ℓ "享丷") ⟫ʷ ≈ ⟪ (ℓ "丷享") ⟫ʷ
lem-comm-TOFF412-CSd03 c4 = derive (ℓ "享丷") (ℓ "丷享")
  (re 1 1 (ℓ "乥乊丩乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "亯") ∷
   rw⁻ 1 (q125 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   re 4 1 (ℓ "乥享乥") ∷
   rw 6 (q7 c4) ∷
   re 0 5 (ℓ "丷") ∷ []) Eq.refl

-- comm CSd12 TOFF403: 15 steps
lem-comm-CSd12-TOFF403 : WsL → ⟪ (ℓ "么亣") ⟫ʷ ≈ ⟪ (ℓ "亣么") ⟫ʷ
lem-comm-CSd12-TOFF403 c4 = derive (ℓ "么亣") (ℓ "亣么")
  (re 1 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "乏") ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 3 3 (ℓ "乪") ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q20 c4) ∷
   re 6 1 (ℓ "乼乣乼") ∷
   rw 8 (q9 c4) ∷
   rw 7 (q21 c4) ∷
   re 8 1 (ℓ "乥么乥") ∷
   rw 10 (q7 c4) ∷
   re 0 9 (ℓ "亣") ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))

-- comm CSd03 CCZ124: 9 steps
lem-comm-CSd03-CCZ124 : WsL → ⟪ (ℓ "丷亨") ⟫ʷ ≈ ⟪ (ℓ "亨丷") ⟫ʷ
lem-comm-CSd03-CCZ124 c4 = derive (ℓ "丷亨") (ℓ "亨丷")
  (re 0 1 (ℓ "乥乊丩乊乥") ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q127 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q7 c4) ∷
   re 1 5 (ℓ "丷") ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))

-- comm CS03 CCZ124: 9 steps
lem-comm-CS03-CCZ124 : WsL → ⟪ (ℓ "丶亨") ⟫ʷ ≈ ⟪ (ℓ "亨丶") ⟫ʷ
lem-comm-CS03-CCZ124 c4 = derive (ℓ "丶亨") (ℓ "亨丶")
  (re 0 1 (ℓ "乥乊丨乊乥") ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (ℓ "京") ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q128 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   re 1 1 (ℓ "乥亨乥") ∷
   rw 0 (q7 c4) ∷
   re 1 5 (ℓ "丶") ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (ℓ "丫亳") (ℓ "亳丫") (c₂ (Swap) (Toffᵗ))

-- resp TOFF412 at 3: 7 steps
lem-resp-TOFF412-at-3 : WsL → ⟪ (ℓ "享") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亳丫乊乥") ⟫ʷ
lem-resp-TOFF412-at-3 c4 = derive (ℓ "享") (ℓ "乥乊丫亳丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "亯") ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q125 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q129 c4) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (ℓ "个亳") (ℓ "亳个") (c₂ (CZ) (Toffᵗ))

-- comm CZ03 TOFF412: 9 steps
lem-comm-CZ03-TOFF412 : WsL → ⟪ (ℓ "丸享") ⟫ʷ ≈ ⟪ (ℓ "享丸") ⟫ʷ
lem-comm-CZ03-TOFF412 c4 = derive (ℓ "丸享") (ℓ "享丸")
  (re 0 1 (ℓ "乥乊个乊乥") ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw 3 (q123 c4) ∷
   rw 2 (q130 c4) ∷
   rw 1 (q125 c4) ∷
   re 1 1 (ℓ "乥享乥") ∷
   rw 0 (q7 c4) ∷
   re 1 5 (ℓ "丸") ∷ []) Eq.refl

-- comm CSd03 TOFF412: 9 steps
lem-comm-CSd03-TOFF412 : WsL → ⟪ (ℓ "丷享") ⟫ʷ ≈ ⟪ (ℓ "享丷") ⟫ʷ
lem-comm-CSd03-TOFF412 c4 = derive (ℓ "丷享") (ℓ "享丷")
  (re 0 1 (ℓ "乥乊丩乊乥") ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (ℓ "亯") ∷
   rw 3 (q123 c4) ∷
   rw 2 (q126 c4) ∷
   rw 1 (q125 c4) ∷
   re 1 1 (ℓ "乥享乥") ∷
   rw 0 (q7 c4) ∷
   re 1 5 (ℓ "丷") ∷ []) Eq.refl

-- resp TOFF124 at 3: 7 steps
lem-resp-TOFF124-at-3 : WsL → ⟪ (ℓ "亩") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亱丫乊乥") ⟫ʷ
lem-resp-TOFF124-at-3 c4 = derive (ℓ "亩") (ℓ "乥乊丫亱丫乊乥")
  (rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "亭") ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q74 c4) ∷ []) Eq.refl

private
  q131 : WsL → Eqn
  q131 c4 = wlE 86 c4

-- comm SWAP02 BOX(4;13): 9 steps
lem-comm-SWAP02-BOX⟨4·13⟩ : WsL → ⟪ (ℓ "串伤") ⟫ʷ ≈ ⟪ (ℓ "伤串") ⟫ʷ
lem-comm-SWAP02-BOX⟨4·13⟩ c4 = derive (ℓ "串伤") (ℓ "伤串")
  (re 1 1 (ℓ "乐") ∷
   re 1 1 (ℓ "乥义乥") ∷
   rw⁻ 0 (q7 c4) ∷
   re 1 3 (ℓ "丹") ∷
   rw⁻ 1 (q131 c4) ∷
   re 2 1 (ℓ "乥串乥") ∷
   rw 4 (q7 c4) ∷
   re 0 3 (ℓ "乐") ∷
   re 0 1 (ℓ "伤") ∷ []) Eq.refl

-- comm CZ04 TOFF312: 13 steps
lem-comm-CZ04-TOFF312 : WsL → ⟪ (ℓ "丿产") ⟫ʷ ≈ ⟪ (ℓ "产丿") ⟫ʷ
lem-comm-CZ04-TOFF312 c4 = derive (ℓ "丿产") (ℓ "产丿")
  (re 0 1 (ℓ "乼乥乊个乊乥乼") ∷
   rw⁻ 8 (q9 c4) ∷
   re 6 3 (ℓ "享") ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (ℓ "亯") ∷
   rw 4 (q123 c4) ∷
   rw 3 (q130 c4) ∷
   rw 2 (q125 c4) ∷
   re 2 1 (ℓ "乥享乥") ∷
   rw 1 (q7 c4) ∷
   re 1 1 (ℓ "乼产乼") ∷
   rw 0 (q9 c4) ∷
   re 1 7 (ℓ "丿") ∷ []) Eq.refl

-- comm TOFF312 CSd04: 13 steps
lem-comm-TOFF312-CSd04 : WsL → ⟪ (ℓ "产举") ⟫ʷ ≈ ⟪ (ℓ "举产") ⟫ʷ
lem-comm-TOFF312-CSd04 c4 = derive (ℓ "产举") (ℓ "举产")
  (re 1 1 (ℓ "乼乥乊丩乊乥乼") ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "享") ∷
   rw⁻ 1 (q7 c4) ∷
   re 2 3 (ℓ "亯") ∷
   rw⁻ 2 (q125 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   re 5 1 (ℓ "乥享乥") ∷
   rw 7 (q7 c4) ∷
   re 6 1 (ℓ "乼产乼") ∷
   rw 8 (q9 c4) ∷
   re 0 7 (ℓ "举") ∷ []) Eq.refl
