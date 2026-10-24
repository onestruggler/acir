{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D374 (W : Ws) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

private
  q1 : Eqn
  q1 = wE 1018 W
  q2 : Eqn
  q2 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q3 : Eqn
  q3 = wE 257 W
  q4 : Eqn
  q4 = wE 389 W
  q5 : Eqn
  q5 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q6 : Eqn
  q6 = wE 390 W
  q7 : Eqn
  q7 = wE 258 W

-- distribute Gad(t=1, W=(2, 3), d=1, e=-1) CS13 TOFF102 CSd13 TOFF102: 15 steps
lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞丘习丘丞举丞丘习丘") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘丞丽习举习丘丞") (ℓ "丞丽丞丘习丘丞举丞丘习丘")
  (rw 3 q1 ∷
   rw 8 q1 ∷
   rw 13 q1 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q2 ∷
   rw 6 q6 ∷
   rw 6 q2 ∷
   rw 7 q7 ∷
   rw 8 q4 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw 12 q6 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q9 : Eqn
  q9 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))

-- pass [X2 CS23 X2] [CS01]: 3 steps
lem-pass-X2-CS23-X2-vs-CS01 : ⟪ (ℓ "丘义丘丠") ⟫ʷ ≈ ⟪ (ℓ "丠丘义丘") ⟫ʷ
lem-pass-X2-CS23-X2-vs-CS01 = derive (ℓ "丘义丘丠") (ℓ "丠丘义丘")
  (rw⁻ 2 q8 ∷
   rw⁻ 1 q9 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1019 W

-- pass [X2 CS23 X2] [TOFF123]: 1 steps
lem-pass-X2-CS23-X2-vs-TOFF123 : ⟪ (ℓ "丘义丘乢") ⟫ʷ ≈ ⟪ (ℓ "乢丘义丘") ⟫ʷ
lem-pass-X2-CS23-X2-vs-TOFF123 = derive (ℓ "丘义丘乢") (ℓ "乢丘义丘")
  (rw 0 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (ℓ "両丘") (ℓ "丘両") (low-comm ((CS • CS • CS)) (X))
  q12 : Eqn
  q12 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))

-- pass [X2 CS23 X2] [CSd01]: 3 steps
lem-pass-X2-CS23-X2-vs-CSd01 : ⟪ (ℓ "丘义丘両") ⟫ʷ ≈ ⟪ (ℓ "両丘义丘") ⟫ʷ
lem-pass-X2-CS23-X2-vs-CSd01 = derive (ℓ "丘义丘両") (ℓ "両丘义丘")
  (rw⁻ 2 q11 ∷
   rw⁻ 1 q12 ∷
   rw⁻ 0 q11 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))

-- pass [X2 CK23 X2] [CS01]: 3 steps
lem-pass-X2-CK23-X2-vs-CS01 : ⟪ (ℓ "丘乍丘丠") ⟫ʷ ≈ ⟪ (ℓ "丠丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS01 = derive (ℓ "丘乍丘丠") (ℓ "丠丘乍丘")
  (rw⁻ 2 q8 ∷
   rw⁻ 1 q13 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1020 W

-- pass [X2 CK23 X2] [TOFF123]: 1 steps
lem-pass-X2-CK23-X2-vs-TOFF123 : ⟪ (ℓ "丘乍丘乢") ⟫ʷ ≈ ⟪ (ℓ "乢丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-TOFF123 = derive (ℓ "丘乍丘乢") (ℓ "乢丘乍丘")
  (rw 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (ℓ "両乍") (ℓ "乍両") (low-comm ((CS • CS • CS)) (CK₀₁))

-- pass [X2 CK23 X2] [CSd01]: 3 steps
lem-pass-X2-CK23-X2-vs-CSd01 : ⟪ (ℓ "丘乍丘両") ⟫ʷ ≈ ⟪ (ℓ "両丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-CSd01 = derive (ℓ "丘乍丘両") (ℓ "両丘乍丘")
  (rw⁻ 2 q11 ∷
   rw⁻ 1 q15 ∷
   rw⁻ 0 q11 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))

-- pass [X2 CSd23 X2] [CS01]: 3 steps
lem-pass-X2-CSd23-X2-vs-CS01 : ⟪ (ℓ "丘乊丘丠") ⟫ʷ ≈ ⟪ (ℓ "丠丘乊丘") ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS01 = derive (ℓ "丘乊丘丠") (ℓ "丠丘乊丘")
  (rw⁻ 2 q8 ∷
   rw⁻ 1 q16 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 1021 W

-- pass [X2 CSd23 X2] [TOFF123]: 1 steps
lem-pass-X2-CSd23-X2-vs-TOFF123 : ⟪ (ℓ "丘乊丘乢") ⟫ʷ ≈ ⟪ (ℓ "乢丘乊丘") ⟫ʷ
lem-pass-X2-CSd23-X2-vs-TOFF123 = derive (ℓ "丘乊丘乢") (ℓ "乢丘乊丘")
  (rw 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [X2 CSd23 X2] [CSd01]: 3 steps
lem-pass-X2-CSd23-X2-vs-CSd01 : ⟪ (ℓ "丘乊丘両") ⟫ʷ ≈ ⟪ (ℓ "両丘乊丘") ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CSd01 = derive (ℓ "丘乊丘両") (ℓ "両丘乊丘")
  (rw⁻ 2 q11 ∷
   rw⁻ 1 q18 ∷
   rw⁻ 0 q11 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1022 W

-- pass [CCZ123] [X2 CS12 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CS12-X2 : ⟪ (ℓ "乜丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-CS12-X2 = derive (ℓ "乜丘丶丘") (ℓ "丘丶丘乜")
  (rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1023 W

-- pass [CCZ123] [X2 CK21 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CK21-X2 : ⟪ (ℓ "乜丘乇丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-CK21-X2 = derive (ℓ "乜丘乇丘") (ℓ "丘乇丘乜")
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1024 W

-- pass [CZ13] [CS13]: 1 steps
lem-pass-CZ13-vs-CS13 : ⟪ (ℓ "丿丽") ⟫ʷ ≈ ⟪ (ℓ "丽丿") ⟫ʷ
lem-pass-CZ13-vs-CS13 = derive (ℓ "丿丽") (ℓ "丽丿")
  (rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 1025 W

-- pass [Z1] [CS13]: 1 steps
lem-pass-Z1-vs-CS13 : ⟪ (ℓ "专丽") ⟫ʷ ≈ ⟪ (ℓ "丽专") ⟫ʷ
lem-pass-Z1-vs-CS13 = derive (ℓ "专丽") (ℓ "丽专")
  (rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1026 W

-- pass [CZ13] [CSd13]: 1 steps
lem-pass-CZ13-vs-CSd13 : ⟪ (ℓ "丿举") ⟫ʷ ≈ ⟪ (ℓ "举丿") ⟫ʷ
lem-pass-CZ13-vs-CSd13 = derive (ℓ "丿举") (ℓ "举丿")
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1027 W

-- pass [Z1] [CSd13]: 1 steps
lem-pass-Z1-vs-CSd13 : ⟪ (ℓ "专举") ⟫ʷ ≈ ⟪ (ℓ "举专") ⟫ʷ
lem-pass-Z1-vs-CSd13 = derive (ℓ "专举") (ℓ "举专")
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 1028 W

-- pass [CCZ123] [X2 CKd21 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CKd21-X2 : ⟪ (ℓ "乜丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘么丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-CKd21-X2 = derive (ℓ "乜丘么丘") (ℓ "丘么丘乜")
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1029 W

-- pass [CCZ123] [X2 CSd12 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CSd12-X2 : ⟪ (ℓ "乜丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-CSd12-X2 = derive (ℓ "乜丘丷丘") (ℓ "丘丷丘乜")
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (ℓ "丠乎") (ℓ "乎丠") (low-comm (CS) ((S • CK₀₁)))

-- pass [X2 CKd23 X2] [CS01]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS01 : ⟪ (ℓ "丘乎丘丠") ⟫ʷ ≈ ⟪ (ℓ "丠丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS01 = derive (ℓ "丘乎丘丠") (ℓ "丠丘乎丘")
  (rw⁻ 2 q8 ∷
   rw⁻ 1 q27 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 1030 W

-- pass [X2 CKd23 X2] [TOFF123]: 1 steps
lem-pass-X2-CKd23-X2-vs-TOFF123 : ⟪ (ℓ "丘乎丘乢") ⟫ʷ ≈ ⟪ (ℓ "乢丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-TOFF123 = derive (ℓ "丘乎丘乢") (ℓ "乢丘乎丘")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (ℓ "両乎") (ℓ "乎両") (low-comm ((CS • CS • CS)) ((S • CK₀₁)))

-- pass [X2 CKd23 X2] [CSd01]: 3 steps
lem-pass-X2-CKd23-X2-vs-CSd01 : ⟪ (ℓ "丘乎丘両") ⟫ʷ ≈ ⟪ (ℓ "両丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CSd01 = derive (ℓ "丘乎丘両") (ℓ "両丘乎丘")
  (rw⁻ 2 q11 ∷
   rw⁻ 1 q29 ∷
   rw⁻ 0 q11 ∷ []) Eq.refl
