{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)

module Examples.Groups.Clifford+CS.Five.D.D001 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

private
  q1 : Ws → Eqn
  q1 c4 = wpE 8 c4
  q2 : Ws → Eqn
  q2 c4 = wpE 111 c4

-- sym-ab: 18 steps
lem-sym-ab : Ws → ⟪ (ℓ "亹") ⟫ʷ ≈ ⟪ (ℓ "仌") ⟫ʷ
lem-sym-ab c4 = derive (ℓ "亹") (ℓ "仌")
  (re 0 1 (ℓ "二亍亸亍二亸") ∷
   re 2 1 (ℓ "亐互亷互亐亷") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (ℓ "今") ∷
   re 7 1 (ℓ "今") ∷
   re 2 6 (ℓ "介") ∷
   re 5 1 (ℓ "亐互亷互亐亷") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "今") ∷
   re 10 1 (ℓ "今") ∷
   re 5 6 (ℓ "介") ∷
   re 0 6 (ℓ "仌") ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = wpE 115 c4
  q4 : Ws → Eqn
  q4 c4 = wlE 268 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (ℓ "二乽") (ℓ "乽二") (c₃ (CCZ) (CX₀₁))
  q6 : Ws → Eqn
  q6 c4 = wpE 116 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 117 c4

-- cQ @13243142: 7 steps
lem-cQ-at13243142 : Ws → ⟪ (ℓ "亠二") ⟫ʷ ≈ ⟪ (ℓ "二亠") ⟫ʷ
lem-cQ-at13243142 c4 = derive (ℓ "亠二") (ℓ "二亠")
  (rw 0 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q3 c4) ∷ []) Eq.refl

-- cQ @13243241: 7 steps
lem-cQ-at13243241 : Ws → ⟪ (ℓ "亠二") ⟫ʷ ≈ ⟪ (ℓ "二亠") ⟫ʷ
lem-cQ-at13243241 c4 = derive (ℓ "亠二") (ℓ "二亠")
  (rw 0 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q3 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = wpE 130 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 131 c4

-- sym-ab @2332: 18 steps
lem-sym-ab-at2332 : Ws → ⟪ (ℓ "亾") ⟫ʷ ≈ ⟪ (ℓ "令") ⟫ʷ
lem-sym-ab-at2332 c4 = derive (ℓ "亾") (ℓ "令")
  (re 0 1 (ℓ "亐云亽云亐亽") ∷
   re 2 1 (ℓ "二于亷于二亷") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (ℓ "仢") ∷
   re 7 1 (ℓ "仢") ∷
   re 2 6 (ℓ "代") ∷
   re 5 1 (ℓ "二于亷于二亷") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 7 1 (ℓ "仢") ∷
   re 10 1 (ℓ "仢") ∷
   re 5 6 (ℓ "代") ∷
   re 0 6 (ℓ "令") ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = wlE 269 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wpE 136 c4

-- sym-ab @13243142: 18 steps
lem-sym-ab-at13243142 : Ws → ⟪ (ℓ "仳") ⟫ʷ ≈ ⟪ (ℓ "伋") ⟫ʷ
lem-sym-ab-at13243142 c4 = derive (ℓ "仳") (ℓ "伋")
  (re 0 1 (ℓ "亠亡仲亡亠仲") ∷
   re 2 1 (ℓ "亐亓仧亓亐仧") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   re 4 1 (ℓ "仿") ∷
   re 7 1 (ℓ "仿") ∷
   re 2 6 (ℓ "伊") ∷
   re 5 1 (ℓ "亐亓仧亓亐仧") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   re 7 1 (ℓ "仿") ∷
   re 10 1 (ℓ "仿") ∷
   re 5 6 (ℓ "伊") ∷
   re 0 6 (ℓ "伋") ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = wpE 153 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 154 c4

-- sym-ab @122331: 18 steps
lem-sym-ab-at122331 : Ws → ⟪ (ℓ "仕") ⟫ʷ ≈ ⟪ (ℓ "仭") ⟫ʷ
lem-sym-ab-at122331 c4 = derive (ℓ "仕") (ℓ "仭")
  (re 0 1 (ℓ "亘亙仔亙亘仔") ∷
   re 2 1 (ℓ "二亏今亏二今") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw 2 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   re 4 1 (ℓ "仢") ∷
   re 7 1 (ℓ "仢") ∷
   re 2 6 (ℓ "们") ∷
   re 5 1 (ℓ "二亏今亏二今") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw 5 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 7 1 (ℓ "仢") ∷
   re 10 1 (ℓ "仢") ∷
   re 5 6 (ℓ "们") ∷
   re 0 6 (ℓ "仭") ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wlE 288 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 162 c4

-- sym-ab @13243241: 18 steps
lem-sym-ab-at13243241 : Ws → ⟪ (ℓ "件") ⟫ʷ ≈ ⟪ (ℓ "伍") ⟫ʷ
lem-sym-ab-at13243241 c4 = derive (ℓ "件") (ℓ "伍")
  (re 0 1 (ℓ "亠亡仵亡亠仵") ∷
   re 2 1 (ℓ "亘些仟些亘仟") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   re 4 1 (ℓ "价") ∷
   re 7 1 (ℓ "价") ∷
   re 2 6 (ℓ "伌") ∷
   re 5 1 (ℓ "亘些仟些亘仟") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q14 c4) ∷
   rw 5 (q15 c4) ∷
   re 7 1 (ℓ "价") ∷
   re 10 1 (ℓ "价") ∷
   re 5 6 (ℓ "伌") ∷
   re 0 6 (ℓ "伍") ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = wlE 292 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 180 c4

-- sym-ab @12243143: 18 steps
lem-sym-ab-at12243143 : Ws → ⟪ (ℓ "仛") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-sym-ab-at12243143 c4 = derive (ℓ "仛") (ℓ "伅")
  (re 0 1 (ℓ "亜亝仚亝亜仚") ∷
   re 2 1 (ℓ "二亏仏亏二仏") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw 2 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   re 4 1 (ℓ "仺") ∷
   re 7 1 (ℓ "仺") ∷
   re 2 6 (ℓ "伄") ∷
   re 5 1 (ℓ "二亏仏亏二仏") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw 5 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   re 7 1 (ℓ "仺") ∷
   re 10 1 (ℓ "仺") ∷
   re 5 6 (ℓ "伄") ∷
   re 0 6 (ℓ "伅") ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = wpE 198 c4
  q19 : Ws → Eqn
  q19 c4 = eqn (ℓ "二争") (ℓ "争二") (c₃ (CCZ) (CX₁₀))
  q20 : Ws → Eqn
  q20 c4 = wlE 328 (lit c4)

-- cQ @14233142: 7 steps
lem-cQ-at14233142 : Ws → ⟪ (ℓ "亠二") ⟫ʷ ≈ ⟪ (ℓ "二亠") ⟫ʷ
lem-cQ-at14233142 c4 = derive (ℓ "亠二") (ℓ "二亠")
  (rw 0 (q18 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q18 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wpE 211 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 212 c4

-- sym-ab @13213442: 18 steps
lem-sym-ab-at13213442 : Ws → ⟪ (ℓ "仩") ⟫ʷ ≈ ⟪ (ℓ "仂") ⟫ʷ
lem-sym-ab-at13213442 c4 = derive (ℓ "仩") (ℓ "仂")
  (re 0 1 (ℓ "亐云仨云亐仨") ∷
   re 2 1 (ℓ "亠亢仧亢亠仧") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   re 4 1 (ℓ "亴") ∷
   re 7 1 (ℓ "亴") ∷
   re 2 6 (ℓ "仁") ∷
   re 5 1 (ℓ "亠亢仧亢亠仧") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   re 7 1 (ℓ "亴") ∷
   re 10 1 (ℓ "亴") ∷
   re 5 6 (ℓ "仁") ∷
   re 0 6 (ℓ "仂") ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = wlE 205 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 216 c4

-- sym-ab @243243: 18 steps
lem-sym-ab-at243243 : Ws → ⟪ (ℓ "仄") ⟫ʷ ≈ ⟪ (ℓ "仼") ⟫ʷ
lem-sym-ab-at243243 c4 = derive (ℓ "仄") (ℓ "仼")
  (re 0 1 (ℓ "五井仃井五仃") ∷
   re 2 1 (ℓ "二于人于二人") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw 2 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   re 4 1 (ℓ "仺") ∷
   re 7 1 (ℓ "仺") ∷
   re 2 6 (ℓ "任") ∷
   re 5 1 (ℓ "二于人于二人") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw 5 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   re 7 1 (ℓ "仺") ∷
   re 10 1 (ℓ "仺") ∷
   re 5 6 (ℓ "任") ∷
   re 0 6 (ℓ "仼") ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = wpE 217 c4
  q26 : Ws → Eqn
  q26 c4 = wpE 218 c4

-- sym-ab @133441: 18 steps
lem-sym-ab-at133441 : Ws → ⟪ (ℓ "仰") ⟫ʷ ≈ ⟪ (ℓ "付") ⟫ʷ
lem-sym-ab-at133441 c4 = derive (ℓ "仰") (ℓ "付")
  (re 0 1 (ℓ "亘亙仯亙亘仯") ∷
   re 2 1 (ℓ "亠亢仟亢亠仟") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   re 4 1 (ℓ "仇") ∷
   re 7 1 (ℓ "仇") ∷
   re 2 6 (ℓ "仗") ∷
   re 5 1 (ℓ "亠亢仟亢亠仟") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   re 7 1 (ℓ "仇") ∷
   re 10 1 (ℓ "仇") ∷
   re 5 6 (ℓ "仗") ∷
   re 0 6 (ℓ "付") ∷ []) Eq.refl

-- sym-ab @12233441: 18 steps
lem-sym-ab-at12233441 : Ws → ⟪ (ℓ "付") ⟫ʷ ≈ ⟪ (ℓ "仰") ⟫ʷ
lem-sym-ab-at12233441 c4 = derive (ℓ "付") (ℓ "仰")
  (re 0 1 (ℓ "亘亙仗亙亘仗") ∷
   re 2 1 (ℓ "亜亞仇亞亜仇") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q26 c4) ∷
   rw 2 (q25 c4) ∷
   re 4 1 (ℓ "仟") ∷
   re 7 1 (ℓ "仟") ∷
   re 2 6 (ℓ "仯") ∷
   re 5 1 (ℓ "亜亞仇亞亜仇") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q26 c4) ∷
   rw 5 (q25 c4) ∷
   re 7 1 (ℓ "仟") ∷
   re 10 1 (ℓ "仟") ∷
   re 5 6 (ℓ "仯") ∷
   re 0 6 (ℓ "仰") ∷ []) Eq.refl

-- sym-ab @1221: 18 steps
lem-sym-ab-at1221 : Ws → ⟪ (ℓ "仌") ⟫ʷ ≈ ⟪ (ℓ "亹") ⟫ʷ
lem-sym-ab-at1221 c4 = derive (ℓ "仌") (ℓ "亹")
  (re 0 1 (ℓ "二亍介亍二介") ∷
   re 2 1 (ℓ "亘亚今亚亘今") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw 2 (q2 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (ℓ "亷") ∷
   re 7 1 (ℓ "亷") ∷
   re 2 6 (ℓ "亸") ∷
   re 5 1 (ℓ "亘亚今亚亘今") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 7 1 (ℓ "亷") ∷
   re 10 1 (ℓ "亷") ∷
   re 5 6 (ℓ "亸") ∷
   re 0 6 (ℓ "亹") ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wlE 348 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 279 c4
  q29 : Ws → Eqn
  q29 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))
  q30 : Ws → Eqn
  q30 c4 = wlE 414 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 415 (lit c4)

-- cQ @021021: 7 steps
lem-cQ-at021021 : Ws → ⟪ (ℓ "二亰") ⟫ʷ ≈ ⟪ (ℓ "亰二") ⟫ʷ
lem-cQ-at021021 c4 = derive (ℓ "二亰") (ℓ "亰二")
  (rw 0 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q27 c4) ∷ []) Eq.refl

-- sym-ab @233442: 18 steps
lem-sym-ab-at233442 : Ws → ⟪ (ℓ "仂") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-sym-ab-at233442 c4 = derive (ℓ "仂") (ℓ "仩")
  (re 0 1 (ℓ "亐云仁云亐仁") ∷
   re 2 1 (ℓ "五亖亴亖五亴") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q22 c4) ∷
   rw 2 (q21 c4) ∷
   re 4 1 (ℓ "仧") ∷
   re 7 1 (ℓ "仧") ∷
   re 2 6 (ℓ "仨") ∷
   re 5 1 (ℓ "五亖亴亖五亴") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   re 7 1 (ℓ "仧") ∷
   re 10 1 (ℓ "仧") ∷
   re 5 6 (ℓ "仨") ∷
   re 0 6 (ℓ "仩") ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = wlE 184 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = wpE 294 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 432 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 433 (lit c4)

-- cQ @03102132: 7 steps
lem-cQ-at03102132 : Ws → ⟪ (ℓ "亐亰") ⟫ʷ ≈ ⟪ (ℓ "亰亐") ⟫ʷ
lem-cQ-at03102132 c4 = derive (ℓ "亐亰") (ℓ "亰亐")
  (rw 0 (q32 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q32 c4) ∷ []) Eq.refl

-- sym-ab @14233142: 18 steps
lem-sym-ab-at14233142 : Ws → ⟪ (ℓ "伋") ⟫ʷ ≈ ⟪ (ℓ "仳") ⟫ʷ
lem-sym-ab-at14233142 c4 = derive (ℓ "伋") (ℓ "仳")
  (re 0 1 (ℓ "亠亡伊亡亠伊") ∷
   re 2 1 (ℓ "五亗仿亗五仿") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q11 c4) ∷
   rw 2 (q10 c4) ∷
   re 4 1 (ℓ "仧") ∷
   re 7 1 (ℓ "仧") ∷
   re 2 6 (ℓ "仲") ∷
   re 5 1 (ℓ "五亗仿亗五仿") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw⁻ 5 (q11 c4) ∷
   rw 5 (q10 c4) ∷
   re 7 1 (ℓ "仧") ∷
   re 10 1 (ℓ "仧") ∷
   re 5 6 (ℓ "仲") ∷
   re 0 6 (ℓ "仳") ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wpE 301 c4
  q37 : Ws → Eqn
  q37 c4 = wpE 302 c4
  q38 : Ws → Eqn
  q38 c4 = wlE 451 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 452 (lit c4)

-- cQ @0410213243: 7 steps
lem-cQ-at0410213243 : Ws → ⟪ (ℓ "五亰") ⟫ʷ ≈ ⟪ (ℓ "亰五") ⟫ʷ
lem-cQ-at0410213243 c4 = derive (ℓ "五亰") (ℓ "亰五")
  (rw 0 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q36 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = wpE 341 c4
  q41 : Ws → Eqn
  q41 c4 = eqn (ℓ "乄亰") (ℓ "亰乄") (c₂ (CX₁₀) (CCZ))
  q42 : Ws → Eqn
  q42 c4 = wpE 342 c4

-- cQ @04203243: 7 steps
lem-cQ-at04203243 : Ws → ⟪ (ℓ "五亰") ⟫ʷ ≈ ⟪ (ℓ "亰五") ⟫ʷ
lem-cQ-at04203243 c4 = derive (ℓ "五亰") (ℓ "亰五")
  (rw 0 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q37 c4) ∷
   rw⁻ 1 (q40 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = wlE 486 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wpE 305 c4

-- sym-ab @04203243: 18 steps
lem-sym-ab-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "侍") ⟫ʷ
lem-sym-ab-at04203243 c4 = derive (ℓ "侒") (ℓ "侍")
  (re 0 1 (ℓ "五亗伫亗五伫") ∷
   re 2 1 (ℓ "亨亩伤亩亨伤") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw 2 (q43 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   re 4 1 (ℓ "份") ∷
   re 7 1 (ℓ "份") ∷
   re 2 6 (ℓ "伆") ∷
   re 5 1 (ℓ "亨亩伤亩亨伤") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw 5 (q43 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (ℓ "份") ∷
   re 10 1 (ℓ "份") ∷
   re 5 6 (ℓ "伆") ∷
   re 0 6 (ℓ "侍") ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wlE 493 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 494 (lit c4)

-- sym-ab @0310243142: 18 steps
lem-sym-ab-at0310243142 : Ws → ⟪ (ℓ "佨") ⟫ʷ ≈ ⟪ (ℓ "佹") ⟫ʷ
lem-sym-ab-at0310243142 c4 = derive (ℓ "佨") (ℓ "佹")
  (re 0 1 (ℓ "亠亢仡亢亠仡") ∷
   re 2 1 (ℓ "亐云仠云亐仠") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw 2 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   re 4 1 (ℓ "佷") ∷
   re 7 1 (ℓ "佷") ∷
   re 2 6 (ℓ "佸") ∷
   re 5 1 (ℓ "亐云仠云亐仠") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw 5 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   re 7 1 (ℓ "佷") ∷
   re 10 1 (ℓ "佷") ∷
   re 5 6 (ℓ "佸") ∷
   re 0 6 (ℓ "佹") ∷ []) Eq.refl

-- sym-ab @0314203142: 18 steps
lem-sym-ab-at0314203142 : Ws → ⟪ (ℓ "佹") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-sym-ab-at0314203142 c4 = derive (ℓ "佹") (ℓ "佨")
  (re 0 1 (ℓ "亠亢佸亢亠佸") ∷
   re 2 1 (ℓ "京亯佷亯京佷") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q46 c4) ∷
   rw⁻ 2 (q45 c4) ∷
   re 4 1 (ℓ "仠") ∷
   re 7 1 (ℓ "仠") ∷
   re 2 6 (ℓ "仡") ∷
   re 5 1 (ℓ "京亯佷亯京佷") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw⁻ 5 (q46 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   re 7 1 (ℓ "仠") ∷
   re 10 1 (ℓ "仠") ∷
   re 5 6 (ℓ "仡") ∷
   re 0 6 (ℓ "佨") ∷ []) Eq.refl

-- sym-ab @0410213243: 18 steps
lem-sym-ab-at0410213243 : Ws → ⟪ (ℓ "侍") ⟫ʷ ≈ ⟪ (ℓ "侒") ⟫ʷ
lem-sym-ab-at0410213243 c4 = derive (ℓ "侍") (ℓ "侒")
  (re 0 1 (ℓ "五亗伆亗五伆") ∷
   re 2 1 (ℓ "亜亝份亝亜份") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q44 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (ℓ "伤") ∷
   re 7 1 (ℓ "伤") ∷
   re 2 6 (ℓ "伫") ∷
   re 5 1 (ℓ "亜亝份亝亜份") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q44 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   re 7 1 (ℓ "伤") ∷
   re 10 1 (ℓ "伤") ∷
   re 5 6 (ℓ "伫") ∷
   re 0 6 (ℓ "侒") ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = wpE 280 c4
  q48 : Ws → Eqn
  q48 c4 = wlE 518 (lit c4)

-- sym-ab @03102132: 18 steps
lem-sym-ab-at03102132 : Ws → ⟪ (ℓ "佤") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-sym-ab-at03102132 c4 = derive (ℓ "佤") (ℓ "佪")
  (re 0 1 (ℓ "亐亓仮亓亐仮") ∷
   re 2 1 (ℓ "亘亙以亙亘以") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q47 c4) ∷
   rw⁻ 2 (q48 c4) ∷
   re 4 1 (ℓ "伛") ∷
   re 7 1 (ℓ "伛") ∷
   re 2 6 (ℓ "伟") ∷
   re 5 1 (ℓ "亘亙以亙亘以") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q47 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 7 1 (ℓ "伛") ∷
   re 10 1 (ℓ "伛") ∷
   re 5 6 (ℓ "伟") ∷
   re 0 6 (ℓ "佪") ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 477 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 363 c4

-- cQ @032032: 7 steps
lem-cQ-at032032 : Ws → ⟪ (ℓ "亐亰") ⟫ʷ ≈ ⟪ (ℓ "亰亐") ⟫ʷ
lem-cQ-at032032 c4 = derive (ℓ "亐亰") (ℓ "亰亐")
  (rw 0 (q49 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw⁻ 1 (q49 c4) ∷ []) Eq.refl

-- sym-ab @032032: 18 steps
lem-sym-ab-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "佤") ⟫ʷ
lem-sym-ab-at032032 c4 = derive (ℓ "佪") (ℓ "佤")
  (re 0 1 (ℓ "亐亓伟亓亐伟") ∷
   re 2 1 (ℓ "交亥伛亥交伛") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q48 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   re 4 1 (ℓ "以") ∷
   re 7 1 (ℓ "以") ∷
   re 2 6 (ℓ "仮") ∷
   re 5 1 (ℓ "交亥伛亥交伛") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q48 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   re 7 1 (ℓ "以") ∷
   re 10 1 (ℓ "以") ∷
   re 5 6 (ℓ "仮") ∷
   re 0 6 (ℓ "佤") ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = wpE 398 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 399 c4
  q53 : Ws → Eqn
  q53 c4 = wpE 400 c4
  q54 : Ws → Eqn
  q54 c4 = wlE 548 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = wpE 401 c4
  q56 : Ws → Eqn
  q56 c4 = wpE 402 c4
  q57 : Ws → Eqn
  q57 c4 = wlE 4 (lit c4)

-- nat-S: 31 steps
lem-nat-S : Ws → ⟪ (ℓ "乼俐乼") ⟫ʷ ≈ ⟪ (ℓ "俢") ⟫ʷ
lem-nat-S c4 = derive (ℓ "乼俐乼") (ℓ "俢")
  (re 1 1 (ℓ "佤享俎享俏") ∷
   re 3 1 (ℓ "丽") ∷
   re 5 1 (ℓ "举") ∷
   re 1 1 (ℓ "亐亓仮亓亐仮") ∷
   rw⁻ 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   re 3 1 (ℓ "亘亙以亙亘以") ∷
   re 5 1 (ℓ "丿") ∷
   re 8 1 (ℓ "丿") ∷
   rw⁻ 2 (q53 c4) ∷
   re 4 1 (ℓ "份") ∷
   re 7 1 (ℓ "份") ∷
   re 2 6 (ℓ "伆") ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q51 c4) ∷
   re 6 1 (ℓ "亘亙以亙亘以") ∷
   re 8 1 (ℓ "丿") ∷
   re 11 1 (ℓ "丿") ∷
   rw⁻ 5 (q53 c4) ∷
   re 7 1 (ℓ "份") ∷
   re 10 1 (ℓ "份") ∷
   re 5 6 (ℓ "伆") ∷
   rw 6 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   rw 10 (q57 c4) ∷
   re 0 6 (ℓ "侍") ∷
   re 2 1 (ℓ "俠") ∷
   re 4 1 (ℓ "信") ∷
   re 0 5 (ℓ "俢") ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = wlE 549 (lit c4)

-- F4-I-I: 1 steps
lem-F4-I-I : Ws → ⟪ (ℓ "並丢並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並丢並") ⟫ʷ
lem-F4-I-I c4 = derive (ℓ "並丢並丢") (ℓ "丢並丢並")
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = wpE 403 c4

-- F4-I-S0: 1 steps
lem-F4-I-S0 : Ws → ⟪ (ℓ "並丢並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並丢並") ⟫ʷ
lem-F4-I-S0 c4 = derive (ℓ "並丢並丽") (ℓ "丽並丢並")
  (rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = wlE 550 (lit c4)

-- F4-I-S1: 1 steps
lem-F4-I-S1 : Ws → ⟪ (ℓ "並丢並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並丢並") ⟫ʷ
lem-F4-I-S1 c4 = derive (ℓ "並丢並乕") (ℓ "乕並丢並")
  (rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 551 (lit c4)

-- F4-I-S2: 1 steps
lem-F4-I-S2 : Ws → ⟪ (ℓ "並丢並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並丢並") ⟫ʷ
lem-F4-I-S2 c4 = derive (ℓ "並丢並乩") (ℓ "乩並丢並")
  (rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = wlE 552 (lit c4)

-- F4-I-S3: 1 steps
lem-F4-I-S3 : Ws → ⟪ (ℓ "並丢並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並丢並") ⟫ʷ
lem-F4-I-S3 c4 = derive (ℓ "並丢並乹") (ℓ "乹並丢並")
  (rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = wpE 404 c4

-- F4-I-K0: 1 steps
lem-F4-I-K0 : Ws → ⟪ (ℓ "並丢並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並丢並") ⟫ʷ
lem-F4-I-K0 c4 = derive (ℓ "並丢並亁") (ℓ "亁並丢並")
  (rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = wlE 553 (lit c4)

-- F4-I-K1: 1 steps
lem-F4-I-K1 : Ws → ⟪ (ℓ "並丢並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並丢並") ⟫ʷ
lem-F4-I-K1 c4 = derive (ℓ "並丢並亄") (ℓ "亄並丢並")
  (rw⁻ 0 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 554 (lit c4)

-- F4-I-K2: 1 steps
lem-F4-I-K2 : Ws → ⟪ (ℓ "並丢並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並丢並") ⟫ʷ
lem-F4-I-K2 c4 = derive (ℓ "並丢並亇") (ℓ "亇並丢並")
  (rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 555 (lit c4)

-- F4-I-K3: 1 steps
lem-F4-I-K3 : Ws → ⟪ (ℓ "並丢並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並丢並") ⟫ʷ
lem-F4-I-K3 c4 = derive (ℓ "並丢並亊") (ℓ "亊並丢並")
  (rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = wpE 410 c4

-- F4-S0-I: 1 steps
lem-F4-S0-I : Ws → ⟪ (ℓ "並丽並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並丽並") ⟫ʷ
lem-F4-S0-I c4 = derive (ℓ "並丽並丢") (ℓ "丢並丽並")
  (rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wpE 411 c4

-- F4-S0-S0: 1 steps
lem-F4-S0-S0 : Ws → ⟪ (ℓ "並丽並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並丽並") ⟫ʷ
lem-F4-S0-S0 c4 = derive (ℓ "並丽並丽") (ℓ "丽並丽並")
  (rw⁻ 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = wpE 412 c4

-- F4-S0-S1: 1 steps
lem-F4-S0-S1 : Ws → ⟪ (ℓ "並丽並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並丽並") ⟫ʷ
lem-F4-S0-S1 c4 = derive (ℓ "並丽並乕") (ℓ "乕並丽並")
  (rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = wpE 413 c4

-- F4-S0-S2: 1 steps
lem-F4-S0-S2 : Ws → ⟪ (ℓ "並丽並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並丽並") ⟫ʷ
lem-F4-S0-S2 c4 = derive (ℓ "並丽並乩") (ℓ "乩並丽並")
  (rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = wpE 414 c4

-- F4-S0-S3: 1 steps
lem-F4-S0-S3 : Ws → ⟪ (ℓ "並丽並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並丽並") ⟫ʷ
lem-F4-S0-S3 c4 = derive (ℓ "並丽並乹") (ℓ "乹並丽並")
  (rw⁻ 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = wpE 415 c4

-- F4-S0-K0: 1 steps
lem-F4-S0-K0 : Ws → ⟪ (ℓ "並丽並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並丽並") ⟫ʷ
lem-F4-S0-K0 c4 = derive (ℓ "並丽並亁") (ℓ "亁並丽並")
  (rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = wpE 416 c4

-- F4-S0-K1: 1 steps
lem-F4-S0-K1 : Ws → ⟪ (ℓ "並丽並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並丽並") ⟫ʷ
lem-F4-S0-K1 c4 = derive (ℓ "並丽並亄") (ℓ "亄並丽並")
  (rw⁻ 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = wpE 417 c4

-- F4-S0-K2: 1 steps
lem-F4-S0-K2 : Ws → ⟪ (ℓ "並丽並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並丽並") ⟫ʷ
lem-F4-S0-K2 c4 = derive (ℓ "並丽並亇") (ℓ "亇並丽並")
  (rw⁻ 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = wpE 418 c4

-- F4-S0-K3: 1 steps
lem-F4-S0-K3 : Ws → ⟪ (ℓ "並丽並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並丽並") ⟫ʷ
lem-F4-S0-K3 c4 = derive (ℓ "並丽並亊") (ℓ "亊並丽並")
  (rw⁻ 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = wlE 563 (lit c4)

-- F4-S1-I: 1 steps
lem-F4-S1-I : Ws → ⟪ (ℓ "並乕並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並乕並") ⟫ʷ
lem-F4-S1-I c4 = derive (ℓ "並乕並丢") (ℓ "丢並乕並")
  (rw⁻ 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = wpE 440 c4

-- F4-S1-S0: 1 steps
lem-F4-S1-S0 : Ws → ⟪ (ℓ "並乕並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並乕並") ⟫ʷ
lem-F4-S1-S0 c4 = derive (ℓ "並乕並丽") (ℓ "丽並乕並")
  (rw⁻ 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = wlE 564 (lit c4)

-- F4-S1-S1: 1 steps
lem-F4-S1-S1 : Ws → ⟪ (ℓ "並乕並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並乕並") ⟫ʷ
lem-F4-S1-S1 c4 = derive (ℓ "並乕並乕") (ℓ "乕並乕並")
  (rw⁻ 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = wlE 565 (lit c4)

-- F4-S1-S2: 1 steps
lem-F4-S1-S2 : Ws → ⟪ (ℓ "並乕並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並乕並") ⟫ʷ
lem-F4-S1-S2 c4 = derive (ℓ "並乕並乩") (ℓ "乩並乕並")
  (rw⁻ 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = wlE 566 (lit c4)

-- F4-S1-S3: 1 steps
lem-F4-S1-S3 : Ws → ⟪ (ℓ "並乕並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並乕並") ⟫ʷ
lem-F4-S1-S3 c4 = derive (ℓ "並乕並乹") (ℓ "乹並乕並")
  (rw⁻ 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wpE 441 c4

-- F4-S1-K0: 1 steps
lem-F4-S1-K0 : Ws → ⟪ (ℓ "並乕並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並乕並") ⟫ʷ
lem-F4-S1-K0 c4 = derive (ℓ "並乕並亁") (ℓ "亁並乕並")
  (rw⁻ 0 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = wlE 567 (lit c4)

-- F4-S1-K1: 1 steps
lem-F4-S1-K1 : Ws → ⟪ (ℓ "並乕並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並乕並") ⟫ʷ
lem-F4-S1-K1 c4 = derive (ℓ "並乕並亄") (ℓ "亄並乕並")
  (rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = wlE 568 (lit c4)

-- F4-S1-K2: 1 steps
lem-F4-S1-K2 : Ws → ⟪ (ℓ "並乕並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並乕並") ⟫ʷ
lem-F4-S1-K2 c4 = derive (ℓ "並乕並亇") (ℓ "亇並乕並")
  (rw⁻ 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wlE 569 (lit c4)

-- F4-S1-K3: 1 steps
lem-F4-S1-K3 : Ws → ⟪ (ℓ "並乕並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並乕並") ⟫ʷ
lem-F4-S1-K3 c4 = derive (ℓ "並乕並亊") (ℓ "亊並乕並")
  (rw⁻ 0 (q84 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = wlE 575 (lit c4)

-- F4-S2-I: 1 steps
lem-F4-S2-I : Ws → ⟪ (ℓ "並乩並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並乩並") ⟫ʷ
lem-F4-S2-I c4 = derive (ℓ "並乩並丢") (ℓ "丢並乩並")
  (rw⁻ 0 (q85 c4) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = wpE 447 c4

-- F4-S2-S0: 1 steps
lem-F4-S2-S0 : Ws → ⟪ (ℓ "並乩並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並乩並") ⟫ʷ
lem-F4-S2-S0 c4 = derive (ℓ "並乩並丽") (ℓ "丽並乩並")
  (rw⁻ 0 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = wlE 576 (lit c4)

-- F4-S2-S1: 1 steps
lem-F4-S2-S1 : Ws → ⟪ (ℓ "並乩並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並乩並") ⟫ʷ
lem-F4-S2-S1 c4 = derive (ℓ "並乩並乕") (ℓ "乕並乩並")
  (rw⁻ 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = wlE 577 (lit c4)

-- F4-S2-S2: 1 steps
lem-F4-S2-S2 : Ws → ⟪ (ℓ "並乩並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並乩並") ⟫ʷ
lem-F4-S2-S2 c4 = derive (ℓ "並乩並乩") (ℓ "乩並乩並")
  (rw⁻ 0 (q88 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = wlE 578 (lit c4)

-- F4-S2-S3: 1 steps
lem-F4-S2-S3 : Ws → ⟪ (ℓ "並乩並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並乩並") ⟫ʷ
lem-F4-S2-S3 c4 = derive (ℓ "並乩並乹") (ℓ "乹並乩並")
  (rw⁻ 0 (q89 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = wpE 448 c4

-- F4-S2-K0: 1 steps
lem-F4-S2-K0 : Ws → ⟪ (ℓ "並乩並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並乩並") ⟫ʷ
lem-F4-S2-K0 c4 = derive (ℓ "並乩並亁") (ℓ "亁並乩並")
  (rw⁻ 0 (q90 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = wlE 579 (lit c4)

-- F4-S2-K1: 1 steps
lem-F4-S2-K1 : Ws → ⟪ (ℓ "並乩並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並乩並") ⟫ʷ
lem-F4-S2-K1 c4 = derive (ℓ "並乩並亄") (ℓ "亄並乩並")
  (rw⁻ 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = wlE 580 (lit c4)

-- F4-S2-K2: 1 steps
lem-F4-S2-K2 : Ws → ⟪ (ℓ "並乩並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並乩並") ⟫ʷ
lem-F4-S2-K2 c4 = derive (ℓ "並乩並亇") (ℓ "亇並乩並")
  (rw⁻ 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = wlE 581 (lit c4)

-- F4-S2-K3: 1 steps
lem-F4-S2-K3 : Ws → ⟪ (ℓ "並乩並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並乩並") ⟫ʷ
lem-F4-S2-K3 c4 = derive (ℓ "並乩並亊") (ℓ "亊並乩並")
  (rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = wlE 588 (lit c4)

-- F4-S3-I: 1 steps
lem-F4-S3-I : Ws → ⟪ (ℓ "並乹並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並乹並") ⟫ʷ
lem-F4-S3-I c4 = derive (ℓ "並乹並丢") (ℓ "丢並乹並")
  (rw⁻ 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = wpE 462 c4

-- F4-S3-S0: 1 steps
lem-F4-S3-S0 : Ws → ⟪ (ℓ "並乹並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並乹並") ⟫ʷ
lem-F4-S3-S0 c4 = derive (ℓ "並乹並丽") (ℓ "丽並乹並")
  (rw⁻ 0 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = wlE 589 (lit c4)

-- F4-S3-S1: 1 steps
lem-F4-S3-S1 : Ws → ⟪ (ℓ "並乹並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並乹並") ⟫ʷ
lem-F4-S3-S1 c4 = derive (ℓ "並乹並乕") (ℓ "乕並乹並")
  (rw⁻ 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = wlE 590 (lit c4)

-- F4-S3-S2: 1 steps
lem-F4-S3-S2 : Ws → ⟪ (ℓ "並乹並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並乹並") ⟫ʷ
lem-F4-S3-S2 c4 = derive (ℓ "並乹並乩") (ℓ "乩並乹並")
  (rw⁻ 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = wlE 591 (lit c4)

-- F4-S3-S3: 1 steps
lem-F4-S3-S3 : Ws → ⟪ (ℓ "並乹並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並乹並") ⟫ʷ
lem-F4-S3-S3 c4 = derive (ℓ "並乹並乹") (ℓ "乹並乹並")
  (rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = wpE 463 c4

-- F4-S3-K0: 1 steps
lem-F4-S3-K0 : Ws → ⟪ (ℓ "並乹並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並乹並") ⟫ʷ
lem-F4-S3-K0 c4 = derive (ℓ "並乹並亁") (ℓ "亁並乹並")
  (rw⁻ 0 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = wlE 592 (lit c4)

-- F4-S3-K1: 1 steps
lem-F4-S3-K1 : Ws → ⟪ (ℓ "並乹並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並乹並") ⟫ʷ
lem-F4-S3-K1 c4 = derive (ℓ "並乹並亄") (ℓ "亄並乹並")
  (rw⁻ 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = wlE 593 (lit c4)

-- F4-S3-K2: 1 steps
lem-F4-S3-K2 : Ws → ⟪ (ℓ "並乹並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並乹並") ⟫ʷ
lem-F4-S3-K2 c4 = derive (ℓ "並乹並亇") (ℓ "亇並乹並")
  (rw⁻ 0 (q101 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = wlE 594 (lit c4)

-- F4-S3-K3: 1 steps
lem-F4-S3-K3 : Ws → ⟪ (ℓ "並乹並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並乹並") ⟫ʷ
lem-F4-S3-K3 c4 = derive (ℓ "並乹並亊") (ℓ "亊並乹並")
  (rw⁻ 0 (q102 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = wpE 469 c4

-- F4-K0-I: 1 steps
lem-F4-K0-I : Ws → ⟪ (ℓ "並亁並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亁並") ⟫ʷ
lem-F4-K0-I c4 = derive (ℓ "並亁並丢") (ℓ "丢並亁並")
  (rw⁻ 0 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = wpE 470 c4

-- F4-K0-S0: 1 steps
lem-F4-K0-S0 : Ws → ⟪ (ℓ "並亁並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並亁並") ⟫ʷ
lem-F4-K0-S0 c4 = derive (ℓ "並亁並丽") (ℓ "丽並亁並")
  (rw⁻ 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = wpE 471 c4

-- F4-K0-S1: 1 steps
lem-F4-K0-S1 : Ws → ⟪ (ℓ "並亁並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亁並") ⟫ʷ
lem-F4-K0-S1 c4 = derive (ℓ "並亁並乕") (ℓ "乕並亁並")
  (rw⁻ 0 (q105 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = wpE 472 c4

-- F4-K0-S2: 1 steps
lem-F4-K0-S2 : Ws → ⟪ (ℓ "並亁並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並亁並") ⟫ʷ
lem-F4-K0-S2 c4 = derive (ℓ "並亁並乩") (ℓ "乩並亁並")
  (rw⁻ 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = wpE 473 c4

-- F4-K0-S3: 1 steps
lem-F4-K0-S3 : Ws → ⟪ (ℓ "並亁並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並亁並") ⟫ʷ
lem-F4-K0-S3 c4 = derive (ℓ "並亁並乹") (ℓ "乹並亁並")
  (rw⁻ 0 (q107 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = wpE 474 c4

-- F4-K0-K0: 1 steps
lem-F4-K0-K0 : Ws → ⟪ (ℓ "並亁並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並亁並") ⟫ʷ
lem-F4-K0-K0 c4 = derive (ℓ "並亁並亁") (ℓ "亁並亁並")
  (rw⁻ 0 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = wpE 475 c4

-- F4-K0-K1: 1 steps
lem-F4-K0-K1 : Ws → ⟪ (ℓ "並亁並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並亁並") ⟫ʷ
lem-F4-K0-K1 c4 = derive (ℓ "並亁並亄") (ℓ "亄並亁並")
  (rw⁻ 0 (q109 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = wpE 476 c4

-- F4-K0-K2: 1 steps
lem-F4-K0-K2 : Ws → ⟪ (ℓ "並亁並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並亁並") ⟫ʷ
lem-F4-K0-K2 c4 = derive (ℓ "並亁並亇") (ℓ "亇並亁並")
  (rw⁻ 0 (q110 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = wpE 477 c4

-- F4-K0-K3: 1 steps
lem-F4-K0-K3 : Ws → ⟪ (ℓ "並亁並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並亁並") ⟫ʷ
lem-F4-K0-K3 c4 = derive (ℓ "並亁並亊") (ℓ "亊並亁並")
  (rw⁻ 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = wlE 603 (lit c4)

-- F4-K1-I: 1 steps
lem-F4-K1-I : Ws → ⟪ (ℓ "並亄並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亄並") ⟫ʷ
lem-F4-K1-I c4 = derive (ℓ "並亄並丢") (ℓ "丢並亄並")
  (rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = wpE 494 c4

-- F4-K1-S0: 1 steps
lem-F4-K1-S0 : Ws → ⟪ (ℓ "並亄並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並亄並") ⟫ʷ
lem-F4-K1-S0 c4 = derive (ℓ "並亄並丽") (ℓ "丽並亄並")
  (rw⁻ 0 (q113 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = wlE 604 (lit c4)

-- F4-K1-S1: 1 steps
lem-F4-K1-S1 : Ws → ⟪ (ℓ "並亄並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亄並") ⟫ʷ
lem-F4-K1-S1 c4 = derive (ℓ "並亄並乕") (ℓ "乕並亄並")
  (rw⁻ 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = wlE 605 (lit c4)

-- F4-K1-S2: 1 steps
lem-F4-K1-S2 : Ws → ⟪ (ℓ "並亄並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並亄並") ⟫ʷ
lem-F4-K1-S2 c4 = derive (ℓ "並亄並乩") (ℓ "乩並亄並")
  (rw⁻ 0 (q115 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = wlE 606 (lit c4)

-- F4-K1-S3: 1 steps
lem-F4-K1-S3 : Ws → ⟪ (ℓ "並亄並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並亄並") ⟫ʷ
lem-F4-K1-S3 c4 = derive (ℓ "並亄並乹") (ℓ "乹並亄並")
  (rw⁻ 0 (q116 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = wpE 495 c4

-- F4-K1-K0: 1 steps
lem-F4-K1-K0 : Ws → ⟪ (ℓ "並亄並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並亄並") ⟫ʷ
lem-F4-K1-K0 c4 = derive (ℓ "並亄並亁") (ℓ "亁並亄並")
  (rw⁻ 0 (q117 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = wlE 607 (lit c4)

-- F4-K1-K1: 1 steps
lem-F4-K1-K1 : Ws → ⟪ (ℓ "並亄並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並亄並") ⟫ʷ
lem-F4-K1-K1 c4 = derive (ℓ "並亄並亄") (ℓ "亄並亄並")
  (rw⁻ 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = wlE 608 (lit c4)

-- F4-K1-K2: 1 steps
lem-F4-K1-K2 : Ws → ⟪ (ℓ "並亄並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並亄並") ⟫ʷ
lem-F4-K1-K2 c4 = derive (ℓ "並亄並亇") (ℓ "亇並亄並")
  (rw⁻ 0 (q119 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = wlE 609 (lit c4)

-- F4-K1-K3: 1 steps
lem-F4-K1-K3 : Ws → ⟪ (ℓ "並亄並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並亄並") ⟫ʷ
lem-F4-K1-K3 c4 = derive (ℓ "並亄並亊") (ℓ "亊並亄並")
  (rw⁻ 0 (q120 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = wlE 182 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wlE 610 (lit c4)

-- sym-ab @0210243143: 18 steps
lem-sym-ab-at0210243143 : Ws → ⟪ (ℓ "伱") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-sym-ab-at0210243143 c4 = derive (ℓ "伱") (ℓ "佔")
  (re 0 1 (ℓ "亜亞仉亞亜仉") ∷
   re 2 1 (ℓ "二亍仈亍二仈") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   re 4 1 (ℓ "佒") ∷
   re 7 1 (ℓ "佒") ∷
   re 2 6 (ℓ "体") ∷
   re 5 1 (ℓ "二亍仈亍二仈") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q121 c4) ∷
   rw 5 (q122 c4) ∷
   re 7 1 (ℓ "佒") ∷
   re 10 1 (ℓ "佒") ∷
   re 5 6 (ℓ "体") ∷
   re 0 6 (ℓ "佔") ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = wpE 509 c4
  q124 : Ws → Eqn
  q124 c4 = wpE 510 c4
  q125 : Ws → Eqn
  q125 c4 = wpE 511 c4
  q126 : Ws → Eqn
  q126 c4 = wpE 512 c4
  q127 : Ws → Eqn
  q127 c4 = eqn (ℓ "丫佒") (ℓ "佒丫") (c₂ (Swap) (CZ ↑))
  q128 : Ws → Eqn
  q128 c4 = wlE 18 (lit c4)

-- nat-SWbc @0214203143: 23 steps
lem-nat-SWbc-at0214203143 : Ws → ⟪ (ℓ "丫佔丫") ⟫ʷ ≈ ⟪ (ℓ "佝") ⟫ʷ
lem-nat-SWbc-at0214203143 c4 = derive (ℓ "丫佔丫") (ℓ "佝")
  (re 1 1 (ℓ "亜亞体亞亜体") ∷
   rw⁻ 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   re 3 1 (ℓ "亨享佒享亨佒") ∷
   rw⁻ 2 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw 4 (q127 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw 7 (q127 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 9 (q123 c4) ∷
   re 11 1 (ℓ "亨享佒享亨佒") ∷
   rw⁻ 10 (q125 c4) ∷
   rw 11 (q126 c4) ∷
   rw 12 (q127 c4) ∷
   rw 13 (q126 c4) ∷
   rw⁻ 14 (q125 c4) ∷
   rw 15 (q127 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (ℓ "作") ∷
   re 5 6 (ℓ "作") ∷
   re 0 6 (ℓ "佝") ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = wpE 527 c4
  q130 : Ws → Eqn
  q130 c4 = wpE 528 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 529 c4
  q132 : Ws → Eqn
  q132 c4 = wpE 530 c4
  q133 : Ws → Eqn
  q133 c4 = eqn (ℓ "仇乼") (ℓ "乼仇") (c₃ (CZ ↑) (Swap))

-- nat-SWbc @122441: 23 steps
lem-nat-SWbc-at122441 : Ws → ⟪ (ℓ "乼仞乼") ⟫ʷ ≈ ⟪ (ℓ "付") ⟫ʷ
lem-nat-SWbc-at122441 c4 = derive (ℓ "乼仞乼") (ℓ "付")
  (re 1 1 (ℓ "亜亝仝亝亜仝") ∷
   rw⁻ 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   re 3 1 (ℓ "亘亚仇亚亘仇") ∷
   rw⁻ 2 (q131 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 6 (q131 c4) ∷
   rw⁻ 7 (q133 c4) ∷
   rw 8 (q130 c4) ∷
   rw⁻ 9 (q129 c4) ∷
   re 11 1 (ℓ "亘亚仇亚亘仇") ∷
   rw⁻ 10 (q131 c4) ∷
   rw 11 (q132 c4) ∷
   rw⁻ 12 (q133 c4) ∷
   rw 13 (q132 c4) ∷
   rw⁻ 14 (q131 c4) ∷
   rw⁻ 15 (q133 c4) ∷
   rw 16 (q57 c4) ∷
   re 2 6 (ℓ "仗") ∷
   re 5 6 (ℓ "仗") ∷
   re 0 6 (ℓ "付") ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wlE 655 (lit c4)

-- F4-K2-I: 1 steps
lem-F4-K2-I : Ws → ⟪ (ℓ "並亇並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亇並") ⟫ʷ
lem-F4-K2-I c4 = derive (ℓ "並亇並丢") (ℓ "丢並亇並")
  (rw⁻ 0 (q134 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = wpE 532 c4

-- F4-K2-S0: 1 steps
lem-F4-K2-S0 : Ws → ⟪ (ℓ "並亇並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並亇並") ⟫ʷ
lem-F4-K2-S0 c4 = derive (ℓ "並亇並丽") (ℓ "丽並亇並")
  (rw⁻ 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = wlE 656 (lit c4)

-- F4-K2-S1: 1 steps
lem-F4-K2-S1 : Ws → ⟪ (ℓ "並亇並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亇並") ⟫ʷ
lem-F4-K2-S1 c4 = derive (ℓ "並亇並乕") (ℓ "乕並亇並")
  (rw⁻ 0 (q136 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = wlE 657 (lit c4)

-- F4-K2-S2: 1 steps
lem-F4-K2-S2 : Ws → ⟪ (ℓ "並亇並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並亇並") ⟫ʷ
lem-F4-K2-S2 c4 = derive (ℓ "並亇並乩") (ℓ "乩並亇並")
  (rw⁻ 0 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = wlE 658 (lit c4)

-- F4-K2-S3: 1 steps
lem-F4-K2-S3 : Ws → ⟪ (ℓ "並亇並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並亇並") ⟫ʷ
lem-F4-K2-S3 c4 = derive (ℓ "並亇並乹") (ℓ "乹並亇並")
  (rw⁻ 0 (q138 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = wpE 533 c4

-- F4-K2-K0: 1 steps
lem-F4-K2-K0 : Ws → ⟪ (ℓ "並亇並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並亇並") ⟫ʷ
lem-F4-K2-K0 c4 = derive (ℓ "並亇並亁") (ℓ "亁並亇並")
  (rw⁻ 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wlE 659 (lit c4)

-- F4-K2-K1: 1 steps
lem-F4-K2-K1 : Ws → ⟪ (ℓ "並亇並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並亇並") ⟫ʷ
lem-F4-K2-K1 c4 = derive (ℓ "並亇並亄") (ℓ "亄並亇並")
  (rw⁻ 0 (q140 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = wlE 660 (lit c4)

-- F4-K2-K2: 1 steps
lem-F4-K2-K2 : Ws → ⟪ (ℓ "並亇並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並亇並") ⟫ʷ
lem-F4-K2-K2 c4 = derive (ℓ "並亇並亇") (ℓ "亇並亇並")
  (rw⁻ 0 (q141 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = wlE 661 (lit c4)

-- F4-K2-K3: 1 steps
lem-F4-K2-K3 : Ws → ⟪ (ℓ "並亇並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並亇並") ⟫ʷ
lem-F4-K2-K3 c4 = derive (ℓ "並亇並亊") (ℓ "亊並亇並")
  (rw⁻ 0 (q142 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = wpE 551 c4
  q144 : Ws → Eqn
  q144 c4 = wpE 552 c4
  q145 : Ws → Eqn
  q145 c4 = wpE 553 c4
  q146 : Ws → Eqn
  q146 c4 = wpE 554 c4
  q147 : Ws → Eqn
  q147 c4 = eqn (ℓ "乊仺") (ℓ "仺乊") (c₃ (Swap ↑) (CZ))
  q148 : Ws → Eqn
  q148 c4 = wlE 6 (lit c4)

-- nat-SWbc @14213243: 23 steps
lem-nat-SWbc-at14213243 : Ws → ⟪ (ℓ "乊仼乊") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-nat-SWbc-at14213243 c4 = derive (ℓ "乊仼乊") (ℓ "伅")
  (re 1 1 (ℓ "五井任井五任") ∷
   rw⁻ 0 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   re 3 1 (ℓ "亜亟仺亟亜仺") ∷
   rw⁻ 2 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 4 (q147 c4) ∷
   rw 5 (q146 c4) ∷
   rw⁻ 6 (q145 c4) ∷
   rw 7 (q147 c4) ∷
   rw 8 (q144 c4) ∷
   rw⁻ 9 (q143 c4) ∷
   re 11 1 (ℓ "亜亟仺亟亜仺") ∷
   rw⁻ 10 (q145 c4) ∷
   rw 11 (q146 c4) ∷
   rw 12 (q147 c4) ∷
   rw 13 (q146 c4) ∷
   rw⁻ 14 (q145 c4) ∷
   rw 15 (q147 c4) ∷
   rw 16 (q148 c4) ∷
   re 2 6 (ℓ "伄") ∷
   re 5 6 (ℓ "伄") ∷
   re 0 6 (ℓ "伅") ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = wlE 687 (lit c4)

-- F4-K3-I: 1 steps
lem-F4-K3-I : Ws → ⟪ (ℓ "並亊並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亊並") ⟫ʷ
lem-F4-K3-I c4 = derive (ℓ "並亊並丢") (ℓ "丢並亊並")
  (rw⁻ 0 (q149 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = wpE 557 c4

-- F4-K3-S0: 1 steps
lem-F4-K3-S0 : Ws → ⟪ (ℓ "並亊並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並亊並") ⟫ʷ
lem-F4-K3-S0 c4 = derive (ℓ "並亊並丽") (ℓ "丽並亊並")
  (rw⁻ 0 (q150 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wlE 688 (lit c4)

-- F4-K3-S1: 1 steps
lem-F4-K3-S1 : Ws → ⟪ (ℓ "並亊並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亊並") ⟫ʷ
lem-F4-K3-S1 c4 = derive (ℓ "並亊並乕") (ℓ "乕並亊並")
  (rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = wlE 689 (lit c4)

-- F4-K3-S2: 1 steps
lem-F4-K3-S2 : Ws → ⟪ (ℓ "並亊並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並亊並") ⟫ʷ
lem-F4-K3-S2 c4 = derive (ℓ "並亊並乩") (ℓ "乩並亊並")
  (rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = wlE 690 (lit c4)

-- F4-K3-S3: 1 steps
lem-F4-K3-S3 : Ws → ⟪ (ℓ "並亊並乹") ⟫ʷ ≈ ⟪ (ℓ "乹並亊並") ⟫ʷ
lem-F4-K3-S3 c4 = derive (ℓ "並亊並乹") (ℓ "乹並亊並")
  (rw⁻ 0 (q153 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = wpE 558 c4

-- F4-K3-K0: 1 steps
lem-F4-K3-K0 : Ws → ⟪ (ℓ "並亊並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並亊並") ⟫ʷ
lem-F4-K3-K0 c4 = derive (ℓ "並亊並亁") (ℓ "亁並亊並")
  (rw⁻ 0 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = wlE 691 (lit c4)

-- F4-K3-K1: 1 steps
lem-F4-K3-K1 : Ws → ⟪ (ℓ "並亊並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並亊並") ⟫ʷ
lem-F4-K3-K1 c4 = derive (ℓ "並亊並亄") (ℓ "亄並亊並")
  (rw⁻ 0 (q155 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = wlE 692 (lit c4)

-- F4-K3-K2: 1 steps
lem-F4-K3-K2 : Ws → ⟪ (ℓ "並亊並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並亊並") ⟫ʷ
lem-F4-K3-K2 c4 = derive (ℓ "並亊並亇") (ℓ "亇並亊並")
  (rw⁻ 0 (q156 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = wlE 693 (lit c4)

-- F4-K3-K3: 1 steps
lem-F4-K3-K3 : Ws → ⟪ (ℓ "並亊並亊") ⟫ʷ ≈ ⟪ (ℓ "亊並亊並") ⟫ʷ
lem-F4-K3-K3 c4 = derive (ℓ "並亊並亊") (ℓ "亊並亊並")
  (rw⁻ 0 (q157 c4) ∷ []) Eq.refl

-- cQ @0210213443: 7 steps
lem-cQ-at0210213443 : Ws → ⟪ (ℓ "二亰") ⟫ʷ ≈ ⟪ (ℓ "亰二") ⟫ʷ
lem-cQ-at0210213443 c4 = derive (ℓ "二亰") (ℓ "亰二")
  (rw 0 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q27 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = wlE 231 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wpE 214 c4

-- sym-ab @122441: 18 steps
lem-sym-ab-at122441 : Ws → ⟪ (ℓ "仞") ⟫ʷ ≈ ⟪ (ℓ "伈") ⟫ʷ
lem-sym-ab-at122441 c4 = derive (ℓ "仞") (ℓ "伈")
  (re 0 1 (ℓ "亜亝仝亝亜仝") ∷
   re 2 1 (ℓ "亘亚仇亚亘仇") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   re 4 1 (ℓ "价") ∷
   re 7 1 (ℓ "价") ∷
   re 2 6 (ℓ "伇") ∷
   re 5 1 (ℓ "亘亚仇亚亘仇") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q158 c4) ∷
   rw 5 (q159 c4) ∷
   re 7 1 (ℓ "价") ∷
   re 10 1 (ℓ "价") ∷
   re 5 6 (ℓ "伇") ∷
   re 0 6 (ℓ "伈") ∷ []) Eq.refl

-- cQ @14233241: 7 steps
lem-cQ-at14233241 : Ws → ⟪ (ℓ "亠二") ⟫ʷ ≈ ⟪ (ℓ "二亠") ⟫ʷ
lem-cQ-at14233241 c4 = derive (ℓ "亠二") (ℓ "二亠")
  (rw 0 (q18 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q18 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = wpE 675 c4
  q161 : Ws → Eqn
  q161 c4 = wpE 676 c4
  q162 : Ws → Eqn
  q162 c4 = wpE 677 c4
  q163 : Ws → Eqn
  q163 c4 = wpE 678 c4
  q164 : Ws → Eqn
  q164 c4 = eqn (ℓ "丫佷") (ℓ "佷丫") (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat-SWbc @0314213042: 23 steps
lem-nat-SWbc-at0314213042 : Ws → ⟪ (ℓ "丫侂丫") ⟫ʷ ≈ ⟪ (ℓ "佹") ⟫ʷ
lem-nat-SWbc-at0314213042 c4 = derive (ℓ "丫侂丫") (ℓ "佹")
  (re 1 1 (ℓ "京亮侁亮京侁") ∷
   rw⁻ 0 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   re 3 1 (ℓ "亠亣佷亣亠佷") ∷
   rw⁻ 2 (q162 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q164 c4) ∷
   rw 5 (q163 c4) ∷
   rw⁻ 6 (q162 c4) ∷
   rw 7 (q164 c4) ∷
   rw 8 (q161 c4) ∷
   rw⁻ 9 (q160 c4) ∷
   re 11 1 (ℓ "亠亣佷亣亠佷") ∷
   rw⁻ 10 (q162 c4) ∷
   rw 11 (q163 c4) ∷
   rw 12 (q164 c4) ∷
   rw 13 (q163 c4) ∷
   rw⁻ 14 (q162 c4) ∷
   rw 15 (q164 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (ℓ "佸") ∷
   re 5 6 (ℓ "佸") ∷
   re 0 6 (ℓ "佹") ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = wpE 516 c4
  q166 : Ws → Eqn
  q166 c4 = wlE 756 (lit c4)

-- sym-ab @0210233441: 18 steps
lem-sym-ab-at0210233441 : Ws → ⟪ (ℓ "估") ⟫ʷ ≈ ⟪ (ℓ "佁") ⟫ʷ
lem-sym-ab-at0210233441 c4 = derive (ℓ "估") (ℓ "佁")
  (re 0 1 (ℓ "亘亚仙亚亘仙") ∷
   re 2 1 (ℓ "亜亝仒亝亜仒") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   re 4 1 (ℓ "伿") ∷
   re 7 1 (ℓ "伿") ∷
   re 2 6 (ℓ "佀") ∷
   re 5 1 (ℓ "亜亝仒亝亜仒") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q165 c4) ∷
   rw 5 (q166 c4) ∷
   re 7 1 (ℓ "伿") ∷
   re 10 1 (ℓ "伿") ∷
   re 5 6 (ℓ "佀") ∷
   re 0 6 (ℓ "佁") ∷ []) Eq.refl

-- sym-ab @0213203441: 18 steps
lem-sym-ab-at0213203441 : Ws → ⟪ (ℓ "佁") ⟫ʷ ≈ ⟪ (ℓ "估") ⟫ʷ
lem-sym-ab-at0213203441 c4 = derive (ℓ "佁") (ℓ "估")
  (re 0 1 (ℓ "亘亚佀亚亘佀") ∷
   re 2 1 (ℓ "亰亲伿亲亰伿") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q166 c4) ∷
   rw⁻ 2 (q165 c4) ∷
   re 4 1 (ℓ "仒") ∷
   re 7 1 (ℓ "仒") ∷
   re 2 6 (ℓ "仙") ∷
   re 5 1 (ℓ "亰亲伿亲亰伿") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q166 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   re 7 1 (ℓ "仒") ∷
   re 10 1 (ℓ "仒") ∷
   re 5 6 (ℓ "仙") ∷
   re 0 6 (ℓ "估") ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = wpE 695 c4
  q168 : Ws → Eqn
  q168 c4 = wpE 696 c4

-- nat-SWbc @0314203142: 23 steps
lem-nat-SWbc-at0314203142 : Ws → ⟪ (ℓ "丫佹丫") ⟫ʷ ≈ ⟪ (ℓ "侂") ⟫ʷ
lem-nat-SWbc-at0314203142 c4 = derive (ℓ "丫佹丫") (ℓ "侂")
  (re 1 1 (ℓ "亠亢佸亢亠佸") ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q167 c4) ∷
   re 3 1 (ℓ "京亯佷亯京佷") ∷
   rw⁻ 2 (q160 c4) ∷
   rw 3 (q168 c4) ∷
   rw 4 (q164 c4) ∷
   rw 5 (q168 c4) ∷
   rw⁻ 6 (q160 c4) ∷
   rw 7 (q164 c4) ∷
   rw 8 (q167 c4) ∷
   rw⁻ 9 (q162 c4) ∷
   re 11 1 (ℓ "京亯佷亯京佷") ∷
   rw⁻ 10 (q160 c4) ∷
   rw 11 (q168 c4) ∷
   rw 12 (q164 c4) ∷
   rw 13 (q168 c4) ∷
   rw⁻ 14 (q160 c4) ∷
   rw 15 (q164 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (ℓ "侁") ∷
   re 5 6 (ℓ "侁") ∷
   re 0 6 (ℓ "侂") ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = wpE 714 c4
  q170 : Ws → Eqn
  q170 c4 = wpE 715 c4

-- nat-SWbc @0214213043: 23 steps
lem-nat-SWbc-at0214213043 : Ws → ⟪ (ℓ "丫佝丫") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-nat-SWbc-at0214213043 c4 = derive (ℓ "丫佝丫") (ℓ "佔")
  (re 1 1 (ℓ "亨亪作亪亨作") ∷
   rw⁻ 0 (q125 c4) ∷
   rw 1 (q169 c4) ∷
   re 3 1 (ℓ "亜亟佒亟亜佒") ∷
   rw⁻ 2 (q123 c4) ∷
   rw 3 (q170 c4) ∷
   rw 4 (q127 c4) ∷
   rw 5 (q170 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw 7 (q127 c4) ∷
   rw 8 (q169 c4) ∷
   rw⁻ 9 (q125 c4) ∷
   re 11 1 (ℓ "亜亟佒亟亜佒") ∷
   rw⁻ 10 (q123 c4) ∷
   rw 11 (q170 c4) ∷
   rw 12 (q127 c4) ∷
   rw 13 (q170 c4) ∷
   rw⁻ 14 (q123 c4) ∷
   rw 15 (q127 c4) ∷
   rw 16 (q128 c4) ∷
   re 2 6 (ℓ "体") ∷
   re 5 6 (ℓ "体") ∷
   re 0 6 (ℓ "佔") ∷ []) Eq.refl

-- sym-ab @0214203143: 18 steps
lem-sym-ab-at0214203143 : Ws → ⟪ (ℓ "佔") ⟫ʷ ≈ ⟪ (ℓ "伱") ⟫ʷ
lem-sym-ab-at0214203143 c4 = derive (ℓ "佔") (ℓ "伱")
  (re 0 1 (ℓ "亜亞体亞亜体") ∷
   re 2 1 (ℓ "亨享佒享亨佒") ∷
   re 4 1 (ℓ "乻") ∷
   re 7 1 (ℓ "乻") ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 2 (q121 c4) ∷
   re 4 1 (ℓ "仈") ∷
   re 7 1 (ℓ "仈") ∷
   re 2 6 (ℓ "仉") ∷
   re 5 1 (ℓ "亨享佒享亨佒") ∷
   re 7 1 (ℓ "乻") ∷
   re 10 1 (ℓ "乻") ∷
   rw⁻ 5 (q122 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   re 7 1 (ℓ "仈") ∷
   re 10 1 (ℓ "仈") ∷
   re 5 6 (ℓ "仉") ∷
   re 0 6 (ℓ "伱") ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = wpE 594 c4
  q172 : Ws → Eqn
  q172 c4 = wpE 719 c4
  q173 : Ws → Eqn
  q173 c4 = wlE 814 (lit c4)
  q174 : Ws → Eqn
  q174 c4 = wlE 815 (lit c4)
  q175 : Ws → Eqn
  q175 c4 = wlE 816 (lit c4)
  q176 : Ws → Eqn
  q176 c4 = wlE 817 (lit c4)
  q177 : Ws → Eqn
  q177 c4 = wlE 3 (lit c4)

-- nat-S @14213243: 31 steps
lem-nat-S-at14213243 : Ws → ⟪ (ℓ "乥俄乥") ⟫ʷ ≈ ⟪ (ℓ "俖") ⟫ʷ
lem-nat-S-at14213243 c4 = derive (ℓ "乥俄乥") (ℓ "俖")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   re 1 1 (ℓ "亜亞仉亞亜仉") ∷
   rw⁻ 0 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   re 3 1 (ℓ "二亍仈亍二仈") ∷
   re 5 1 (ℓ "丸") ∷
   re 8 1 (ℓ "丸") ∷
   rw⁻ 2 (q173 c4) ∷
   re 4 1 (ℓ "仠") ∷
   re 7 1 (ℓ "仠") ∷
   re 2 6 (ℓ "仡") ∷
   rw 3 (q172 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   re 6 1 (ℓ "二亍仈亍二仈") ∷
   re 8 1 (ℓ "丸") ∷
   re 11 1 (ℓ "丸") ∷
   rw⁻ 5 (q173 c4) ∷
   re 7 1 (ℓ "仠") ∷
   re 10 1 (ℓ "仠") ∷
   re 5 6 (ℓ "仡") ∷
   rw 6 (q174 c4) ∷
   rw⁻ 7 (q175 c4) ∷
   rw 8 (q174 c4) ∷
   rw⁻ 9 (q176 c4) ∷
   rw 10 (q177 c4) ∷
   re 0 6 (ℓ "佨") ∷
   re 2 1 (ℓ "俑") ∷
   re 4 1 (ℓ "俕") ∷
   re 0 5 (ℓ "俖") ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = wlE 838 (lit c4)
  q179 : Ws → Eqn
  q179 c4 = wlE 839 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = wlE 840 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 841 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (ℓ "乊仢") (ℓ "仢乊") (c₃ (Swap ↑) (CZ))

-- nat-SWbc @1331: 23 steps
lem-nat-SWbc-at1331 : Ws → ⟪ (ℓ "乊仭乊") ⟫ʷ ≈ ⟪ (ℓ "令") ⟫ʷ
lem-nat-SWbc-at1331 c4 = derive (ℓ "乊仭乊") (ℓ "令")
  (re 1 1 (ℓ "亘亙们亙亘们") ∷
   rw⁻ 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   re 3 1 (ℓ "亐亓仢亓亐仢") ∷
   rw⁻ 2 (q180 c4) ∷
   rw 3 (q181 c4) ∷
   rw 4 (q182 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 6 (q180 c4) ∷
   rw 7 (q182 c4) ∷
   rw 8 (q179 c4) ∷
   rw⁻ 9 (q178 c4) ∷
   re 11 1 (ℓ "亐亓仢亓亐仢") ∷
   rw⁻ 10 (q180 c4) ∷
   rw 11 (q181 c4) ∷
   rw 12 (q182 c4) ∷
   rw 13 (q181 c4) ∷
   rw⁻ 14 (q180 c4) ∷
   rw 15 (q182 c4) ∷
   rw 16 (q148 c4) ∷
   re 2 6 (ℓ "代") ∷
   re 5 6 (ℓ "代") ∷
   re 0 6 (ℓ "令") ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = wpE 732 c4
  q184 : Ws → Eqn
  q184 c4 = wpE 733 c4

-- sym-ab @0312213440: 18 steps
lem-sym-ab-at0312213440 : Ws → ⟪ (ℓ "佳") ⟫ʷ ≈ ⟪ (ℓ "佭") ⟫ʷ
lem-sym-ab-at0312213440 c4 = derive (ℓ "佳") (ℓ "佭")
  (re 0 1 (ℓ "交产佉产交佉") ∷
   re 2 1 (ℓ "亰亱佂亱亰佂") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q183 c4) ∷
   rw 2 (q184 c4) ∷
   re 4 1 (ℓ "伝") ∷
   re 7 1 (ℓ "伝") ∷
   re 2 6 (ℓ "传") ∷
   re 5 1 (ℓ "亰亱佂亱亰佂") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw⁻ 5 (q183 c4) ∷
   rw 5 (q184 c4) ∷
   re 7 1 (ℓ "伝") ∷
   re 10 1 (ℓ "伝") ∷
   re 5 6 (ℓ "传") ∷
   re 0 6 (ℓ "佭") ∷ []) Eq.refl

-- sym-ab @033440: 18 steps
lem-sym-ab-at033440 : Ws → ⟪ (ℓ "佭") ⟫ʷ ≈ ⟪ (ℓ "佳") ⟫ʷ
lem-sym-ab-at033440 c4 = derive (ℓ "佭") (ℓ "佳")
  (re 0 1 (ℓ "交产传产交传") ∷
   re 2 1 (ℓ "京亭伝亭京伝") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q184 c4) ∷
   rw 2 (q183 c4) ∷
   re 4 1 (ℓ "佂") ∷
   re 7 1 (ℓ "佂") ∷
   re 2 6 (ℓ "佉") ∷
   re 5 1 (ℓ "京亭伝亭京伝") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q184 c4) ∷
   rw 5 (q183 c4) ∷
   re 7 1 (ℓ "佂") ∷
   re 10 1 (ℓ "佂") ∷
   re 5 6 (ℓ "佉") ∷
   re 0 6 (ℓ "佳") ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = wlE 876 (lit c4)
  q186 : Ws → Eqn
  q186 c4 = wlE 877 (lit c4)

-- nat-SWbc @132132: 23 steps
lem-nat-SWbc-at132132 : Ws → ⟪ (ℓ "乊令乊") ⟫ʷ ≈ ⟪ (ℓ "仭") ⟫ʷ
lem-nat-SWbc-at132132 c4 = derive (ℓ "乊令乊") (ℓ "仭")
  (re 1 1 (ℓ "亐云代云亐代") ∷
   rw⁻ 0 (q180 c4) ∷
   rw 1 (q185 c4) ∷
   re 3 1 (ℓ "亘些仢些亘仢") ∷
   rw⁻ 2 (q178 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q182 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 6 (q178 c4) ∷
   rw 7 (q182 c4) ∷
   rw 8 (q185 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   re 11 1 (ℓ "亘些仢些亘仢") ∷
   rw⁻ 10 (q178 c4) ∷
   rw 11 (q186 c4) ∷
   rw 12 (q182 c4) ∷
   rw 13 (q186 c4) ∷
   rw⁻ 14 (q178 c4) ∷
   rw 15 (q182 c4) ∷
   rw 16 (q148 c4) ∷
   re 2 6 (ℓ "们") ∷
   re 5 6 (ℓ "们") ∷
   re 0 6 (ℓ "仭") ∷ []) Eq.refl
