{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)

module Examples.Groups.Clifford+CS.Five.D.D002 where

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
  q1 c4 = wpE 154 c4
  q2 : Ws → Eqn
  q2 c4 = wpE 153 c4

-- sym-ab @1331: 18 steps
lem-sym-ab-at1331 : Ws → ⟪ (ℓ "仭") ⟫ʷ ≈ ⟪ (ℓ "仕") ⟫ʷ
lem-sym-ab-at1331 c4 = derive (ℓ "仭") (ℓ "仕")
  (re 0 1 (ℓ "亘亙们亙亘们") ∷
   re 2 1 (ℓ "亐亓仢亓亐仢") ∷
   re 4 1 (ℓ "乻") ∷
   re 7 1 (ℓ "乻") ∷
   rw 2 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (ℓ "今") ∷
   re 7 1 (ℓ "今") ∷
   re 2 6 (ℓ "仔") ∷
   re 5 1 (ℓ "亐亓仢亓亐仢") ∷
   re 7 1 (ℓ "乻") ∷
   re 10 1 (ℓ "乻") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "今") ∷
   re 10 1 (ℓ "今") ∷
   re 5 6 (ℓ "仔") ∷
   re 0 6 (ℓ "仕") ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = wlE 518 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wpE 280 c4

-- sym-ab @0220: 18 steps
lem-sym-ab-at0220 : Ws → ⟪ (ℓ "伳") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-sym-ab-at0220 c4 = derive (ℓ "伳") (ℓ "伭")
  (re 0 1 (ℓ "二亏伕亏二伕") ∷
   re 2 1 (ℓ "交亥休亥交休") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   re 4 1 (ℓ "仍") ∷
   re 7 1 (ℓ "仍") ∷
   re 2 6 (ℓ "他") ∷
   re 5 1 (ℓ "交亥休亥交休") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (ℓ "仍") ∷
   re 10 1 (ℓ "仍") ∷
   re 5 6 (ℓ "他") ∷
   re 0 6 (ℓ "伭") ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = wpE 162 c4
  q6 : Ws → Eqn
  q6 c4 = wlE 288 (lit c4)

-- sym-ab @14233241: 18 steps
lem-sym-ab-at14233241 : Ws → ⟪ (ℓ "伍") ⟫ʷ ≈ ⟪ (ℓ "件") ⟫ʷ
lem-sym-ab-at14233241 c4 = derive (ℓ "伍") (ℓ "件")
  (re 0 1 (ℓ "亠亡伌亡亠伌") ∷
   re 2 1 (ℓ "亜亟价亟亜价") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   re 4 1 (ℓ "仟") ∷
   re 7 1 (ℓ "仟") ∷
   re 2 6 (ℓ "仵") ∷
   re 5 1 (ℓ "亜亟价亟亜价") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   re 7 1 (ℓ "仟") ∷
   re 10 1 (ℓ "仟") ∷
   re 5 6 (ℓ "仵") ∷
   re 0 6 (ℓ "件") ∷ []) Eq.refl

-- sym-ab @021021: 18 steps
lem-sym-ab-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "伳") ⟫ʷ
lem-sym-ab-at021021 c4 = derive (ℓ "伭") (ℓ "伳")
  (re 0 1 (ℓ "二亏他亏二他") ∷
   re 2 1 (ℓ "亘亙仍亙亘仍") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q4 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (ℓ "休") ∷
   re 7 1 (ℓ "休") ∷
   re 2 6 (ℓ "伕") ∷
   re 5 1 (ℓ "亘亙仍亙亘仍") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (ℓ "休") ∷
   re 10 1 (ℓ "休") ∷
   re 5 6 (ℓ "伕") ∷
   re 0 6 (ℓ "伳") ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wlE 929 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 415 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (ℓ "乄亰") (ℓ "亰乄") (c₂ (CX₁₀) (CCZ))
  q10 : Ws → Eqn
  q10 c4 = wpE 765 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 279 c4

-- cQ @0220: 7 steps
lem-cQ-at0220 : Ws → ⟪ (ℓ "二亰") ⟫ʷ ≈ ⟪ (ℓ "亰二") ⟫ʷ
lem-cQ-at0220 c4 = derive (ℓ "二亰") (ℓ "亰二")
  (rw 0 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q7 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = wlE 293 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 294 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (ℓ "二乽") (ℓ "乽二") (c₃ (CCZ) (CX₀₁))
  q15 : Ws → Eqn
  q15 c4 = wpE 140 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 141 c4

-- cQ @0213243140: 7 steps
lem-cQ-at0213243140 : Ws → ⟪ (ℓ "亰二") ⟫ʷ ≈ ⟪ (ℓ "二亰") ⟫ʷ
lem-cQ-at0213243140 c4 = derive (ℓ "亰二") (ℓ "二亰")
  (rw 0 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q12 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = wpE 766 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 767 c4

-- sym-ab @0213213440: 18 steps
lem-sym-ab-at0213213440 : Ws → ⟪ (ℓ "佈") ⟫ʷ ≈ ⟪ (ℓ "伵") ⟫ʷ
lem-sym-ab-at0213213440 c4 = derive (ℓ "佈") (ℓ "伵")
  (re 0 1 (ℓ "交亦佇亦交佇") ∷
   re 2 1 (ℓ "亰亲伷亲亰伷") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   re 4 1 (ℓ "伓") ∷
   re 7 1 (ℓ "伓") ∷
   re 2 6 (ℓ "伖") ∷
   re 5 1 (ℓ "亰亲伷亲亰伷") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   re 7 1 (ℓ "伓") ∷
   re 10 1 (ℓ "伓") ∷
   re 5 6 (ℓ "伖") ∷
   re 0 6 (ℓ "伵") ∷ []) Eq.refl

-- sym-ab @02233440: 18 steps
lem-sym-ab-at02233440 : Ws → ⟪ (ℓ "伵") ⟫ʷ ≈ ⟪ (ℓ "佈") ⟫ʷ
lem-sym-ab-at02233440 c4 = derive (ℓ "伵") (ℓ "佈")
  (re 0 1 (ℓ "交亦伖亦交伖") ∷
   re 2 1 (ℓ "亨亩伓亩亨伓") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q18 c4) ∷
   rw 2 (q17 c4) ∷
   re 4 1 (ℓ "伷") ∷
   re 7 1 (ℓ "伷") ∷
   re 2 6 (ℓ "佇") ∷
   re 5 1 (ℓ "亨亩伓亩亨伓") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q18 c4) ∷
   rw 5 (q17 c4) ∷
   re 7 1 (ℓ "伷") ∷
   re 10 1 (ℓ "伷") ∷
   re 5 6 (ℓ "佇") ∷
   re 0 6 (ℓ "佈") ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = wpE 529 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 812 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 527 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 813 c4
  q23 : Ws → Eqn
  q23 c4 = eqn (ℓ "仇乼") (ℓ "乼仇") (c₃ (CZ ↑) (Swap))
  q24 : Ws → Eqn
  q24 c4 = wlE 4 (lit c4)

-- nat-SWbc @12233441: 23 steps
lem-nat-SWbc-at12233441 : Ws → ⟪ (ℓ "乼付乼") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-nat-SWbc-at12233441 c4 = derive (ℓ "乼付乼") (ℓ "仞")
  (re 1 1 (ℓ "亘亙仗亙亘仗") ∷
   rw⁻ 0 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   re 3 1 (ℓ "亜亞仇亞亜仇") ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   re 11 1 (ℓ "亜亞仇亞亜仇") ∷
   rw⁻ 10 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw⁻ 12 (q23 c4) ∷
   rw 13 (q22 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "仝") ∷
   re 5 6 (ℓ "仝") ∷
   re 0 6 (ℓ "仞") ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = wpE 216 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 205 (lit c4)

-- sym-ab @14213243: 18 steps
lem-sym-ab-at14213243 : Ws → ⟪ (ℓ "仼") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-sym-ab-at14213243 c4 = derive (ℓ "仼") (ℓ "仄")
  (re 0 1 (ℓ "五井任井五任") ∷
   re 2 1 (ℓ "亜亟仺亟亜仺") ∷
   re 4 1 (ℓ "乻") ∷
   re 7 1 (ℓ "乻") ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   re 4 1 (ℓ "人") ∷
   re 7 1 (ℓ "人") ∷
   re 2 6 (ℓ "仃") ∷
   re 5 1 (ℓ "亜亟仺亟亜仺") ∷
   re 7 1 (ℓ "乻") ∷
   re 10 1 (ℓ "乻") ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (ℓ "人") ∷
   re 10 1 (ℓ "人") ∷
   re 5 6 (ℓ "仃") ∷
   re 0 6 (ℓ "仄") ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wpE 131 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 130 c4

-- sym-ab @132132: 18 steps
lem-sym-ab-at132132 : Ws → ⟪ (ℓ "令") ⟫ʷ ≈ ⟪ (ℓ "亾") ⟫ʷ
lem-sym-ab-at132132 c4 = derive (ℓ "令") (ℓ "亾")
  (re 0 1 (ℓ "亐云代云亐代") ∷
   re 2 1 (ℓ "亘些仢些亘仢") ∷
   re 4 1 (ℓ "乻") ∷
   re 7 1 (ℓ "乻") ∷
   rw 2 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   re 4 1 (ℓ "亷") ∷
   re 7 1 (ℓ "亷") ∷
   re 2 6 (ℓ "亽") ∷
   re 5 1 (ℓ "亘些仢些亘仢") ∷
   re 7 1 (ℓ "乻") ∷
   re 10 1 (ℓ "乻") ∷
   rw 5 (q27 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   re 7 1 (ℓ "亷") ∷
   re 10 1 (ℓ "亷") ∷
   re 5 6 (ℓ "亽") ∷
   re 0 6 (ℓ "亾") ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wpE 847 c4

-- F2-I-S0: 1 steps
lem-F2-I-S0 : Ws → ⟪ (ℓ "丢丽") ⟫ʷ ≈ ⟪ (ℓ "丽丢") ⟫ʷ
lem-F2-I-S0 c4 = derive (ℓ "丢丽") (ℓ "丽丢")
  (rw⁻ 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = wlE 1044 (lit c4)

-- F2-I-S1: 1 steps
lem-F2-I-S1 : Ws → ⟪ (ℓ "丢乕") ⟫ʷ ≈ ⟪ (ℓ "乕丢") ⟫ʷ
lem-F2-I-S1 c4 = derive (ℓ "丢乕") (ℓ "乕丢")
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = wlE 1045 (lit c4)

-- F2-I-S2: 1 steps
lem-F2-I-S2 : Ws → ⟪ (ℓ "丢乩") ⟫ʷ ≈ ⟪ (ℓ "乩丢") ⟫ʷ
lem-F2-I-S2 c4 = derive (ℓ "丢乩") (ℓ "乩丢")
  (rw⁻ 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = wlE 1046 (lit c4)

-- F2-I-S3: 1 steps
lem-F2-I-S3 : Ws → ⟪ (ℓ "丢乹") ⟫ʷ ≈ ⟪ (ℓ "乹丢") ⟫ʷ
lem-F2-I-S3 c4 = derive (ℓ "丢乹") (ℓ "乹丢")
  (rw⁻ 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = wpE 848 c4

-- F2-I-K0: 1 steps
lem-F2-I-K0 : Ws → ⟪ (ℓ "丢亁") ⟫ʷ ≈ ⟪ (ℓ "亁丢") ⟫ʷ
lem-F2-I-K0 c4 = derive (ℓ "丢亁") (ℓ "亁丢")
  (rw⁻ 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = wlE 1047 (lit c4)

-- F2-I-K1: 1 steps
lem-F2-I-K1 : Ws → ⟪ (ℓ "丢亄") ⟫ʷ ≈ ⟪ (ℓ "亄丢") ⟫ʷ
lem-F2-I-K1 c4 = derive (ℓ "丢亄") (ℓ "亄丢")
  (rw⁻ 0 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = wlE 1048 (lit c4)

-- F2-I-K2: 1 steps
lem-F2-I-K2 : Ws → ⟪ (ℓ "丢亇") ⟫ʷ ≈ ⟪ (ℓ "亇丢") ⟫ʷ
lem-F2-I-K2 c4 = derive (ℓ "丢亇") (ℓ "亇丢")
  (rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wlE 1049 (lit c4)

-- F2-I-K3: 1 steps
lem-F2-I-K3 : Ws → ⟪ (ℓ "丢亊") ⟫ʷ ≈ ⟪ (ℓ "亊丢") ⟫ʷ
lem-F2-I-K3 c4 = derive (ℓ "丢亊") (ℓ "亊丢")
  (rw⁻ 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = wpE 850 c4

-- F2-S0-S1: 1 steps
lem-F2-S0-S1 : Ws → ⟪ (ℓ "丽乕") ⟫ʷ ≈ ⟪ (ℓ "乕丽") ⟫ʷ
lem-F2-S0-S1 c4 = derive (ℓ "丽乕") (ℓ "乕丽")
  (rw 0 (q37 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = wpE 851 c4

-- F2-S0-S2: 1 steps
lem-F2-S0-S2 : Ws → ⟪ (ℓ "丽乩") ⟫ʷ ≈ ⟪ (ℓ "乩丽") ⟫ʷ
lem-F2-S0-S2 c4 = derive (ℓ "丽乩") (ℓ "乩丽")
  (rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wpE 852 c4

-- F2-S0-S3: 1 steps
lem-F2-S0-S3 : Ws → ⟪ (ℓ "丽乹") ⟫ʷ ≈ ⟪ (ℓ "乹丽") ⟫ʷ
lem-F2-S0-S3 c4 = derive (ℓ "丽乹") (ℓ "乹丽")
  (rw 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = wpE 853 c4

-- F2-S0-K1: 1 steps
lem-F2-S0-K1 : Ws → ⟪ (ℓ "丽亄") ⟫ʷ ≈ ⟪ (ℓ "亄丽") ⟫ʷ
lem-F2-S0-K1 c4 = derive (ℓ "丽亄") (ℓ "亄丽")
  (rw⁻ 0 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = wpE 854 c4

-- F2-S0-K2: 1 steps
lem-F2-S0-K2 : Ws → ⟪ (ℓ "丽亇") ⟫ʷ ≈ ⟪ (ℓ "亇丽") ⟫ʷ
lem-F2-S0-K2 c4 = derive (ℓ "丽亇") (ℓ "亇丽")
  (rw⁻ 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = wpE 855 c4

-- F2-S0-K3: 1 steps
lem-F2-S0-K3 : Ws → ⟪ (ℓ "丽亊") ⟫ʷ ≈ ⟪ (ℓ "亊丽") ⟫ʷ
lem-F2-S0-K3 c4 = derive (ℓ "丽亊") (ℓ "亊丽")
  (rw⁻ 0 (q42 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = wlE 1052 (lit c4)

-- F2-S1-S2: 1 steps
lem-F2-S1-S2 : Ws → ⟪ (ℓ "乕乩") ⟫ʷ ≈ ⟪ (ℓ "乩乕") ⟫ʷ
lem-F2-S1-S2 c4 = derive (ℓ "乕乩") (ℓ "乩乕")
  (rw 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = wlE 1053 (lit c4)

-- F2-S1-S3: 1 steps
lem-F2-S1-S3 : Ws → ⟪ (ℓ "乕乹") ⟫ʷ ≈ ⟪ (ℓ "乹乕") ⟫ʷ
lem-F2-S1-S3 c4 = derive (ℓ "乕乹") (ℓ "乹乕")
  (rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wpE 861 c4

-- F2-S1-K0: 1 steps
lem-F2-S1-K0 : Ws → ⟪ (ℓ "乕亁") ⟫ʷ ≈ ⟪ (ℓ "亁乕") ⟫ʷ
lem-F2-S1-K0 c4 = derive (ℓ "乕亁") (ℓ "亁乕")
  (rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = wlE 1054 (lit c4)

-- F2-S1-K2: 1 steps
lem-F2-S1-K2 : Ws → ⟪ (ℓ "乕亇") ⟫ʷ ≈ ⟪ (ℓ "亇乕") ⟫ʷ
lem-F2-S1-K2 c4 = derive (ℓ "乕亇") (ℓ "亇乕")
  (rw⁻ 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = wlE 1055 (lit c4)

-- F2-S1-K3: 1 steps
lem-F2-S1-K3 : Ws → ⟪ (ℓ "乕亊") ⟫ʷ ≈ ⟪ (ℓ "亊乕") ⟫ʷ
lem-F2-S1-K3 c4 = derive (ℓ "乕亊") (ℓ "亊乕")
  (rw⁻ 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = wlE 1057 (lit c4)

-- F2-S2-S3: 1 steps
lem-F2-S2-S3 : Ws → ⟪ (ℓ "乩乹") ⟫ʷ ≈ ⟪ (ℓ "乹乩") ⟫ʷ
lem-F2-S2-S3 c4 = derive (ℓ "乩乹") (ℓ "乹乩")
  (rw 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wpE 862 c4

-- F2-S2-K0: 1 steps
lem-F2-S2-K0 : Ws → ⟪ (ℓ "乩亁") ⟫ʷ ≈ ⟪ (ℓ "亁乩") ⟫ʷ
lem-F2-S2-K0 c4 = derive (ℓ "乩亁") (ℓ "亁乩")
  (rw⁻ 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = wlE 1058 (lit c4)

-- F2-S2-K1: 1 steps
lem-F2-S2-K1 : Ws → ⟪ (ℓ "乩亄") ⟫ʷ ≈ ⟪ (ℓ "亄乩") ⟫ʷ
lem-F2-S2-K1 c4 = derive (ℓ "乩亄") (ℓ "亄乩")
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = wlE 1059 (lit c4)

-- F2-S2-K3: 1 steps
lem-F2-S2-K3 : Ws → ⟪ (ℓ "乩亊") ⟫ʷ ≈ ⟪ (ℓ "亊乩") ⟫ʷ
lem-F2-S2-K3 c4 = derive (ℓ "乩亊") (ℓ "亊乩")
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = wpE 865 c4

-- F2-S3-K0: 1 steps
lem-F2-S3-K0 : Ws → ⟪ (ℓ "乹亁") ⟫ʷ ≈ ⟪ (ℓ "亁乹") ⟫ʷ
lem-F2-S3-K0 c4 = derive (ℓ "乹亁") (ℓ "亁乹")
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wlE 1060 (lit c4)

-- F2-S3-K1: 1 steps
lem-F2-S3-K1 : Ws → ⟪ (ℓ "乹亄") ⟫ʷ ≈ ⟪ (ℓ "亄乹") ⟫ʷ
lem-F2-S3-K1 c4 = derive (ℓ "乹亄") (ℓ "亄乹")
  (rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = wlE 1061 (lit c4)

-- F2-S3-K2: 1 steps
lem-F2-S3-K2 : Ws → ⟪ (ℓ "乹亇") ⟫ʷ ≈ ⟪ (ℓ "亇乹") ⟫ʷ
lem-F2-S3-K2 c4 = derive (ℓ "乹亇") (ℓ "亇乹")
  (rw⁻ 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wpE 867 c4

-- F2-K0-K1: 1 steps
lem-F2-K0-K1 : Ws → ⟪ (ℓ "亁亄") ⟫ʷ ≈ ⟪ (ℓ "亄亁") ⟫ʷ
lem-F2-K0-K1 c4 = derive (ℓ "亁亄") (ℓ "亄亁")
  (rw 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = wpE 868 c4

-- F2-K0-K2: 1 steps
lem-F2-K0-K2 : Ws → ⟪ (ℓ "亁亇") ⟫ʷ ≈ ⟪ (ℓ "亇亁") ⟫ʷ
lem-F2-K0-K2 c4 = derive (ℓ "亁亇") (ℓ "亇亁")
  (rw 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = wpE 869 c4

-- F2-K0-K3: 1 steps
lem-F2-K0-K3 : Ws → ⟪ (ℓ "亁亊") ⟫ʷ ≈ ⟪ (ℓ "亊亁") ⟫ʷ
lem-F2-K0-K3 c4 = derive (ℓ "亁亊") (ℓ "亊亁")
  (rw 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = wlE 1063 (lit c4)

-- F2-K1-K2: 1 steps
lem-F2-K1-K2 : Ws → ⟪ (ℓ "亄亇") ⟫ʷ ≈ ⟪ (ℓ "亇亄") ⟫ʷ
lem-F2-K1-K2 c4 = derive (ℓ "亄亇") (ℓ "亇亄")
  (rw 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = wlE 1064 (lit c4)

-- F2-K1-K3: 1 steps
lem-F2-K1-K3 : Ws → ⟪ (ℓ "亄亊") ⟫ʷ ≈ ⟪ (ℓ "亊亄") ⟫ʷ
lem-F2-K1-K3 c4 = derive (ℓ "亄亊") (ℓ "亊亄")
  (rw 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = wlE 1067 (lit c4)

-- F2-K2-K3: 1 steps
lem-F2-K2-K3 : Ws → ⟪ (ℓ "亇亊") ⟫ʷ ≈ ⟪ (ℓ "亊亇") ⟫ʷ
lem-F2-K2-K3 c4 = derive (ℓ "亇亊") (ℓ "亊亇")
  (rw 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 1077 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 788 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wlE 1078 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 1079 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 135 c4
  q66 : Ws → Eqn
  q66 c4 = wpE 19 c4

-- inv-SBOX(2;0;41;3): 30 steps
lem-inv-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (ℓ "俄俸") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-inv-SBOX⟨2·0·41·3⟩ c4 = derive (ℓ "俄俸") []
  (re 0 1 (ℓ "伱亮係亮促") ∷
   re 5 1 (ℓ "係亮促亮侣") ∷
   re 4 1 (ℓ "丷") ∷
   re 5 1 (ℓ "丶") ∷
   rw 4 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   re 2 1 (ℓ "丶") ∷
   re 3 1 (ℓ "丷") ∷
   rw 2 (q63 c4) ∷
   rw 1 (q62 c4) ∷
   re 0 1 (ℓ "亜亞仉亞亜仉") ∷
   re 6 1 (ℓ "侢亜亞侢亞亜") ∷
   re 5 1 (ℓ "二亍仈亍二仈") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   re 11 1 (ℓ "価二亍価亍二") ∷
   re 11 1 (ℓ "丸") ∷
   re 14 1 (ℓ "丸") ∷
   rw 5 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   re 2 1 (ℓ "二亍仈亍二仈") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   re 8 1 (ℓ "価二亍価亍二") ∷
   re 8 1 (ℓ "丸") ∷
   re 11 1 (ℓ "丸") ∷
   rw 2 (q64 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q65 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = wlE 1080 (lit c4)

-- invr-SBOX(2;0;41;3): 30 steps
lem-invr-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (ℓ "俸俄") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-invr-SBOX⟨2·0·41·3⟩ c4 = derive (ℓ "俸俄") []
  (re 0 1 (ℓ "係亮促亮侣") ∷
   re 5 1 (ℓ "伱亮係亮促") ∷
   re 4 1 (ℓ "侢亜亞侢亞亜") ∷
   re 10 1 (ℓ "亜亞仉亞亜仉") ∷
   rw 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   re 7 1 (ℓ "価二亍価亍二") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   re 13 1 (ℓ "二亍仈亍二仈") ∷
   re 15 1 (ℓ "丸") ∷
   re 18 1 (ℓ "丸") ∷
   rw 7 (q67 c4) ∷
   rw 6 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 4 1 (ℓ "価二亍価亍二") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "二亍仈亍二仈") ∷
   re 12 1 (ℓ "丸") ∷
   re 15 1 (ℓ "丸") ∷
   rw 4 (q67 c4) ∷
   rw 3 (q62 c4) ∷
   re 2 1 (ℓ "丷") ∷
   re 3 1 (ℓ "丶") ∷
   rw 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   re 0 1 (ℓ "丶") ∷
   re 1 1 (ℓ "丷") ∷
   rw 0 (q63 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wlE 1102 (lit c4)

-- F1-order-I@0: 1 steps
lem-F1-order-Iat0 : Ws → ⟪ (ℓ "丢丢丢丢") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Iat0 c4 = derive (ℓ "丢丢丢丢") []
  (rw 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = wpE 902 c4

-- F1-order-S@0: 1 steps
lem-F1-order-Sat0 : Ws → ⟪ (ℓ "丽丽丽丽") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat0 c4 = derive (ℓ "丽丽丽丽") []
  (rw 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = wlE 1103 (lit c4)

-- F1-order-S@1: 1 steps
lem-F1-order-Sat1 : Ws → ⟪ (ℓ "乕乕乕乕") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat1 c4 = derive (ℓ "乕乕乕乕") []
  (rw 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = wlE 1104 (lit c4)

-- F1-order-S@2: 1 steps
lem-F1-order-Sat2 : Ws → ⟪ (ℓ "乩乩乩乩") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat2 c4 = derive (ℓ "乩乩乩乩") []
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = wlE 1105 (lit c4)

-- F1-order-S@3: 1 steps
lem-F1-order-Sat3 : Ws → ⟪ (ℓ "乹乹乹乹") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat3 c4 = derive (ℓ "乹乹乹乹") []
  (rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = wpE 903 c4

-- F1-order-K@0: 1 steps
lem-F1-order-Kat0 : Ws → ⟪ (ℓ "亁亁") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-Kat0 c4 = derive (ℓ "亁亁") (ℓ "丢丢丢")
  (rw 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = wlE 1106 (lit c4)

-- F1-order-K@1: 1 steps
lem-F1-order-Kat1 : Ws → ⟪ (ℓ "亄亄") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-Kat1 c4 = derive (ℓ "亄亄") (ℓ "丢丢丢")
  (rw 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = wlE 1107 (lit c4)

-- F1-order-K@2: 1 steps
lem-F1-order-Kat2 : Ws → ⟪ (ℓ "亇亇") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-Kat2 c4 = derive (ℓ "亇亇") (ℓ "丢丢丢")
  (rw 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = wlE 1108 (lit c4)

-- F1-order-K@3: 1 steps
lem-F1-order-Kat3 : Ws → ⟪ (ℓ "亊亊") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-Kat3 c4 = derive (ℓ "亊亊") (ℓ "丢丢丢")
  (rw 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = wpE 904 c4

-- F1-order-SK@0: 1 steps
lem-F1-order-SKat0 : Ws → ⟪ (ℓ "丽亁丽亁丽亁") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-SKat0 c4 = derive (ℓ "丽亁丽亁丽亁") (ℓ "丢丢丢")
  (rw 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = wlE 1109 (lit c4)

-- F1-order-SK@1: 1 steps
lem-F1-order-SKat1 : Ws → ⟪ (ℓ "乕亄乕亄乕亄") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-SKat1 c4 = derive (ℓ "乕亄乕亄乕亄") (ℓ "丢丢丢")
  (rw 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = wlE 1110 (lit c4)

-- F1-order-SK@2: 1 steps
lem-F1-order-SKat2 : Ws → ⟪ (ℓ "乩亇乩亇乩亇") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-SKat2 c4 = derive (ℓ "乩亇乩亇乩亇") (ℓ "丢丢丢")
  (rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = wlE 1111 (lit c4)

-- F1-order-SK@3: 1 steps
lem-F1-order-SKat3 : Ws → ⟪ (ℓ "乹亊乹亊乹亊") ⟫ʷ ≈ ⟪ (ℓ "丢丢丢") ⟫ʷ
lem-F1-order-SKat3 c4 = derive (ℓ "乹亊乹亊乹亊") (ℓ "丢丢丢")
  (rw 0 (q80 c4) ∷ []) Eq.refl

-- nf-order-CS@0: 0 steps
lem-nf-order-CSat0 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat0 c4 = refl

-- nf-order-CS@1: 0 steps
lem-nf-order-CSat1 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat1 c4 = refl

-- nf-order-CS@2: 0 steps
lem-nf-order-CSat2 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat2 c4 = refl

private
  q81 : Ws → Eqn
  q81 c4 = wlE 1122 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wlE 1123 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 1124 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wlE 1125 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (ℓ "伓乼") (ℓ "乼伓") (c₂ (CZ) (Swap ↑))

-- nat-SWbc @02233440: 23 steps
lem-nat-SWbc-at02233440 : Ws → ⟪ (ℓ "乼伵乼") ⟫ʷ ≈ ⟪ (ℓ "伶") ⟫ʷ
lem-nat-SWbc-at02233440 c4 = derive (ℓ "乼伵乼") (ℓ "伶")
  (re 1 1 (ℓ "交亦伖亦交伖") ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   re 3 1 (ℓ "亨亩伓亩亨伓") ∷
   rw⁻ 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw 8 (q82 c4) ∷
   rw⁻ 9 (q81 c4) ∷
   re 11 1 (ℓ "亨亩伓亩亨伓") ∷
   rw⁻ 10 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw 13 (q84 c4) ∷
   rw⁻ 14 (q83 c4) ∷
   rw⁻ 15 (q85 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "伔") ∷
   re 5 6 (ℓ "伔") ∷
   re 0 6 (ℓ "伶") ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = wlE 1137 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 1138 (lit c4)

-- nat-SWbc @022440: 23 steps
lem-nat-SWbc-at022440 : Ws → ⟪ (ℓ "乼伶乼") ⟫ʷ ≈ ⟪ (ℓ "伵") ⟫ʷ
lem-nat-SWbc-at022440 c4 = derive (ℓ "乼伶乼") (ℓ "伵")
  (re 1 1 (ℓ "亨亪伔亪亨伔") ∷
   rw⁻ 0 (q83 c4) ∷
   rw 1 (q86 c4) ∷
   re 3 1 (ℓ "交亥伓亥交伓") ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q87 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   re 11 1 (ℓ "交亥伓亥交伓") ∷
   rw⁻ 10 (q81 c4) ∷
   rw 11 (q87 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw 13 (q87 c4) ∷
   rw⁻ 14 (q81 c4) ∷
   rw⁻ 15 (q85 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "伖") ∷
   re 5 6 (ℓ "伖") ∷
   re 0 6 (ℓ "伵") ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = wpE 214 c4
  q89 : Ws → Eqn
  q89 c4 = wlE 231 (lit c4)

-- sym-ab @1441: 18 steps
lem-sym-ab-at1441 : Ws → ⟪ (ℓ "伈") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-sym-ab-at1441 c4 = derive (ℓ "伈") (ℓ "仞")
  (re 0 1 (ℓ "亜亝伇亝亜伇") ∷
   re 2 1 (ℓ "亠亣价亣亠价") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   re 4 1 (ℓ "仇") ∷
   re 7 1 (ℓ "仇") ∷
   re 2 6 (ℓ "仝") ∷
   re 5 1 (ℓ "亠亣价亣亠价") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q88 c4) ∷
   rw 5 (q89 c4) ∷
   re 7 1 (ℓ "仇") ∷
   re 10 1 (ℓ "仇") ∷
   re 5 6 (ℓ "仝") ∷
   re 0 6 (ℓ "仞") ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = wpE 530 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 528 c4
  q92 : Ws → Eqn
  q92 c4 = eqn (ℓ "仒乼") (ℓ "乼仒") (c₂ (CZ) (Swap ↑))

-- nat-SWbc @0210233441: 23 steps
lem-nat-SWbc-at0210233441 : Ws → ⟪ (ℓ "乼估乼") ⟫ʷ ≈ ⟪ (ℓ "伲") ⟫ʷ
lem-nat-SWbc-at0210233441 c4 = derive (ℓ "乼估乼") (ℓ "伲")
  (re 1 1 (ℓ "亘亚仙亚亘仙") ∷
   rw⁻ 0 (q19 c4) ∷
   rw 1 (q90 c4) ∷
   re 3 1 (ℓ "亜亝仒亝亜仒") ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q91 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 5 (q91 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 8 (q90 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   re 11 1 (ℓ "亜亝仒亝亜仒") ∷
   rw⁻ 10 (q21 c4) ∷
   rw 11 (q91 c4) ∷
   rw⁻ 12 (q92 c4) ∷
   rw 13 (q91 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 15 (q92 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "仓") ∷
   re 5 6 (ℓ "仓") ∷
   re 0 6 (ℓ "伲") ∷ []) Eq.refl

-- nat-SWbc @02102441: 23 steps
lem-nat-SWbc-at02102441 : Ws → ⟪ (ℓ "乼伲乼") ⟫ʷ ≈ ⟪ (ℓ "估") ⟫ʷ
lem-nat-SWbc-at02102441 c4 = derive (ℓ "乼伲乼") (ℓ "估")
  (re 1 1 (ℓ "亜亞仓亞亜仓") ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   re 3 1 (ℓ "亘亙仒亙亘仒") ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   re 11 1 (ℓ "亘亙仒亙亘仒") ∷
   rw⁻ 10 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw⁻ 12 (q92 c4) ∷
   rw 13 (q20 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 15 (q92 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "仙") ∷
   re 5 6 (ℓ "仙") ∷
   re 0 6 (ℓ "估") ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = wpE 398 c4
  q94 : Ws → Eqn
  q94 c4 = wpE 957 c4
  q95 : Ws → Eqn
  q95 c4 = wpE 958 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 959 c4
  q97 : Ws → Eqn
  q97 c4 = eqn (ℓ "亴乼") (ℓ "乼亴") (c₃ (CZ ↑) (Swap))

-- nat-SWbc @233442: 23 steps
lem-nat-SWbc-at233442 : Ws → ⟪ (ℓ "乼仂乼") ⟫ʷ ≈ ⟪ (ℓ "仆") ⟫ʷ
lem-nat-SWbc-at233442 c4 = derive (ℓ "乼仂乼") (ℓ "仆")
  (re 1 1 (ℓ "亐云仁云亐仁") ∷
   rw⁻ 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   re 3 1 (ℓ "五亖亴亖五亴") ∷
   rw⁻ 2 (q95 c4) ∷
   rw 3 (q96 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw 5 (q96 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw 8 (q94 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   re 11 1 (ℓ "五亖亴亖五亴") ∷
   rw⁻ 10 (q95 c4) ∷
   rw 11 (q96 c4) ∷
   rw⁻ 12 (q97 c4) ∷
   rw 13 (q96 c4) ∷
   rw⁻ 14 (q95 c4) ∷
   rw⁻ 15 (q97 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "仅") ∷
   re 5 6 (ℓ "仅") ∷
   re 0 6 (ℓ "仆") ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = wpE 965 c4
  q99 : Ws → Eqn
  q99 c4 = wpE 966 c4

-- nat-SWbc @2442: 23 steps
lem-nat-SWbc-at2442 : Ws → ⟪ (ℓ "乼仆乼") ⟫ʷ ≈ ⟪ (ℓ "仂") ⟫ʷ
lem-nat-SWbc-at2442 c4 = derive (ℓ "乼仆乼") (ℓ "仂")
  (re 1 1 (ℓ "五井仅井五仅") ∷
   rw⁻ 0 (q95 c4) ∷
   rw 1 (q98 c4) ∷
   re 3 1 (ℓ "亐互亴互亐亴") ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw 8 (q98 c4) ∷
   rw⁻ 9 (q95 c4) ∷
   re 11 1 (ℓ "亐互亴互亐亴") ∷
   rw⁻ 10 (q93 c4) ∷
   rw 11 (q99 c4) ∷
   rw⁻ 12 (q97 c4) ∷
   rw 13 (q99 c4) ∷
   rw⁻ 14 (q93 c4) ∷
   rw⁻ 15 (q97 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (ℓ "仁") ∷
   re 5 6 (ℓ "仁") ∷
   re 0 6 (ℓ "仂") ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = wpE 553 c4
  q101 : Ws → Eqn
  q101 c4 = wpE 972 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 551 c4
  q103 : Ws → Eqn
  q103 c4 = wpE 973 c4
  q104 : Ws → Eqn
  q104 c4 = eqn (ℓ "乊仺") (ℓ "仺乊") (c₃ (Swap ↑) (CZ))
  q105 : Ws → Eqn
  q105 c4 = wlE 6 (lit c4)

-- nat-SWbc @143143: 23 steps
lem-nat-SWbc-at143143 : Ws → ⟪ (ℓ "乊伅乊") ⟫ʷ ≈ ⟪ (ℓ "仼") ⟫ʷ
lem-nat-SWbc-at143143 c4 = derive (ℓ "乊伅乊") (ℓ "仼")
  (re 1 1 (ℓ "亜亝伄亝亜伄") ∷
   rw⁻ 0 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   re 3 1 (ℓ "五亗仺亗五仺") ∷
   rw⁻ 2 (q102 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q104 c4) ∷
   rw 5 (q103 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 7 (q104 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 9 (q100 c4) ∷
   re 11 1 (ℓ "五亗仺亗五仺") ∷
   rw⁻ 10 (q102 c4) ∷
   rw 11 (q103 c4) ∷
   rw 12 (q104 c4) ∷
   rw 13 (q103 c4) ∷
   rw⁻ 14 (q102 c4) ∷
   rw 15 (q104 c4) ∷
   rw 16 (q105 c4) ∷
   re 2 6 (ℓ "任") ∷
   re 5 6 (ℓ "任") ∷
   re 0 6 (ℓ "仼") ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = wpE 992 c4
  q107 : Ws → Eqn
  q107 c4 = wlE 1126 (lit c4)

-- sym-ab @0314213240: 18 steps
lem-sym-ab-at0314213240 : Ws → ⟪ (ℓ "侅") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-sym-ab-at0314213240 c4 = derive (ℓ "侅") (ℓ "佯")
  (re 0 1 (ℓ "京亮侄亮京侄") ∷
   re 2 1 (ℓ "亰亳佶亳亰佶") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw⁻ 2 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   re 4 1 (ℓ "伝") ∷
   re 7 1 (ℓ "伝") ∷
   re 2 6 (ℓ "伞") ∷
   re 5 1 (ℓ "亰亳佶亳亰佶") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw⁻ 5 (q106 c4) ∷
   rw 5 (q107 c4) ∷
   re 7 1 (ℓ "伝") ∷
   re 10 1 (ℓ "伝") ∷
   re 5 6 (ℓ "伞") ∷
   re 0 6 (ℓ "佯") ∷ []) Eq.refl

-- sym-ab @03243240: 18 steps
lem-sym-ab-at03243240 : Ws → ⟪ (ℓ "佯") ⟫ʷ ≈ ⟪ (ℓ "侅") ⟫ʷ
lem-sym-ab-at03243240 c4 = derive (ℓ "佯") (ℓ "侅")
  (re 0 1 (ℓ "京亮伞亮京伞") ∷
   re 2 1 (ℓ "交亥伝亥交伝") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q107 c4) ∷
   rw 2 (q106 c4) ∷
   re 4 1 (ℓ "佶") ∷
   re 7 1 (ℓ "佶") ∷
   re 2 6 (ℓ "侄") ∷
   re 5 1 (ℓ "交亥伝亥交伝") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q107 c4) ∷
   rw 5 (q106 c4) ∷
   re 7 1 (ℓ "佶") ∷
   re 10 1 (ℓ "佶") ∷
   re 5 6 (ℓ "侄") ∷
   re 0 6 (ℓ "侅") ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = wpE 1014 c4
  q109 : Ws → Eqn
  q109 c4 = wpE 1015 c4
  q110 : Ws → Eqn
  q110 c4 = wlE 1210 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wpE 1016 c4
  q112 : Ws → Eqn
  q112 c4 = wlE 1211 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 1212 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 928 (lit c4)

-- nat-S @01143043: 31 steps
lem-nat-S-at01143043 : Ws → ⟪ (ℓ "丹侧丹") ⟫ʷ ≈ ⟪ (ℓ "俜") ⟫ʷ
lem-nat-S-at01143043 c4 = derive (ℓ "丹侧丹") (ℓ "俜")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   re 1 1 (ℓ "五井仃井五仃") ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   re 3 1 (ℓ "二于人于二人") ∷
   re 5 1 (ℓ "乐") ∷
   re 8 1 (ℓ "乐") ∷
   rw⁻ 2 (q110 c4) ∷
   re 4 1 (ℓ "伝") ∷
   re 7 1 (ℓ "伝") ∷
   re 2 6 (ℓ "伞") ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   re 6 1 (ℓ "二于人于二人") ∷
   re 8 1 (ℓ "乐") ∷
   re 11 1 (ℓ "乐") ∷
   rw⁻ 5 (q110 c4) ∷
   re 7 1 (ℓ "伝") ∷
   re 10 1 (ℓ "伝") ∷
   re 5 6 (ℓ "伞") ∷
   rw 6 (q111 c4) ∷
   rw⁻ 7 (q112 c4) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 9 (q113 c4) ∷
   rw 10 (q114 c4) ∷
   re 0 6 (ℓ "佯") ∷
   re 2 1 (ℓ "俗") ∷
   re 4 1 (ℓ "俛") ∷
   re 0 5 (ℓ "俜") ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = wlE 1216 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wlE 1217 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wlE 1218 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wlE 1219 (lit c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (ℓ "伝乬") (ℓ "乬伝") (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))
  q120 : Ws → Eqn
  q120 c4 = wlE 322 (lit c4)

-- nat-SWbc @033440: 23 steps
lem-nat-SWbc-at033440 : Ws → ⟪ (ℓ "乬佭乬") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-nat-SWbc-at033440 c4 = derive (ℓ "乬佭乬") (ℓ "佯")
  (re 1 1 (ℓ "交产传产交传") ∷
   rw⁻ 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   re 3 1 (ℓ "京亭伝亭京伝") ∷
   rw⁻ 2 (q117 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 5 (q118 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 8 (q116 c4) ∷
   rw⁻ 9 (q115 c4) ∷
   re 11 1 (ℓ "京亭伝亭京伝") ∷
   rw⁻ 10 (q117 c4) ∷
   rw 11 (q118 c4) ∷
   rw⁻ 12 (q119 c4) ∷
   rw 13 (q118 c4) ∷
   rw⁻ 14 (q117 c4) ∷
   rw⁻ 15 (q119 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (ℓ "伞") ∷
   re 5 6 (ℓ "伞") ∷
   re 0 6 (ℓ "佯") ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = wlE 1231 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wlE 1232 (lit c4)

-- nat-SWbc @03243240: 23 steps
lem-nat-SWbc-at03243240 : Ws → ⟪ (ℓ "乬佯乬") ⟫ʷ ≈ ⟪ (ℓ "佭") ⟫ʷ
lem-nat-SWbc-at03243240 c4 = derive (ℓ "乬佯乬") (ℓ "佭")
  (re 1 1 (ℓ "京亮伞亮京伞") ∷
   rw⁻ 0 (q117 c4) ∷
   rw 1 (q121 c4) ∷
   re 3 1 (ℓ "交亥伝亥交伝") ∷
   rw⁻ 2 (q115 c4) ∷
   rw 3 (q122 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 5 (q122 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 8 (q121 c4) ∷
   rw⁻ 9 (q117 c4) ∷
   re 11 1 (ℓ "交亥伝亥交伝") ∷
   rw⁻ 10 (q115 c4) ∷
   rw 11 (q122 c4) ∷
   rw⁻ 12 (q119 c4) ∷
   rw 13 (q122 c4) ∷
   rw⁻ 14 (q115 c4) ∷
   rw⁻ 15 (q119 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (ℓ "传") ∷
   re 5 6 (ℓ "传") ∷
   re 0 6 (ℓ "佭") ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = wpE 177 c4
  q124 : Ws → Eqn
  q124 c4 = wpE 178 c4
  q125 : Ws → Eqn
  q125 c4 = wpE 175 c4
  q126 : Ws → Eqn
  q126 c4 = wpE 176 c4
  q127 : Ws → Eqn
  q127 c4 = eqn (ℓ "仪乬") (ℓ "乬仪") (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))

-- nat-SWbc @03103441: 23 steps
lem-nat-SWbc-at03103441 : Ws → ⟪ (ℓ "乬佧乬") ⟫ʷ ≈ ⟪ (ℓ "佩") ⟫ʷ
lem-nat-SWbc-at03103441 c4 = derive (ℓ "乬佧乬") (ℓ "佩")
  (re 1 1 (ℓ "亘些仱些亘仱") ∷
   rw⁻ 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   re 3 1 (ℓ "亠亡仪亡亠仪") ∷
   rw⁻ 2 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw⁻ 7 (q127 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 9 (q123 c4) ∷
   re 11 1 (ℓ "亠亡仪亡亠仪") ∷
   rw⁻ 10 (q125 c4) ∷
   rw 11 (q126 c4) ∷
   rw⁻ 12 (q127 c4) ∷
   rw 13 (q126 c4) ∷
   rw⁻ 14 (q125 c4) ∷
   rw⁻ 15 (q127 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (ℓ "仫") ∷
   re 5 6 (ℓ "仫") ∷
   re 0 6 (ℓ "佩") ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = wpE 274 c4
  q129 : Ws → Eqn
  q129 c4 = wpE 273 c4

-- nat-SWbc @0310243241: 23 steps
lem-nat-SWbc-at0310243241 : Ws → ⟪ (ℓ "乬佩乬") ⟫ʷ ≈ ⟪ (ℓ "佧") ⟫ʷ
lem-nat-SWbc-at0310243241 c4 = derive (ℓ "乬佩乬") (ℓ "佧")
  (re 1 1 (ℓ "亠亢仫亢亠仫") ∷
   rw⁻ 0 (q125 c4) ∷
   rw 1 (q128 c4) ∷
   re 3 1 (ℓ "亘亙仪亙亘仪") ∷
   rw⁻ 2 (q123 c4) ∷
   rw 3 (q129 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 5 (q129 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 7 (q127 c4) ∷
   rw 8 (q128 c4) ∷
   rw⁻ 9 (q125 c4) ∷
   re 11 1 (ℓ "亘亙仪亙亘仪") ∷
   rw⁻ 10 (q123 c4) ∷
   rw 11 (q129 c4) ∷
   rw⁻ 12 (q127 c4) ∷
   rw 13 (q129 c4) ∷
   rw⁻ 14 (q123 c4) ∷
   rw⁻ 15 (q127 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (ℓ "仱") ∷
   re 5 6 (ℓ "仱") ∷
   re 0 6 (ℓ "佧") ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = wlE 184 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wpE 294 c4
  q132 : Ws → Eqn
  q132 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))
  q133 : Ws → Eqn
  q133 c4 = wlE 432 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = wlE 433 (lit c4)

-- cQ @0310213442: 7 steps
lem-cQ-at0310213442 : Ws → ⟪ (ℓ "亐亰") ⟫ʷ ≈ ⟪ (ℓ "亰亐") ⟫ʷ
lem-cQ-at0310213442 c4 = derive (ℓ "亐亰") (ℓ "亰亐")
  (rw 0 (q130 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 2 (q133 c4) ∷
   rw 1 (q132 c4) ∷
   rw⁻ 0 (q134 c4) ∷
   rw⁻ 1 (q130 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = wlE 1303 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wpE 262 c4

-- sym-ab @03122031: 18 steps
lem-sym-ab-at03122031 : Ws → ⟪ (ℓ "佰") ⟫ʷ ≈ ⟪ (ℓ "佦") ⟫ʷ
lem-sym-ab-at03122031 c4 = derive (ℓ "佰") (ℓ "佦")
  (re 0 1 (ℓ "亘些但些亘但") ∷
   re 2 1 (ℓ "交亦伽亦交伽") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw 2 (q135 c4) ∷
   rw⁻ 2 (q136 c4) ∷
   re 4 1 (ℓ "以") ∷
   re 7 1 (ℓ "以") ∷
   re 2 6 (ℓ "仦") ∷
   re 5 1 (ℓ "交亦伽亦交伽") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw 5 (q135 c4) ∷
   rw⁻ 5 (q136 c4) ∷
   re 7 1 (ℓ "以") ∷
   re 10 1 (ℓ "以") ∷
   re 5 6 (ℓ "仦") ∷
   re 0 6 (ℓ "佦") ∷ []) Eq.refl

-- sym-ab @0312243041: 18 steps
lem-sym-ab-at0312243041 : Ws → ⟪ (ℓ "佴") ⟫ʷ ≈ ⟪ (ℓ "侈") ⟫ʷ
lem-sym-ab-at0312243041 c4 = derive (ℓ "佴") (ℓ "侈")
  (re 0 1 (ℓ "亰亲伹亲亰伹") ∷
   re 2 1 (ℓ "亘亚伸亚亘伸") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q89 c4) ∷
   rw 2 (q88 c4) ∷
   re 4 1 (ℓ "佼") ∷
   re 7 1 (ℓ "佼") ∷
   re 2 6 (ℓ "侇") ∷
   re 5 1 (ℓ "亘亚伸亚亘伸") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q89 c4) ∷
   rw 5 (q88 c4) ∷
   re 7 1 (ℓ "佼") ∷
   re 10 1 (ℓ "佼") ∷
   re 5 6 (ℓ "侇") ∷
   re 0 6 (ℓ "侈") ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = wlE 330 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (ℓ "二争") (ℓ "争二") (c₃ (CCZ) (CX₁₀))
  q139 : Ws → Eqn
  q139 c4 = wlE 331 (lit c4)

-- cQ @0214233041: 7 steps
lem-cQ-at0214233041 : Ws → ⟪ (ℓ "亰二") ⟫ʷ ≈ ⟪ (ℓ "二亰") ⟫ʷ
lem-cQ-at0214233041 c4 = derive (ℓ "亰二") (ℓ "二亰")
  (rw 0 (q137 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 3 (q138 c4) ∷
   rw⁻ 2 (q139 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw⁻ 1 (q137 c4) ∷ []) Eq.refl

-- sym-ab @0214233041: 18 steps
lem-sym-ab-at0214233041 : Ws → ⟪ (ℓ "佢") ⟫ʷ ≈ ⟪ (ℓ "佋") ⟫ʷ
lem-sym-ab-at0214233041 c4 = derive (ℓ "佢") (ℓ "佋")
  (re 0 1 (ℓ "亰亱佡亱亰佡") ∷
   re 2 1 (ℓ "亜亟佗亟亜佗") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   re 4 1 (ℓ "伿") ∷
   re 7 1 (ℓ "伿") ∷
   re 2 6 (ℓ "佊") ∷
   re 5 1 (ℓ "亜亟佗亟亜佗") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   re 7 1 (ℓ "伿") ∷
   re 10 1 (ℓ "伿") ∷
   re 5 6 (ℓ "佊") ∷
   re 0 6 (ℓ "佋") ∷ []) Eq.refl

-- sym-ab @03143041: 18 steps
lem-sym-ab-at03143041 : Ws → ⟪ (ℓ "侈") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-sym-ab-at03143041 c4 = derive (ℓ "侈") (ℓ "佴")
  (re 0 1 (ℓ "亰亲侇亲亰侇") ∷
   re 2 1 (ℓ "亠亣佼亣亠佼") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   re 4 1 (ℓ "伸") ∷
   re 7 1 (ℓ "伸") ∷
   re 2 6 (ℓ "伹") ∷
   re 5 1 (ℓ "亠亣佼亣亠佼") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q88 c4) ∷
   rw 5 (q89 c4) ∷
   re 7 1 (ℓ "伸") ∷
   re 10 1 (ℓ "伸") ∷
   re 5 6 (ℓ "伹") ∷
   re 0 6 (ℓ "佴") ∷ []) Eq.refl

-- sym-ab @0213243041: 18 steps
lem-sym-ab-at0213243041 : Ws → ⟪ (ℓ "佋") ⟫ʷ ≈ ⟪ (ℓ "佢") ⟫ʷ
lem-sym-ab-at0213243041 c4 = derive (ℓ "佋") (ℓ "佢")
  (re 0 1 (ℓ "亰亱佊亱亰佊") ∷
   re 2 1 (ℓ "亘些伿些亘伿") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q6 c4) ∷
   rw 2 (q5 c4) ∷
   re 4 1 (ℓ "佗") ∷
   re 7 1 (ℓ "佗") ∷
   re 2 6 (ℓ "佡") ∷
   re 5 1 (ℓ "亘些伿些亘伿") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q6 c4) ∷
   rw 5 (q5 c4) ∷
   re 7 1 (ℓ "佗") ∷
   re 10 1 (ℓ "佗") ∷
   re 5 6 (ℓ "佡") ∷
   re 0 6 (ℓ "佢") ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wlE 1319 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 1155 (lit c4)

-- sym-ab @02142041: 18 steps
lem-sym-ab-at02142041 : Ws → ⟪ (ℓ "余") ⟫ʷ ≈ ⟪ (ℓ "伲") ⟫ʷ
lem-sym-ab-at02142041 c4 = derive (ℓ "余") (ℓ "伲")
  (re 0 1 (ℓ "亜亞佘亞亜佘") ∷
   re 2 1 (ℓ "亰亳佗亳亰佗") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q140 c4) ∷
   rw⁻ 2 (q141 c4) ∷
   re 4 1 (ℓ "仒") ∷
   re 7 1 (ℓ "仒") ∷
   re 2 6 (ℓ "仓") ∷
   re 5 1 (ℓ "亰亳佗亳亰佗") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   re 7 1 (ℓ "仒") ∷
   re 10 1 (ℓ "仒") ∷
   re 5 6 (ℓ "仓") ∷
   re 0 6 (ℓ "伲") ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = wlE 30 (lit c4)
  q143 : Ws → Eqn
  q143 c4 = wlE 31 (lit c4)
  q144 : Ws → Eqn
  q144 c4 = wlE 135 (lit c4)
  q145 : Ws → Eqn
  q145 c4 = wlE 1340 (lit c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (ℓ "丫伺") (ℓ "伺丫") (c₂ (Swap) (CZ ↑))
  q147 : Ws → Eqn
  q147 c4 = wlE 18 (lit c4)

-- nat-SWbc @02132130: 23 steps
lem-nat-SWbc-at02132130 : Ws → ⟪ (ℓ "丫佅丫") ⟫ʷ ≈ ⟪ (ℓ "似") ⟫ʷ
lem-nat-SWbc-at02132130 c4 = derive (ℓ "丫佅丫") (ℓ "似")
  (re 1 1 (ℓ "交亦佄亦交佄") ∷
   rw⁻ 0 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   re 3 1 (ℓ "亘些伺些亘伺") ∷
   rw⁻ 2 (q144 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw 5 (q145 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 7 (q146 c4) ∷
   rw 8 (q143 c4) ∷
   rw⁻ 9 (q142 c4) ∷
   re 11 1 (ℓ "亘些伺些亘伺") ∷
   rw⁻ 10 (q144 c4) ∷
   rw 11 (q145 c4) ∷
   rw 12 (q146 c4) ∷
   rw 13 (q145 c4) ∷
   rw⁻ 14 (q144 c4) ∷
   rw 15 (q146 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (ℓ "伻") ∷
   re 5 6 (ℓ "伻") ∷
   re 0 6 (ℓ "似") ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = wlE 136 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = wlE 63 (lit c4)

-- nat-SWbc @02132031: 23 steps
lem-nat-SWbc-at02132031 : Ws → ⟪ (ℓ "丫似丫") ⟫ʷ ≈ ⟪ (ℓ "佅") ⟫ʷ
lem-nat-SWbc-at02132031 c4 = derive (ℓ "丫似丫") (ℓ "佅")
  (re 1 1 (ℓ "亘亚伻亚亘伻") ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q148 c4) ∷
   re 3 1 (ℓ "交产伺产交伺") ∷
   rw⁻ 2 (q142 c4) ∷
   rw 3 (q149 c4) ∷
   rw 4 (q146 c4) ∷
   rw 5 (q149 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 7 (q146 c4) ∷
   rw 8 (q148 c4) ∷
   rw⁻ 9 (q144 c4) ∷
   re 11 1 (ℓ "交产伺产交伺") ∷
   rw⁻ 10 (q142 c4) ∷
   rw 11 (q149 c4) ∷
   rw 12 (q146 c4) ∷
   rw 13 (q149 c4) ∷
   rw⁻ 14 (q142 c4) ∷
   rw 15 (q146 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (ℓ "佄") ∷
   re 5 6 (ℓ "佄") ∷
   re 0 6 (ℓ "佅") ∷ []) Eq.refl

-- sym-ab @02102441: 18 steps
lem-sym-ab-at02102441 : Ws → ⟪ (ℓ "伲") ⟫ʷ ≈ ⟪ (ℓ "余") ⟫ʷ
lem-sym-ab-at02102441 c4 = derive (ℓ "伲") (ℓ "余")
  (re 0 1 (ℓ "亜亞仓亞亜仓") ∷
   re 2 1 (ℓ "亘亙仒亙亘仒") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q141 c4) ∷
   rw 2 (q140 c4) ∷
   re 4 1 (ℓ "佗") ∷
   re 7 1 (ℓ "佗") ∷
   re 2 6 (ℓ "佘") ∷
   re 5 1 (ℓ "亘亙仒亙亘仒") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q141 c4) ∷
   rw 5 (q140 c4) ∷
   re 7 1 (ℓ "佗") ∷
   re 10 1 (ℓ "佗") ∷
   re 5 6 (ℓ "佘") ∷
   re 0 6 (ℓ "余") ∷ []) Eq.refl

-- cQ @0213243041: 7 steps
lem-cQ-at0213243041 : Ws → ⟪ (ℓ "亰二") ⟫ʷ ≈ ⟪ (ℓ "二亰") ⟫ʷ
lem-cQ-at0213243041 c4 = derive (ℓ "亰二") (ℓ "二亰")
  (rw 0 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q12 c4) ∷ []) Eq.refl

-- sym-ab @0314203241: 18 steps
lem-sym-ab-at0314203241 : Ws → ⟪ (ℓ "佾") ⟫ʷ ≈ ⟪ (ℓ "佩") ⟫ʷ
lem-sym-ab-at0314203241 c4 = derive (ℓ "佾") (ℓ "佩")
  (re 0 1 (ℓ "亠亢佽亢亠佽") ∷
   re 2 1 (ℓ "亰亳佼亳亰佼") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q140 c4) ∷
   rw⁻ 2 (q141 c4) ∷
   re 4 1 (ℓ "仪") ∷
   re 7 1 (ℓ "仪") ∷
   re 2 6 (ℓ "仫") ∷
   re 5 1 (ℓ "亰亳佼亳亰佼") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   re 7 1 (ℓ "仪") ∷
   re 10 1 (ℓ "仪") ∷
   re 5 6 (ℓ "仫") ∷
   re 0 6 (ℓ "佩") ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (ℓ "丫伽") (ℓ "伽丫") (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat-SWbc @03122130: 23 steps
lem-nat-SWbc-at03122130 : Ws → ⟪ (ℓ "丫佲丫") ⟫ʷ ≈ ⟪ (ℓ "佰") ⟫ʷ
lem-nat-SWbc-at03122130 c4 = derive (ℓ "丫佲丫") (ℓ "佰")
  (re 1 1 (ℓ "交产伾产交伾") ∷
   rw⁻ 0 (q142 c4) ∷
   rw 1 (q149 c4) ∷
   re 3 1 (ℓ "亘亚伽亚亘伽") ∷
   rw⁻ 2 (q144 c4) ∷
   rw 3 (q148 c4) ∷
   rw 4 (q150 c4) ∷
   rw 5 (q148 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 7 (q150 c4) ∷
   rw 8 (q149 c4) ∷
   rw⁻ 9 (q142 c4) ∷
   re 11 1 (ℓ "亘亚伽亚亘伽") ∷
   rw⁻ 10 (q144 c4) ∷
   rw 11 (q148 c4) ∷
   rw 12 (q150 c4) ∷
   rw 13 (q148 c4) ∷
   rw⁻ 14 (q144 c4) ∷
   rw 15 (q150 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (ℓ "但") ∷
   re 5 6 (ℓ "但") ∷
   re 0 6 (ℓ "佰") ∷ []) Eq.refl

-- nat-SWbc @03122031: 23 steps
lem-nat-SWbc-at03122031 : Ws → ⟪ (ℓ "丫佰丫") ⟫ʷ ≈ ⟪ (ℓ "佲") ⟫ʷ
lem-nat-SWbc-at03122031 c4 = derive (ℓ "丫佰丫") (ℓ "佲")
  (re 1 1 (ℓ "亘些但些亘但") ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   re 3 1 (ℓ "交亦伽亦交伽") ∷
   rw⁻ 2 (q142 c4) ∷
   rw 3 (q143 c4) ∷
   rw 4 (q150 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 7 (q150 c4) ∷
   rw 8 (q145 c4) ∷
   rw⁻ 9 (q144 c4) ∷
   re 11 1 (ℓ "交亦伽亦交伽") ∷
   rw⁻ 10 (q142 c4) ∷
   rw 11 (q143 c4) ∷
   rw 12 (q150 c4) ∷
   rw 13 (q143 c4) ∷
   rw⁻ 14 (q142 c4) ∷
   rw 15 (q150 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (ℓ "伾") ∷
   re 5 6 (ℓ "伾") ∷
   re 0 6 (ℓ "佲") ∷ []) Eq.refl

-- sym-ab @0310243241: 18 steps
lem-sym-ab-at0310243241 : Ws → ⟪ (ℓ "佩") ⟫ʷ ≈ ⟪ (ℓ "佾") ⟫ʷ
lem-sym-ab-at0310243241 c4 = derive (ℓ "佩") (ℓ "佾")
  (re 0 1 (ℓ "亠亢仫亢亠仫") ∷
   re 2 1 (ℓ "亘亙仪亙亘仪") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q141 c4) ∷
   rw 2 (q140 c4) ∷
   re 4 1 (ℓ "佼") ∷
   re 7 1 (ℓ "佼") ∷
   re 2 6 (ℓ "佽") ∷
   re 5 1 (ℓ "亘亙仪亙亘仪") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q141 c4) ∷
   rw 5 (q140 c4) ∷
   re 7 1 (ℓ "佼") ∷
   re 10 1 (ℓ "佼") ∷
   re 5 6 (ℓ "佽") ∷
   re 0 6 (ℓ "佾") ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wpE 8 c4
  q152 : Ws → Eqn
  q152 c4 = wpE 111 c4

-- sym-ab @0330: 18 steps
lem-sym-ab-at0330 : Ws → ⟪ (ℓ "佬") ⟫ʷ ≈ ⟪ (ℓ "佲") ⟫ʷ
lem-sym-ab-at0330 c4 = derive (ℓ "佬") (ℓ "佲")
  (re 0 1 (ℓ "交产伜产交伜") ∷
   re 2 1 (ℓ "亐互伛互亐伛") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q151 c4) ∷
   rw⁻ 2 (q152 c4) ∷
   re 4 1 (ℓ "伽") ∷
   re 7 1 (ℓ "伽") ∷
   re 2 6 (ℓ "伾") ∷
   re 5 1 (ℓ "亐互伛互亐伛") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q151 c4) ∷
   rw⁻ 5 (q152 c4) ∷
   re 7 1 (ℓ "伽") ∷
   re 10 1 (ℓ "伽") ∷
   re 5 6 (ℓ "伾") ∷
   re 0 6 (ℓ "佲") ∷ []) Eq.refl

-- sym-ab @022330: 18 steps
lem-sym-ab-at022330 : Ws → ⟪ (ℓ "伴") ⟫ʷ ≈ ⟪ (ℓ "佅") ⟫ʷ
lem-sym-ab-at022330 c4 = derive (ℓ "伴") (ℓ "佅")
  (re 0 1 (ℓ "交亦伒亦交伒") ∷
   re 2 1 (ℓ "二于休于二休") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q28 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   re 4 1 (ℓ "伺") ∷
   re 7 1 (ℓ "伺") ∷
   re 2 6 (ℓ "佄") ∷
   re 5 1 (ℓ "二于休于二休") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q28 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   re 7 1 (ℓ "伺") ∷
   re 10 1 (ℓ "伺") ∷
   re 5 6 (ℓ "佄") ∷
   re 0 6 (ℓ "佅") ∷ []) Eq.refl

-- sym-ab @03122130: 18 steps
lem-sym-ab-at03122130 : Ws → ⟪ (ℓ "佲") ⟫ʷ ≈ ⟪ (ℓ "佬") ⟫ʷ
lem-sym-ab-at03122130 c4 = derive (ℓ "佲") (ℓ "佬")
  (re 0 1 (ℓ "交产伾产交伾") ∷
   re 2 1 (ℓ "亘亚伽亚亘伽") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw 2 (q152 c4) ∷
   rw⁻ 2 (q151 c4) ∷
   re 4 1 (ℓ "伛") ∷
   re 7 1 (ℓ "伛") ∷
   re 2 6 (ℓ "伜") ∷
   re 5 1 (ℓ "亘亚伽亚亘伽") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw 5 (q152 c4) ∷
   rw⁻ 5 (q151 c4) ∷
   re 7 1 (ℓ "伛") ∷
   re 10 1 (ℓ "伛") ∷
   re 5 6 (ℓ "伜") ∷
   re 0 6 (ℓ "佬") ∷ []) Eq.refl
