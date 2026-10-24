{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD225 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D225 (Sᴰ : SD225) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-box-perm-2134 : Ws → St 2314
  lem-box-perm-2134 = pickᴰ 0 Sᴰ
  lem-box-perm-2134-at1221 : Ws → St 2315
  lem-box-perm-2134-at1221 = pickᴰ 1 Sᴰ
  lem-S-sym-xt-at14213243 : Ws → St 2236
  lem-S-sym-xt-at14213243 = pickᴰ 2 Sᴰ
  lem-box-perm-4132-at03102132 : Ws → St 2241
  lem-box-perm-4132-at03102132 = pickᴰ 3 Sᴰ
  lem-box-box-1-at021021 : Ws → St 1515
  lem-box-box-1-at021021 = pickᴰ 4 Sᴰ
  lem-box-perm-2431-at0314203241 : Ws → St 2245
  lem-box-perm-2431-at0314203241 = pickᴰ 5 Sᴰ
  lem-box-perm-3241-at02142041 : Ws → St 2246
  lem-box-perm-3241-at02142041 = pickᴰ 6 Sᴰ
  lem-box-perm-4213-at02132031 : Ws → St 2248
  lem-box-perm-4213-at02132031 = pickᴰ 7 Sᴰ
  lem-L-CX10-2 : Ws → St 1764
  lem-L-CX10-2 = pickᴰ 8 Sᴰ
  lem-Tu-box-at0314203241 : Ws → St 2251
  lem-Tu-box-at0314203241 = pickᴰ 9 Sᴰ
  lem-box-box-3-at03102132 : Ws → St 2252
  lem-box-box-3-at03102132 = pickᴰ 10 Sᴰ
  lem-L-CCZ-1 : Ws → St 2068
  lem-L-CCZ-1 = pickᴰ 11 Sᴰ
  lem-L-CCZ-0 : Ws → St 2257
  lem-L-CCZ-0 = pickᴰ 12 Sᴰ
  lem-ckt-TST-at0440 : Ws → St 2316
  lem-ckt-TST-at0440 = pickᴰ 13 Sᴰ
  lem-L-CCZ013-0 : Ws → St 2317
  lem-L-CCZ013-0 = pickᴰ 14 Sᴰ
  lem-nf-cx-cczat0 : Ws → St 2318
  lem-nf-cx-cczat0 = pickᴰ 15 Sᴰ
  lem-ckt-TST : Ws → St 2319
  lem-ckt-TST = pickᴰ 16 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1764 (lem-L-CX10-2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2257 (lem-L-CCZ-0 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 420 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2241 (lem-box-perm-4132-at03102132 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2251 (lem-Tu-box-at0314203241 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2245 (lem-box-perm-2431-at0314203241 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 2246 (lem-box-perm-3241-at02142041 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 2252 (lem-box-box-3-at03102132 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2248 (lem-box-perm-4213-at02132031 c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 1372 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 2318 (lem-nf-cx-cczat0 c4)

-- F1-cx-ccz@0: 13 steps
lem-F1-cx-cczat0 : Ws → ⟪ (ℓ "亇侬侬亇丢侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亇侬侬亇丢") ⟫ʷ ≈ ⟪ (ℓ "侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢") ⟫ʷ
lem-F1-cx-cczat0 c4 = derive (ℓ "亇侬侬亇丢侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亇侬侬亇丢") (ℓ "侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢")
  (rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q4 c4) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 0 (q11 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = sE 2317 (lem-L-CCZ013-0 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 2068 (lem-L-CCZ-1 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 2314 (lem-box-perm-2134 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1515 (lem-box-box-1-at021021 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 2315 (lem-box-perm-2134-at1221 c4)

-- nf-toff-ccz@0: 5 steps
lem-nf-toff-cczat0 : Ws → ⟪ (ℓ "亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢") ⟫ʷ ≈ ⟪ (ℓ "亹伭") ⟫ʷ
lem-nf-toff-cczat0 c4 = derive (ℓ "亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亄俄俄亄丢侧侧侧亄俄俄亄丢亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢俄亇侧侧亇丢亄侧侧亄丢亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢") (ℓ "亹伭")
  (rw 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 2319 (lem-ckt-TST c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2236 (lem-S-sym-xt-at14213243 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 2316 (lem-ckt-TST-at0440 c4)

-- ckt-B: 3 steps
lem-ckt-B : Ws → ⟪ (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-B c4 = derive (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 0 (q17 c4) ∷
   rw 48 (q18 c4) ∷
   rw 0 (q19 c4) ∷ []) Eq.refl
