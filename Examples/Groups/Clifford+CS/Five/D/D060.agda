{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD060 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D060 (Sᴰ : SD060) where

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
  lem-comm-CCZ134-CK02 : Ws → St 1655
  lem-comm-CCZ134-CK02 = pickᴰ 0 Sᴰ
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 1 Sᴰ
  lem-F4-I-K1 : Ws → St 1409
  lem-F4-I-K1 = pickᴰ 2 Sᴰ
  lem-F4-I-K2 : Ws → St 1410
  lem-F4-I-K2 = pickᴰ 3 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 4 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 5 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 6 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 7 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 8 Sᴰ
  lem-box-cP-at04233042 : Ws → St 1656
  lem-box-cP-at04233042 = pickᴰ 9 Sᴰ
  lem-F4-I-CS0 : Ws → St 1401
  lem-F4-I-CS0 = pickᴰ 10 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 11 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 12 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 13 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 14 Sᴰ
  lem-box-perm-1423-at04203243 : Ws → St 1657
  lem-box-perm-1423-at04203243 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1618 (lem-F4-K3-I c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1401 (lem-F4-I-CS0 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1386 (lem-F4-I-I c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1409 (lem-F4-I-K1 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1411 (lem-F4-I-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1410 (lem-F4-I-K2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1432 (lem-F4-I-CS1 c4)

-- ckt-TST part49: 77 steps
lem-ckt-TST-part49 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄並亊並丢俄並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊並丢並丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part49 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄並亊並丢俄並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊並丢並丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 322 (q1 c4) ∷
   rw⁻ 321 (q2 c4) ∷
   rw⁻ 320 (q3 c4) ∷
   rw⁻ 319 (q4 c4) ∷
   rw⁻ 318 (q4 c4) ∷
   rw⁻ 317 (q3 c4) ∷
   rw⁻ 316 (q2 c4) ∷
   rw⁻ 315 (q5 c4) ∷
   rw⁻ 314 (q4 c4) ∷
   rw⁻ 313 (q4 c4) ∷
   rw⁻ 312 (q5 c4) ∷
   rw⁻ 311 (q2 c4) ∷
   rw⁻ 310 (q3 c4) ∷
   rw⁻ 309 (q4 c4) ∷
   rw⁻ 308 (q4 c4) ∷
   rw⁻ 307 (q3 c4) ∷
   rw⁻ 306 (q6 c4) ∷
   rw⁻ 305 (q2 c4) ∷
   rw⁻ 304 (q3 c4) ∷
   rw⁻ 303 (q4 c4) ∷
   rw⁻ 302 (q4 c4) ∷
   rw⁻ 301 (q3 c4) ∷
   rw⁻ 300 (q2 c4) ∷
   rw⁻ 299 (q5 c4) ∷
   rw⁻ 298 (q4 c4) ∷
   rw⁻ 297 (q4 c4) ∷
   rw⁻ 296 (q5 c4) ∷
   rw⁻ 295 (q2 c4) ∷
   rw⁻ 294 (q3 c4) ∷
   rw⁻ 293 (q4 c4) ∷
   rw⁻ 292 (q4 c4) ∷
   rw⁻ 291 (q3 c4) ∷
   rw⁻ 290 (q2 c4) ∷
   rw⁻ 289 (q5 c4) ∷
   rw⁻ 288 (q6 c4) ∷
   rw⁻ 287 (q6 c4) ∷
   rw⁻ 286 (q5 c4) ∷
   rw⁻ 285 (q4 c4) ∷
   rw⁻ 284 (q4 c4) ∷
   rw⁻ 283 (q4 c4) ∷
   rw⁻ 282 (q2 c4) ∷
   rw⁻ 281 (q5 c4) ∷
   rw⁻ 280 (q6 c4) ∷
   rw⁻ 279 (q6 c4) ∷
   rw⁻ 278 (q5 c4) ∷
   rw⁻ 277 (q4 c4) ∷
   rw⁻ 276 (q1 c4) ∷
   rw⁻ 327 (q7 c4) ∷
   rw⁻ 326 (q8 c4) ∷
   rw⁻ 325 (q9 c4) ∷
   rw⁻ 324 (q8 c4) ∷
   rw⁻ 323 (q10 c4) ∷
   rw⁻ 322 (q11 c4) ∷
   rw⁻ 321 (q11 c4) ∷
   rw⁻ 320 (q10 c4) ∷
   rw⁻ 319 (q8 c4) ∷
   rw⁻ 318 (q12 c4) ∷
   rw⁻ 317 (q11 c4) ∷
   rw⁻ 316 (q11 c4) ∷
   rw⁻ 315 (q12 c4) ∷
   rw⁻ 314 (q8 c4) ∷
   rw⁻ 313 (q10 c4) ∷
   rw⁻ 312 (q11 c4) ∷
   rw⁻ 311 (q11 c4) ∷
   rw⁻ 310 (q10 c4) ∷
   rw⁻ 309 (q13 c4) ∷
   rw⁻ 308 (q8 c4) ∷
   rw⁻ 307 (q10 c4) ∷
   rw⁻ 306 (q11 c4) ∷
   rw⁻ 305 (q11 c4) ∷
   rw⁻ 304 (q10 c4) ∷
   rw⁻ 303 (q8 c4) ∷
   rw⁻ 302 (q12 c4) ∷
   rw⁻ 301 (q11 c4) ∷
   rw⁻ 300 (q11 c4) ∷
   rw⁻ 299 (q12 c4) ∷
   rw⁻ 298 (q8 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wlE 1487 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 1488 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1657 (lem-box-perm-1423-at04203243 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1656 (lem-box-cP-at04233042 c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 1332 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 1489 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1655 (lem-comm-CCZ134-CK02 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (ℓ "上京") (ℓ "京上") (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q22 : Ws → Eqn
  q22 c4 = wlE 1490 (lit c4)

-- F4-CS1-K2 @0440: 21 steps
lem-F4-CS1-K2-at0440 : Ws → ⟪ (ℓ "与俭与临") ⟫ʷ ≈ ⟪ (ℓ "临与俭与") ⟫ʷ
lem-F4-CS1-K2-at0440 c4 = derive (ℓ "与俭与临") (ℓ "临与俭与")
  (rw⁻ 2 (q14 c4) ∷
   re 1 1 (ℓ "侒些俫些俬") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw⁻ 2 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   re 6 1 (ℓ "俫") ∷
   re 8 1 (ℓ "俬") ∷
   re 4 5 (ℓ "俭") ∷
   rw⁻ 0 (q22 c4) ∷ []) Eq.refl
