{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD056 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D056 (Sᴰ : SD056) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-K3-at0213243140 : Ws → St 1407
  lem-F4-I-K3-at0213243140 = pickᴰ 0 Sᴰ
  lem-F4-I-S2-at0213243140 : Ws → St 1408
  lem-F4-I-S2-at0213243140 = pickᴰ 1 Sᴰ
  lem-F4-K3-K3-at0213243140 : Ws → St 1410
  lem-F4-K3-K3-at0213243140 = pickᴰ 2 Sᴰ
  lem-F4-K3-S2-at0213243140 : Ws → St 1411
  lem-F4-K3-S2-at0213243140 = pickᴰ 3 Sᴰ
  lem-F4-S2-K3-at0213243140 : Ws → St 1413
  lem-F4-S2-K3-at0213243140 = pickᴰ 4 Sᴰ
  lem-F4-S2-S2-at0213243140 : Ws → St 1414
  lem-F4-S2-S2-at0213243140 = pickᴰ 5 Sᴰ
  lem-F4-I-CS2-at0213243140 : Ws → St 1415
  lem-F4-I-CS2-at0213243140 = pickᴰ 6 Sᴰ
  lem-F4-S2-CS2-at0213243140 : Ws → St 1416
  lem-F4-S2-CS2-at0213243140 = pickᴰ 7 Sᴰ
  lem-F4-CS2-CS2-at0213243140 : Ws → St 1417
  lem-F4-CS2-CS2-at0213243140 = pickᴰ 8 Sᴰ
  lem-F4-CS2-S2-at0213243140 : Ws → St 1419
  lem-F4-CS2-S2-at0213243140 = pickᴰ 9 Sᴰ
  lem-F4-CS2-K3-at0213243140 : Ws → St 1420
  lem-F4-CS2-K3-at0213243140 = pickᴰ 10 Sᴰ
  lem-F4-K3-CS2-at0213243140 : Ws → St 1421
  lem-F4-K3-CS2-at0213243140 = pickᴰ 11 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0213243140 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0213243140 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-K3-at0213243140 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-S2-at0213243140 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-S2-at0213243140 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-S2-at0213243140 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-S2-at0213243140 c4)

-- deb-CKS @0213243140 part2: 173 steps
lem-deb-CKS-at0213243140-part2 : Ws → ⟪ (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) ⟫ʷ
lem-deb-CKS-at0213243140-part2 c4 = derive (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ []) (CCZ014 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ S0 ∷ X0 ∷ S0 ∷ CS04 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS01 ∷ [])
  (rw 80 (q1 c4) ∷
   rw 135 (q2 c4) ∷
   rw 132 (q3 c4) ∷
   rw 129 (q3 c4) ∷
   rw 126 (q3 c4) ∷
   rw 123 (q1 c4) ∷
   rw 120 (q4 c4) ∷
   rw 117 (q1 c4) ∷
   rw 114 (q4 c4) ∷
   rw 111 (q1 c4) ∷
   rw 108 (q1 c4) ∷
   rw 105 (q2 c4) ∷
   rw 102 (q3 c4) ∷
   rw 99 (q3 c4) ∷
   rw 96 (q3 c4) ∷
   rw 93 (q1 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q1 c4) ∷
   rw 84 (q4 c4) ∷
   rw 81 (q1 c4) ∷
   rw 136 (q2 c4) ∷
   rw 133 (q3 c4) ∷
   rw 130 (q3 c4) ∷
   rw 127 (q3 c4) ∷
   rw 124 (q1 c4) ∷
   rw 121 (q4 c4) ∷
   rw 118 (q1 c4) ∷
   rw 115 (q4 c4) ∷
   rw 112 (q1 c4) ∷
   rw 109 (q1 c4) ∷
   rw 106 (q2 c4) ∷
   rw 103 (q3 c4) ∷
   rw 100 (q3 c4) ∷
   rw 97 (q3 c4) ∷
   rw 94 (q1 c4) ∷
   rw 91 (q4 c4) ∷
   rw 88 (q1 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q1 c4) ∷
   rw 137 (q2 c4) ∷
   rw 134 (q3 c4) ∷
   rw 131 (q3 c4) ∷
   rw 128 (q3 c4) ∷
   rw 125 (q1 c4) ∷
   rw 122 (q4 c4) ∷
   rw 119 (q1 c4) ∷
   rw 116 (q4 c4) ∷
   rw 113 (q1 c4) ∷
   rw 110 (q1 c4) ∷
   rw 107 (q2 c4) ∷
   rw 104 (q3 c4) ∷
   rw 101 (q3 c4) ∷
   rw 98 (q3 c4) ∷
   rw 95 (q1 c4) ∷
   rw 92 (q4 c4) ∷
   rw 89 (q1 c4) ∷
   rw 86 (q4 c4) ∷
   rw 83 (q1 c4) ∷
   rw 138 (q5 c4) ∷
   rw 135 (q6 c4) ∷
   rw 132 (q6 c4) ∷
   rw 129 (q6 c4) ∷
   rw 126 (q7 c4) ∷
   rw 123 (q8 c4) ∷
   rw 120 (q7 c4) ∷
   rw 117 (q8 c4) ∷
   rw 114 (q7 c4) ∷
   rw 111 (q7 c4) ∷
   rw 108 (q5 c4) ∷
   rw 105 (q6 c4) ∷
   rw 102 (q6 c4) ∷
   rw 99 (q6 c4) ∷
   rw 96 (q7 c4) ∷
   rw 93 (q8 c4) ∷
   rw 90 (q7 c4) ∷
   rw 87 (q8 c4) ∷
   rw 84 (q7 c4) ∷
   rw 139 (q2 c4) ∷
   rw 136 (q3 c4) ∷
   rw 133 (q3 c4) ∷
   rw 130 (q3 c4) ∷
   rw 127 (q1 c4) ∷
   rw 124 (q4 c4) ∷
   rw 121 (q1 c4) ∷
   rw 118 (q4 c4) ∷
   rw 115 (q1 c4) ∷
   rw 112 (q1 c4) ∷
   rw 109 (q2 c4) ∷
   rw 106 (q3 c4) ∷
   rw 103 (q3 c4) ∷
   rw 100 (q3 c4) ∷
   rw 97 (q1 c4) ∷
   rw 94 (q4 c4) ∷
   rw 91 (q1 c4) ∷
   rw 88 (q4 c4) ∷
   rw 85 (q1 c4) ∷
   rw 140 (q5 c4) ∷
   rw 137 (q6 c4) ∷
   rw 134 (q6 c4) ∷
   rw 131 (q6 c4) ∷
   rw 128 (q7 c4) ∷
   rw 125 (q8 c4) ∷
   rw 122 (q7 c4) ∷
   rw 119 (q8 c4) ∷
   rw 116 (q7 c4) ∷
   rw 113 (q7 c4) ∷
   rw 110 (q5 c4) ∷
   rw 107 (q6 c4) ∷
   rw 104 (q6 c4) ∷
   rw 101 (q6 c4) ∷
   rw 98 (q7 c4) ∷
   rw 95 (q8 c4) ∷
   rw 92 (q7 c4) ∷
   rw 89 (q8 c4) ∷
   rw 86 (q7 c4) ∷
   rw 141 (q2 c4) ∷
   rw 138 (q3 c4) ∷
   rw 135 (q3 c4) ∷
   rw 132 (q3 c4) ∷
   rw 129 (q1 c4) ∷
   rw 126 (q4 c4) ∷
   rw 123 (q1 c4) ∷
   rw 120 (q4 c4) ∷
   rw 117 (q1 c4) ∷
   rw 114 (q1 c4) ∷
   rw 111 (q2 c4) ∷
   rw 108 (q3 c4) ∷
   rw 105 (q3 c4) ∷
   rw 102 (q3 c4) ∷
   rw 99 (q1 c4) ∷
   rw 96 (q4 c4) ∷
   rw 93 (q1 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q1 c4) ∷
   rw 142 (q9 c4) ∷
   rw 139 (q10 c4) ∷
   rw 136 (q10 c4) ∷
   rw 133 (q10 c4) ∷
   rw 130 (q11 c4) ∷
   rw 127 (q12 c4) ∷
   rw 124 (q11 c4) ∷
   rw 121 (q12 c4) ∷
   rw 118 (q11 c4) ∷
   rw 115 (q11 c4) ∷
   rw 112 (q9 c4) ∷
   rw 109 (q10 c4) ∷
   rw 106 (q10 c4) ∷
   rw 103 (q10 c4) ∷
   rw 100 (q11 c4) ∷
   rw 97 (q12 c4) ∷
   rw 94 (q11 c4) ∷
   rw 91 (q12 c4) ∷
   rw 88 (q11 c4) ∷
   rw 143 (q9 c4) ∷
   rw 140 (q10 c4) ∷
   rw 137 (q10 c4) ∷
   rw 134 (q10 c4) ∷
   rw 131 (q11 c4) ∷
   rw 128 (q12 c4) ∷
   rw 125 (q11 c4) ∷
   rw 122 (q12 c4) ∷
   rw 119 (q11 c4) ∷
   rw 116 (q11 c4) ∷
   rw 113 (q9 c4) ∷
   rw 110 (q10 c4) ∷
   rw 107 (q10 c4) ∷
   rw 104 (q10 c4) ∷
   rw 101 (q11 c4) ∷
   rw 98 (q12 c4) ∷
   rw 95 (q11 c4) ∷
   rw 92 (q12 c4) ∷
   rw 89 (q11 c4) ∷
   rw 144 (q9 c4) ∷ []) Eq.refl
