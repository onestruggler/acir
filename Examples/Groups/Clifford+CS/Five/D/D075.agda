{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D075 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1411 ; wl1417 ; wp1267)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K3-at02132031 ; lem-F4-I-S2-at02132031 ; lem-F4-K3-K3-at02132031 ; lem-F4-S2-I-at02132031 ; lem-F4-S2-K3-at02132031 ; lem-F4-S2-S2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-S2-at02132031 ; lem-F4-I-CS2-at02132031 ; lem-F4-S2-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F4-CS2-K3-at02132031 ; lem-F4-K3-CS2-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D052 using (lem-deb-CKS-split-a-at0213243140-part0)
open import Examples.Groups.Clifford+CS.Five.D.D053 using (lem-deb-CKS-split-a-at0213243140-part1)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (lem-deb-CKS-split-a-at0213243140-part0 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sb0-4-31-2 ∷ X3 ∷ Sb0-4-31-2 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ []) (lem-deb-CKS-split-a-at0213243140-part1 c4)

-- deb-CKS-split-a @0213243140: 2 steps
lem-deb-CKS-split-a-at0213243140 : Ws → ⟪ (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-CKS-split-a-at0213243140 c4 = derive (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ CS04 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-23-at02132031 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at02132031 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl1417 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-CS2-at02132031 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at02132031 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K3-K3-at02132031 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-CS2-at02132031 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-K3-at02132031 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-S2-at02132031 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl1411 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at02132031 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at02132031 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at02132031 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S2-I-at02132031 c4)

-- deb-AD-split-a @02132031: 136 steps
lem-deb-AD-split-a-at02132031 : Ws → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-deb-AD-split-a-at02132031 c4 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS04 ∷ [])
  (rw⁻ 0 (q3 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 20 (q4 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 26 (q6 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw 36 (q5 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 32 (q6 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw⁻ 28 (q6 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw 44 (q9 c4) ∷
   rw⁻ 43 (q10 c4) ∷
   rw⁻ 42 (q11 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw⁻ 40 (q11 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q10 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw 48 (q9 c4) ∷
   rw⁻ 47 (q12 c4) ∷
   rw⁻ 46 (q10 c4) ∷
   rw⁻ 45 (q11 c4) ∷
   rw⁻ 44 (q10 c4) ∷
   rw⁻ 43 (q11 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q10 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw 52 (q9 c4) ∷
   rw⁻ 51 (q12 c4) ∷
   rw⁻ 50 (q12 c4) ∷
   rw⁻ 49 (q10 c4) ∷
   rw⁻ 48 (q11 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q11 c4) ∷
   rw⁻ 45 (q10 c4) ∷
   rw⁻ 44 (q10 c4) ∷
   rw⁻ 43 (q10 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q14 c4) ∷
   rw⁻ 54 (q14 c4) ∷
   rw⁻ 53 (q14 c4) ∷
   rw⁻ 52 (q15 c4) ∷
   rw⁻ 51 (q16 c4) ∷
   rw⁻ 50 (q15 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   rw⁻ 48 (q15 c4) ∷
   rw⁻ 47 (q15 c4) ∷
   rw⁻ 46 (q15 c4) ∷
   rw⁻ 45 (q15 c4) ∷
   rw⁻ 44 (q15 c4) ∷
   rw⁻ 43 (q15 c4) ∷
   rw⁻ 42 (q15 c4) ∷
   rw 60 (q9 c4) ∷
   rw⁻ 59 (q17 c4) ∷
   rw⁻ 58 (q12 c4) ∷
   rw⁻ 57 (q12 c4) ∷
   rw⁻ 56 (q12 c4) ∷
   rw⁻ 55 (q10 c4) ∷
   rw⁻ 54 (q11 c4) ∷
   rw⁻ 53 (q10 c4) ∷
   rw⁻ 52 (q11 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q10 c4) ∷
   rw⁻ 48 (q10 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q10 c4) ∷
   rw⁻ 45 (q10 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-I-at02132031 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS2-S2-at02132031 c4)

-- deb-AD-split-b @02132031: 66 steps
lem-deb-AD-split-b-at02132031 : Ws → ⟪ (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-deb-AD-split-b-at02132031 c4 = derive (CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q3 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw 20 (q9 c4) ∷
   rw⁻ 19 (q10 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 17 (q10 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw 24 (q9 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 22 (q10 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 20 (q10 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 18 (q10 c4) ∷
   rw 28 (q9 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 25 (q10 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 21 (q10 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 28 (q15 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw⁻ 26 (q15 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 24 (q15 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw⁻ 35 (q18 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw⁻ 37 (q19 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 35 (q19 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 30 (q4 c4) ∷ []) Eq.refl
