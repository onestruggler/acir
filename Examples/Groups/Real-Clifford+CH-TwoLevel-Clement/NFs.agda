------------------------------------------------------------------------
-- Presentations of groups
--
-- The normal forms: Clément's (38) for Subcase 3.4.2, and the form of
-- Subcase 3.4.1 (generated).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.NFs where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Quantum.Synthesis.Ring using (RootTwo)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms using (Form ; form)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check using (Hˡ ; Xˡ ; Zˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree


private
  𝟎 𝟏 -𝟏 𝟐 : Z
  𝟎 = RootTwo (+ 0) (+ 0)
  𝟏 = RootTwo (+ 1) (+ 0)
  -𝟏 = RootTwo -[1+ 0 ] (+ 0)
  𝟐 = RootTwo (+ 2) (+ 0)
  f0 : ∀ {m} → Fin (suc m)
  f0 = zero
  f1 : ∀ {m} → Fin (suc (suc m))
  f1 = suc f0
  f2 : ∀ {m} → Fin (suc (suc (suc m)))
  f2 = suc f1
  f3 : ∀ {m} → Fin (suc (suc (suc (suc m))))
  f3 = suc f2
  f4 : ∀ {m} → Fin (suc (suc (suc (suc (suc m)))))
  f4 = suc f3
  f5 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc m))))))
  f5 = suc f4
  f6 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc m)))))))
  f6 = suc f5
  f7 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc m))))))))
  f7 = suc f6
  f8 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))
  f8 = suc f7
  f9 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))
  f9 = suc f8
  f10 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))
  f10 = suc f9
  f11 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))
  f11 = suc f10
  f12 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))
  f12 = suc f11
  f13 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))
  f13 = suc f12
  f14 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))))
  f14 = suc f13
  f15 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))))
  f15 = suc f14
  f16 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))))))
  f16 = suc f15
  f17 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))))))
  f17 = suc f16
  f18 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))))))))
  f18 = suc f17
  f19 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))))))))
  f19 = suc f18

nfData : (nf : NF) → NFData nf
nfData nf38 = record
  { forms = ((form (RootTwo (+ 0) (+ 1)) ((RootTwo (+ 0) (+ 2)) ∷ 𝟐 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟐 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 4) (+ 0)) ∷ [])) ∷ (form (RootTwo -[1+ 1 ] (+ 1)) ((RootTwo (+ 0) -[1+ 1 ]) ∷ (RootTwo -[1+ 1 ] (+ 0)) ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo -[1+ 1 ] (+ 0)) ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 4) (+ 0)) ∷ 𝟎 ∷ [])) ∷ (form (RootTwo (+ 1) (+ 1)) (𝟐 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form 𝟏 ((RootTwo -[1+ 1 ] (+ 0)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form (RootTwo (+ 1) (+ 1)) (𝟐 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form 𝟏 ((RootTwo -[1+ 1 ] (+ 0)) ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) -[1+ 1 ]) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ [])
  ; tags = ((just 1) ∷ (just 1) ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ [])
  ; ic = f2 ; id = f3 ; mini = true }
nfData nf341 = record
  { forms = ((form (RootTwo (+ 1) (+ 1)) (𝟐 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form 𝟏 (𝟐 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form (RootTwo (+ 1) (+ 1)) (𝟐 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form (RootTwo (+ 1) (+ 2)) (𝟐 ∷ (RootTwo (+ 0) (+ 2)) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ [])) ∷ [])
  ; tags = (nothing ∷ nothing ∷ nothing ∷ nothing ∷ [])
  ; ic = f0 ; id = f1 ; mini = false }
