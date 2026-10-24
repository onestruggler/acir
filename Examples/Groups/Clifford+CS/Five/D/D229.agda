{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD229 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D229 (Sᴰ : SD229) where

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
  lem-F1-ck-tctat0-part1 : Ws → St 2345
  lem-F1-ck-tctat0-part1 = pickᴰ 0 Sᴰ
  lem-F1-ck-tctat0-part2 : Ws → St 2346
  lem-F1-ck-tctat0-part2 = pickᴰ 1 Sᴰ
  lem-F1-ck-tctat0-part0 : Ws → St 2347
  lem-F1-ck-tctat0-part0 = pickᴰ 2 Sᴰ
  lem-F1-ck-tctat0-part3 : Ws → St 2348
  lem-F1-ck-tctat0-part3 = pickᴰ 3 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2347 (lem-F1-ck-tctat0-part0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2345 (lem-F1-ck-tctat0-part1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2346 (lem-F1-ck-tctat0-part2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2348 (lem-F1-ck-tctat0-part3 c4)

-- F1-ck-tct@0: 4 steps
lem-F1-ck-tctat0 : Ws → ⟪ (ℓ "亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢") ⟫ʷ
lem-F1-ck-tctat0 c4 = derive (ℓ "亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢亁丽丽亁丢俄亄俄亄俄丽丽丽丢亁丽丽亁丢")
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl
