------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level derivations of the P′ rules, first part
--
-- Each lemma is one rule of `Rules` read through `asG`: its sides as
-- words over the two-level generators, equal by Bian and Selinger's
-- relations.  This part has the phase-pair rules — pure phase algebra,
-- the phases commuting totally and i⁴ vanishing — and the two
-- unconditional K rules, whose proofs are the cancellations through
-- relations (17) and (18) that make them need no disjointness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.SoundLemmas (N : ℕ) where

open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i ; X ; K)

open import Examples.Groups.Clifford+CS.Auxiliary.SoundBase N

private
  WT : Set
  WT = Word (TL.Gen N)

  _<F_ : Fin N → Fin N → Set
  _<F_ = Data.Fin._<_
    where import Data.Fin

------------------------------------------------------------------------
-- The phase pairs

sd-pp-id : ∀ (a : Fin N) → i a • i a ^ 3 ≈ ε
sd-pp-id a = i⁴ a

sd-pp-ord : ∀ (a b : Fin N) → (i a • i b ^ 3) ^ 4 ≈ ε
sd-pp-ord a b = begin
  (i a • i b ^ 3) ^ 4
    ≈⟨ ^-• (i a) (i b ^ 3) 4 (ipow-comm a b 1 3) ⟩
  i a ^ 4 • (i b ^ 3) ^ 4
    ≈⟨ front _ (i⁴ a) ⟩
  ε • (i b ^ 3) ^ 4
    ≈⟨ left-unit ⟩
  (i b ^ 3) ^ 4
    ≈⟨ ^^ (i b) 3 4 ⟩
  i b ^ 12
    ≈⟨ sym (^^ (i b) 4 3) ⟩
  (i b ^ 4) ^ 3
    ≈⟨ ^-cong (i b ^ 4) ε 3 (i⁴ b) ⟩
  ε ^ 3
    ≈⟨ ε^k=ε 3 ⟩
  ε ∎

sd-pp-comm : ∀ (a b c d : Fin N) →
             (i a • i b ^ 3) • (i c • i d ^ 3)
             ≈ (i c • i d ^ 3) • (i a • i b ^ 3)
sd-pp-comm a b c d =
  comm-pair (i a) (i b ^ 3) (i c) (i d ^ 3)
            (ipow-comm a c 1 1) (ipow-comm a d 1 3)
            (ipow-comm b c 3 1) (ipow-comm b d 3 3)

sd-pp-tele : ∀ (a b c : Fin N) →
             (i a • i b ^ 3) • (i b • i c ^ 3) ≈ i a • i c ^ 3
sd-pp-tele a b c = begin
  (i a • i b ^ 3) • (i b • i c ^ 3)
    ≈⟨ assoc ⟩
  i a • (i b ^ 3 • (i b • i c ^ 3))
    ≈⟨ back (i a) (sym assoc) ⟩
  i a • ((i b ^ 3 • i b) • i c ^ 3)
    ≈⟨ back (i a) (front _ (sym (^-+ (i b) 3 1))) ⟩
  i a • (i b ^ 4 • i c ^ 3)
    ≈⟨ back (i a) (front _ (i⁴ b)) ⟩
  i a • (ε • i c ^ 3)
    ≈⟨ back (i a) left-unit ⟩
  i a • i c ^ 3 ∎

------------------------------------------------------------------------
-- The unconditional K rules

sd-kk-inv : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
            (K a b ab • (K c d cd • (i c • i d)))
            • (K c d cd • (K a b ab • (i a • i b))) ≈ ε
sd-kk-inv a b c d ab cd = begin
  (K a b ab • (K c d cd • (i c • i d)))
  • (K c d cd • (K a b ab • (i a • i b)))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • (K c d cd • (((i c • i d) • K c d cd) • (K a b ab • (i a • i b))))
    ≈⟨ back _ (back _ (front _ (iiK c d cd))) ⟩
  K a b ab • (K c d cd • ((K c d cd • (i c • i d)) • (K a b ab • (i a • i b))))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • ((K c d cd • (K c d cd • (i c • i d))) • (K a b ab • (i a • i b)))
    ≈⟨ back _ (front _ (K²ii c d cd)) ⟩
  K a b ab • (ε • (K a b ab • (i a • i b)))
    ≈⟨ back _ left-unit ⟩
  K a b ab • (K a b ab • (i a • i b))
    ≈⟨ K²ii a b ab ⟩
  ε ∎

sd-kk-bridge : ∀ (a b c d e f : Fin N)
                 .(ab : a <F b) .(cd : c <F d) .(ef : e <F f) →
               K a b ab • (K c d cd • (i c • i d))
               ≈ (K a b ab • (K e f ef • (i e • i f)))
                 • (K e f ef • (K c d cd • (i c • i d)))
sd-kk-bridge a b c d e f ab cd ef = sym (begin
  (K a b ab • (K e f ef • (i e • i f)))
  • (K e f ef • (K c d cd • (i c • i d)))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • (K e f ef • (((i e • i f) • K e f ef) • (K c d cd • (i c • i d))))
    ≈⟨ back _ (back _ (front _ (iiK e f ef))) ⟩
  K a b ab • (K e f ef • ((K e f ef • (i e • i f)) • (K c d cd • (i c • i d))))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • ((K e f ef • (K e f ef • (i e • i f))) • (K c d cd • (i c • i d)))
    ≈⟨ back _ (front _ (K²ii e f ef)) ⟩
  K a b ab • (ε • (K c d cd • (i c • i d)))
    ≈⟨ back _ left-unit ⟩
  K a b ab • (K c d cd • (i c • i d)) ∎)
