------------------------------------------------------------------------
-- Presentations of groups
--
-- Every rule of P′ decodes, from the facts at the top pair
--
-- On N = 4 + m indices: the K-free rules from the consecutive facts
-- (Lemma88.Fragment), and the hybrid rules from the facts about the
-- hybrid at the top pair N − 2, N − 1 — the far facts (`TopFar`, and
-- `far-k` against the hybrid two or more below), the pair scalar `sc`,
-- the shifts, the core fact k p = p h k at the top pair, and ki-16,
-- ki-sq at the canonical position — by
-- HybridPair (ki-sink, ki-pp, ki-px, ki-swap, ki-swap′), HybridOne (the
-- one-pair rules) and HybridKK (ki-ki).  ki-yb is still a hypothesis,
-- at every instance.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _<_ ; _≤_)
open import Word.Base using (Word ; WRel ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

module Examples.Groups.Clifford+CS.Lemma88.HybridRules
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Fin using (Fin) renaming (_<_ to _<ᶠ_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_ ; pw ; xw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_ ; kiw)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k using (d)
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
import Examples.Groups.Clifford+CS.Lemma88.HybridCen as HCen
import Examples.Groups.Clifford+CS.Lemma88.HybridPair as HP
import Examples.Groups.Clifford+CS.Lemma88.HybridOne as HO
import Examples.Groups.Clifford+CS.Lemma88.HybridKK as HK

open _R,_===_

private
  N : ℕ
  N = suc (suc (suc (suc m)))

  module FrN = Fr Γ N p p′ l h k

open PB Γ using (_≈_)
open HTop Γ N p p′ l h k using (top ; TopFar)
open HCen Γ m p p′ l h k using (tT ; tT1 ; tB)
open HO Γ m p p′ l h k using (tT<tT1)

-- ki-yb, decoded, at every instance.
YB : Set
YB = ∀ (jj kk ll mm s : Fin N) .(jk : jj <ᶠ kk) .(lm : ll <ᶠ mm) .(jl : jj <ᶠ ll) .(km : kk <ᶠ mm) →
     kk ≢ ll → s ≢ jj → s ≢ kk → s ≢ ll → s ≢ mm →
     (d ʷ) (kiw jj kk s jk • (kiw ll mm s lm • (kiw jj ll s jl • kiw kk mm s km)))
     ≈ (d ʷ) (kiw jj ll s jl • (kiw kk mm s km • (kiw jj kk s jk • kiw ll mm s lm)))

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))))
  (shift : ∀ {j} → suc (suc j) < N →
           (l j • l (suc j)) • k j ≈ k (suc j) • (l j • l (suc j)))
  (far-k : ∀ {j} → suc (suc j) ≤ top → k top • k j ≈ k j • k top)
  (cp : k top • p top ≈ p top • (h top • k top))
  (16₀ : (d ʷ) (kiw tT tT1 tB tT<tT1 • (pw tT1 tB • (pw tT1 tB • pw tT1 tB)))
         ≈ (d ʷ) (pw tT1 tB • (kiw tT tT1 tB tT<tT1 • (pw tT1 tB • kiw tT tT1 tB tT<tT1))))
  (sq₀ : (d ʷ) ((kiw tT tT1 tB tT<tT1 • kiw tT tT1 tB tT<tT1) • (pw tT tB • pw tT1 tB))
         ≈ ε)
  (yb : YB) where

  open FrN.Proofs F using (fragment)
  open HP.Proofs Γ m p p′ l h k F T sc shift
    using (d-ki-sink ; d-ki-pp ; d-ki-px ; d-ki-swap ; d-ki-swap′)
  open HO.Proofs Γ m p p′ l h k F T sc shift cp 16₀ sq₀
    using (d-ki-x ; d-ki-16 ; d-ki-ii ; d-ki-sq)
  open HK.Proofs Γ m p p′ l h k F T sc shift far-k using (d-ki-ki)

  rules : ∀ {u t : Word (GenP N)} → N R, u === t → (d ʷ) u ≈ (d ʷ) t
  rules (pp-id a)                  = fragment (_F,_===_.pp-id a)
  rules (pp-ord a b)               = fragment (_F,_===_.pp-ord a b)
  rules (pp-comm a b c e)          = fragment (_F,_===_.pp-comm a b c e)
  rules (pp-tele a b c)            = fragment (_F,_===_.pp-tele a b c)
  rules (px-sq a a′ s)             = fragment (_F,_===_.px-sq a a′ s)
  rules (px-braid a a′ a″ s s′)    = fragment (_F,_===_.px-braid a a′ a″ s s′)
  rules (px-shrink₁ a a′ c s lt)   = fragment (_F,_===_.px-shrink₁ a a′ c s lt)
  rules (px-shrink₂ a a′ c s lt)   = fragment (_F,_===_.px-shrink₂ a a′ c s lt)
  rules (px-shrink₃ a c′ c s lt)   = fragment (_F,_===_.px-shrink₃ a c′ c s lt)
  rules (px-shrink₄ a c′ c s lt)   = fragment (_F,_===_.px-shrink₄ a c′ c s lt)
  rules (px-inv a a′ s)            = fragment (_F,_===_.px-inv a a′ s)
  rules (px-sign c a b ab)         = fragment (_F,_===_.px-sign c a b ab)
  rules (px-conj a a′ c s ca ca′)  = fragment (_F,_===_.px-conj a a′ c s ca ca′)
  rules (px-conj₂ a a′ s)          = fragment (_F,_===_.px-conj₂ a a′ s)
  rules (px-comm a a′ b b′ s s′ lt) = fragment (_F,_===_.px-comm a a′ b b′ s s′ lt)
  rules (dx-split a b c e ab ce)   = fragment (_F,_===_.dx-split a b c e ab ce)
  rules (ki-sink a b s t ab)       = d-ki-sink a b s t ab
  rules (ki-pp a b s x ab xa xb sa sb) = d-ki-pp a b s x ab xa xb sa sb
  rules (ki-px a b s x y ab xy xa xb ya yb′ sa sb sx sy) =
    d-ki-px a b s x y ab xy xa xb ya yb′ sa sb sx sy
  rules (ki-ki a b c e s ab ce ca cb ea eb sa sb sc se) =
    d-ki-ki a b c e s ab ce ca cb ea eb sa sb sc se
  rules (ki-swap j kk ll s pq qr sj sk sl)  = d-ki-swap j kk ll s pq qr sj sk sl
  rules (ki-swap′ j kk ll s pq qr sj sk sl) = d-ki-swap′ j kk ll s pq qr sj sk sl
  rules (ki-x a b s ab sa sb)      = d-ki-x a b s ab sa sb
  rules (ki-16 a b s ab sa sb)     = d-ki-16 a b s ab sa sb
  rules (ki-ii a b s ab sa sb)     = d-ki-ii a b s ab sa sb
  rules (ki-sq a b s ab sa sb)     = d-ki-sq a b s ab sa sb
  rules (ki-yb jj kk ll mm s jk lm jl km kl sj sk sl sm) =
    yb jj kk ll mm s jk lm jl km kl sj sk sl sm
