------------------------------------------------------------------------
-- Presentations of groups
--
-- The 0→1 level of the coset tower, instantiated hole-free: with the
-- full width-1 well-definedness wd1 (SrelWD1) as the h-wd-ax field,
-- Normalization.CosetNF.SingleLevel.Transfer yields the width-1
-- normal-form map nf : Circuit 1 → Circuit 0 × C 1 — injective and
-- well-defined for the width-1 congruence — and transports the trivial
-- width-0 normal form (Gen 0 is empty) to a NormalForm at width 1 with
-- carrier ⊤ × C 1.  The remaining Extension fields are the width-0/1
-- instances of the generic ones in Normalization.agda (which cannot be
-- imported while its higher-width holes are open).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Tower01
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using ([])
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
open import Word.Properties using (wconcatmap-[f]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
open NFBase using (NormalForm ; NormalFormInjective)
import Normalization.CosetNF as CosetNF

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime
  as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C ; ract ; _≋_ ; sing0)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWD1
  p-2 p-prime using (wd1)
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime
  using (lemma-XM1)

------------------------------------------------------------------------
-- The identity coset at width 1 and its section identities (the
-- width-0/1 instances of Iᶜ / [Ia]≈ε / aux-MB / [I]≈ε' in
-- Normalization.agda).

Ia : A
Ia = (₀ , ₁) , λ ()

I₀ : C 1
I₀ = ([] , ₀) , ([] , Ia)

-- [ Ia ]ᵃ is XM ₁ in the XM form of [_]ᵃ, and XM ₁ collapses for the
-- same reason ZM ₁ does (₁ ⁻¹ is ₁).
[Ia]≈ε : let open PB (1 QRel,_===_) in [ Ia ]ᵃ ≈ ε
[Ia]≈ε = lemma-XM1

[₀]ᵉ≈ε : let open PB (1 QRel,_===_) in [_]ᵉ {0} ₀ ≈ ε
[₀]ᵉ≈ε = refl' (Eq.cong S^ -0#≈0#)
  where open PB (1 QRel,_===_)

aux-MB₀ : let open PB (1 QRel,_===_) in
  [ ([] , ₀) ]ᵐ • [ [] ]ᵛᵇ ≈ ε
aux-MB₀ = trans right-unit [₀]ᵉ≈ε
  where open PB (1 QRel,_===_)

[I]≈ε₀ : let open PB (1 QRel,_===_) in [ I₀ ]ᵐˡ ≈ ε
[I]≈ε₀ = trans (sym assoc) (trans (cleft aux-MB₀) (trans left-unit [Ia]≈ε))
  where open PB (1 QRel,_===_) ; open PP (1 QRel,_===_)

------------------------------------------------------------------------
-- The remaining Transfer hypotheses at this level.

-- The generator embedding: lift a width-0 generator one wire up.
f↥ : Gen 0 → Circuit 1
f↥ = [_]ʷ ∘ _↥

-- (1) h inverts f on the identity coset — vacuous: Gen 0 holds only
-- gate₀, and this gate set has no 0-ary gate.
gen0 : ∀ (x : Gen 0) → ([ x ]ʷ , I₀) ≋ ((ract {0} ᵗ) I₀ (f↥ x))
gen0 (gate₀ ())

-- (3) the embedding respects the width-0 relations (via cong↑).
fwd0 : ∀ {w v : Circuit 0} → (0 QRel,_===_) w v →
  let open PB (1 QRel,_===_) in (f↥ ʷ) w ≈ (f↥ ʷ) v
fwd0 x = Eq.subst₂ _≈_
  (Eq.sym (wconcatmap-[f]ʷ _)) (Eq.sym (wconcatmap-[f]ʷ _))
  (axiom (cong↑ x))
  where open PB (1 QRel,_===_)

-- (5) section/action compatibility: ract-sound, with the residual's
-- lift rewritten from wmap _↥ to (f↥ ʷ).
hract0 : ∀ (c : C 1) (b : Gen 1) →
  let open PB (1 QRel,_===_) in
  [ c ]ᵐˡ • [ b ]ʷ ≈ (f↥ ʷ) (ract c b .proj₁) • [ ract c b .proj₂ ]ᵐˡ
hract0 c b = Eq.subst
  (λ x → ([ c ]ᵐˡ • [ b ]ʷ) ≈ (x • [ ract c b .proj₂ ]ᵐˡ))
  (Eq.sym (wconcatmap-[f]ʷ (ract c b .proj₁)))
  (PushML.ract-sound c b)
  where open PB (1 QRel,_===_)

------------------------------------------------------------------------
-- The 0→1 level, instantiated.  (2) h-wd-ax is wd1 — the point of the
-- whole construction.

module SL01 = CosetNF.SingleLevel
  (0 QRel,_===_) (1 QRel,_===_) (C 1) I₀ f↥ (ract {0}) [_]ᵐˡ

module TR01 = SL01.Transfer gen0 wd1 fwd0 [I]≈ε₀ hract0

-- The width-1 normal-form map and its properties, exported.
open TR01 public
  using ( nf ; nf-wd ; h-wd ; nf-injective
        ; inv-nf ; inv-nf-wd ; inv-nf∘nf=id ; fʷ-injective ; nfx )

------------------------------------------------------------------------
-- The trivial width-0 normal form (Gen 0 is empty: every word ≈ ε) and
-- its transport: a normal form for the width-1 presentation, with
-- carrier ⊤ × C 1.

nfi₀ : NormalFormInjective (0 QRel,_===_) ⊤
nfi₀ = record
  { injection = record
      { to        = λ _ → tt
      ; cong      = λ _ → Eq.refl
      ; injective = λ _ → PB.trans sing0 (PB.sym sing0)
      }
  }

nf₀ : NormalForm (0 QRel,_===_) ⊤
nf₀ = record
  { rightInverse = record
      { to        = λ _ → tt
      ; from      = λ _ → ε
      ; to-cong   = λ _ → Eq.refl
      ; from-cong = λ { Eq.refl → PB.refl }
      ; inverseʳ  = λ { Eq.refl → PB.sym sing0 }
      }
  }

nfp1 : NormalFormInjective (1 QRel,_===_) (⊤ × C 1)
nfp1 = TR01.nfp nfi₀

nfp1' : NormalForm (1 QRel,_===_) (⊤ × C 1)
nfp1' = TR01.nfp' nf₀
