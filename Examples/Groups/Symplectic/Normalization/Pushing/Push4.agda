------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Push4 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open NFBase using (NormalFormInjective ; NormalForm)
import Normalization.CosetNF as CosetNF


--open import Examples.Groups.Symplectic.NewCosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Data.Sum


private variable
  n : ℕ


open import Data.Vec
open import Data.Nat using (s≤s ; z≤n)

open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (aux-DS ; dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd' ; gen-DH-box)
import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T

------------------------------------------------------------------------
-- Right coset action

-- The right action of a generator on a coset: ract c b returns the
-- residual circuit b' and the coset c' reached from c by b, so that
-- [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ (see ract-sound below).
-- A wire-0 gate touches only the bottom D box; the lifted ML' box (on
-- wires ≥ 1) is inert.  So the coset update leaves ml alone and only
-- rewrites the D box (via the single-gate D-box push aux-DS / gen-DH-box),
-- the emitted direction escaping one wire up.
ract : ∀ {n} -> ML' (₁₊ n) -> D → SympGate 1 → Circuit (₁₊ n) × D
ract {n} _ d S-gate = dir-of-DS d , d-of-DS d
ract {n} _ d H-gate = (Hdir d ↓ᵏ n) , Hd' d

------------------------------------------------------------------------
-- Soundness of the coset action

[_]ᶜ = [_]ᵐˡ'

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c b we have [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract-sound : ∀ {n} ml d g →
  let
    open PB ((₂₊ n) QRel,_===_)
    (dir , d') = ract {n} ml d g
  in

    ([ d ]ᵈ • [ ml ]ᵐˡ' ↑) • [ gate₁ g ]ʷ ≈ dir ↑ • ([ d' ]ᵈ • [ ml ]ᵐˡ' ↑)

ract-sound {n} ml d S-gate = begin
  ([ d ]ᵈ • [ ml ]ᵐˡ' ↑) • S                          ≈⟨ assoc ⟩
  [ d ]ᵈ • ([ ml ]ᵐˡ' ↑ • S)                          ≈⟨ cright (sym (lemma-comm-S-w↑ [ ml ]ᵐˡ')) ⟩
  [ d ]ᵈ • (S • [ ml ]ᵐˡ' ↑)                          ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • S) • [ ml ]ᵐˡ' ↑                          ≈⟨ cleft ds-step ⟩
  ((dir-of-DS d ↑) • [ d-of-DS d ]ᵈ) • [ ml ]ᵐˡ' ↑    ≈⟨ assoc ⟩
  (dir-of-DS d ↑) • ([ d-of-DS d ]ᵈ • [ ml ]ᵐˡ' ↑)    ∎
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  -- aux-DS is stated over LM-Sym's D box; ML'T.dbox-eq bridges to Section's.
  ds-step : [ d ]ᵈ • S ≈ (dir-of-DS d ↑) • [ d-of-DS d ]ᵈ
  ds-step = trans (cleft (refl' (ML'T.dbox-eq d)))
              (trans (aux-DS d)
                (cright (refl' (Eq.sym (ML'T.dbox-eq (d-of-DS d))))))
ract-sound {n} ml d H-gate = begin
  ([ d ]ᵈ • [ ml ]ᵐˡ' ↑) • H                             ≈⟨ assoc ⟩
  [ d ]ᵈ • ([ ml ]ᵐˡ' ↑ • H)                             ≈⟨ cright (sym (lemma-comm-H-w↑ [ ml ]ᵐˡ')) ⟩
  [ d ]ᵈ • (H • [ ml ]ᵐˡ' ↑)                             ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • H) • [ ml ]ᵐˡ' ↑                             ≈⟨ cleft dh-step ⟩
  (((Hdir d ↓ᵏ n) ↑) • [ Hd' d ]ᵈ) • [ ml ]ᵐˡ' ↑        ≈⟨ assoc ⟩
  ((Hdir d ↓ᵏ n) ↑) • ([ Hd' d ]ᵈ • [ ml ]ᵐˡ' ↑)        ∎
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  -- gen-DH-box is stated over LM-Sym's D box; ML'T.dbox-eq bridges to Section's.
  dh-step : [ d ]ᵈ • H ≈ ((Hdir d ↓ᵏ n) ↑) • [ Hd' d ]ᵈ
  dh-step = trans (cleft (refl' (ML'T.dbox-eq d)))
              (trans (gen-DH-box d)
                (cright (refl' (Eq.sym (ML'T.dbox-eq (Hd' d))))))
