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

module Examples.Groups.Symplectic.Normalization.Pushing.Push5 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
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

open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n p-2 p-prime using (gen-dd-cz-tail)
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM

------------------------------------------------------------------------
-- Right coset action

-- The right action of a generator on a coset: ract c b returns the
-- residual circuit b' and the coset c' reached from c by b, so that
-- [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ (see ract-sound below).
-- CZ (wires 0,1) interacts with only the bottom two D boxes; the ML'
-- box, lifted twice onto wires ≥ 2, is inert.  So the coset update
-- rewrites d1, d2 to the DD-CZ image and leaves ml alone, the emitted
-- direction escaping one wire up (BR.Three.DD-CZ-n.gen-dd-cz-tail).
ract : ∀ {n} -> ML' (₁₊ n) -> D -> D → SympGate 2 → Circuit (₂₊ n) × D × D
ract {n} _ d1 d2 CZ-gate =
  (DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ n) ,
  (proj₁ d1 , proj₂ d1 + - proj₁ d2) ,
  (proj₁ d2 , proj₂ d2 + - proj₁ d1)

------------------------------------------------------------------------
-- Soundness of the coset action

[_]ᶜ = [_]ᵐˡ'

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c b we have [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract-sound : ∀ {n} ml d1 d2 g →
  let
    open PB ((₃₊ n) QRel,_===_)
    (dir , d1' , d2') = ract {n} ml d1 d2 g
  in

    ([ d1 ]ᵈ • ([ d2 ]ᵈ • [ ml ]ᵐˡ' ↑) ↑) • [ gate₂ g ]ʷ ≈ dir ↑ •  ([ d1' ]ᵈ • ([ d2' ]ᵈ • [ ml ]ᵐˡ' ↑) ↑)

ract-sound {n} ml d1 d2 CZ-gate = begin
  ([ d1 ]ᵈ • ([ d2 ]ᵈ • Mw ↑) ↑) • CZ
    ≈⟨ cleft bridge-in ⟩
  (LM[ d1 ]ᵈ • (LM[ d2 ]ᵈ • Mw ↑) ↑) • CZ
    ≈⟨ gen-dd-cz-tail d1 d2 Mw ⟩
  ((DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ n) ↑) • (LM[ d1' ]ᵈ • (LM[ d2' ]ᵈ • Mw ↑) ↑)
    ≈⟨ cright bridge-out ⟩
  ((DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ n) ↑) • ([ d1' ]ᵈ • ([ d2' ]ᵈ • Mw ↑) ↑)
  ∎
  where
  open PB ((₃₊ n) QRel,_===_) ; open PP ((₃₊ n) QRel,_===_) ; open SR word-setoid
  Mw = [ ml ]ᵐˡ'
  d1' = (proj₁ d1 , proj₂ d1 + - proj₁ d2)
  d2' = (proj₁ d2 , proj₂ d2 + - proj₁ d1)
  LM[_]ᵈ = LM.[_]ᵈ
  -- gen-dd-cz-tail is over LM-Sym's D box; ML'T.dbox-eq bridges to Section's.
  bridge-in : [ d1 ]ᵈ • ([ d2 ]ᵈ • Mw ↑) ↑ ≈ LM[ d1 ]ᵈ • (LM[ d2 ]ᵈ • Mw ↑) ↑
  bridge-in = refl' (Eq.cong₂ (λ x y → x • ((y • Mw ↑) ↑)) (ML'T.dbox-eq d1) (ML'T.dbox-eq d2))
  bridge-out : LM[ d1' ]ᵈ • (LM[ d2' ]ᵈ • Mw ↑) ↑ ≈ [ d1' ]ᵈ • ([ d2' ]ᵈ • Mw ↑) ↑
  bridge-out = refl' (Eq.cong₂ (λ x y → x • ((y • Mw ↑) ↑))
                 (Eq.sym (ML'T.dbox-eq d1')) (Eq.sym (ML'T.dbox-eq d2')))
