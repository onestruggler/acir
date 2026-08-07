------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli rules, and the theorem that they present (ℤ/pℤ × ℤ/pℤ)ⁿ.
--
-- The rules are the n-wire Pauli presentation: generators X and Z on
-- each wire, each of order p, all commuting.  They are built on the
-- circuit framework, the gate set being two one-qubit gates and no
-- two-qubit gate, so Circuit.Base.Gen supplies the generators and the
-- wire shifts.
--
-- The semantic target is the additive group of Pauli n = (ℤ/pℤ × ℤ/pℤ)ⁿ,
-- a Pauli word being read as the vector of its X- and Z-exponents.  The
-- normal form is X^a Z^b on each wire, read straight off that vector;
-- normalising a word is just collecting exponents, which the
-- commutation lemmas below already support.
--
-- This file is `Presentation-Alt` because Examples.Groups.Pauli
-- .Presentation presents the same group by other means.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=2 #-}


open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Circuit.Base
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)
import Presentation.Construct.Properties.DirectProduct as DP
import Examples.Groups.Cyclic.Cyclic as Cyclic


open import Data.Fin using (Fin)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality

module Examples.Groups.Pauli.Presentation-Alt
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime


------------------------------------------------------------------------
-- Generators, from the circuit framework
--
-- The gate set is two one-qubit gates and no two-qubit gate, so
-- Circuit.Base.Gen gives back exactly the datatype this file used to
-- declare by hand: gate₁ X-gate, gate₁ Z-gate, and _↥.  The gate₂
-- constructor is there but uninhabited, XZGate 2 being empty.

data XZGate : ℕ → Set where
  X-gate : XZGate 1
  Z-gate : XZGate 1

private module SC = Circuit.Base XZGate
open SC public using (Gen ; _↥ ; _↑ ; _↓)

-- The old constructor names, as pattern synonyms, so that uses in both
-- expression and pattern position go on working untouched.
pattern X-gen = SC.gate₁ X-gate
pattern Z-gen = SC.gate₁ Z-gate

[_⇑] : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
[_⇑] {n} = ([_]ʷ ∘ _↥) WB.ʷ

[_⇑]' : ∀ {n} → Word (Gen n) → Word (Gen (₁₊ n))
[_⇑]' {n} = wmap _↥

-- _↑ and _↓ are the framework's now (opened above).  They agree with
-- the definitions that stood here: SC._↑ is wmap (_↥ᵏ 1), and g ↥ᵏ 1
-- reduces to g ↥, so this is the same function.

lemma-[⇑]=[⇑]' : ∀ {n} (w : Word (Gen n)) → [ w ⇑] ≡ [ w ⇑]'
lemma-[⇑]=[⇑]' {n} [ x ]ʷ = Eq.refl
lemma-[⇑]=[⇑]' {n} ε = Eq.refl
lemma-[⇑]=[⇑]' {n} (w • w₁) = Eq.cong₂ _•_ (lemma-[⇑]=[⇑]' w) (lemma-[⇑]=[⇑]' w₁)

X : ∀ {n} → Word (Gen (₁₊ n))
X = [ X-gen ]ʷ

Z : ∀ {n} → Word (Gen (₁₊ n))
Z = [ Z-gen ]ʷ

-- Group-specific axioms only.  cong↑, and a gate commuting with
-- anything shifted up past it, are the same for every circuit
-- presentation and come from Lift-Relation below.
module Base where
  infix 4 _SRel,_===_
  data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

    order-X :  ∀ {n} → (₁₊ n) SRel,  X ^ p === ε
    order-Z :  ∀ {n} → (₁₊ n) SRel,  Z ^ p === ε
    comm-Z-X : ∀ {n} → (₁₊ n) SRel,  Z • X === X • Z

private module LR = SC.Lift-Relation Base._SRel,_===_

infix 4 _QRel,_===_
_QRel,_===_ : (n : ℕ) → WRel (Gen n)
_QRel,_===_ = LR._VRel,_===_

-- Structural rules, exported directly.  lemma-cong↑ is the framework's
-- now; the hand-written copy that stood here was the same induction.
open LR public using (srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑)

pattern order-X  = srel Base.order-X
pattern order-Z  = srel Base.order-Z
pattern comm-Z-X = srel Base.comm-Z-X

-- comm-X and comm-Z were structural axioms; they are instances of comm₁
-- now.  Definitions rather than pattern synonyms: as synonyms the
-- implicit g is a meta the goal does not always pin down.
comm-X : ∀ {n} {g : Gen (₁₊ n)} → (₂₊ n) QRel, [ g ↥ ]ʷ • X === X • [ g ↥ ]ʷ
comm-X {g = g} = comm₁ X-gate g

comm-Z : ∀ {n} {g : Gen (₁₊ n)} → (₂₊ n) QRel, [ g ↥ ]ʷ • Z === Z • [ g ↥ ]ʷ
comm-Z {g = g} = comm₁ Z-gate g


import Data.Nat.Literals as NL
open import Agda.Builtin.FromNat
open import Data.Fin.Literals
import Data.Nat.Literals as NL


lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
lemma-^-↑ w ₀ = auto
lemma-^-↑ w ₁ = auto
lemma-^-↑ w (₂₊ k) = begin
  (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (₁₊ k)) ⟩
  (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
  ((w • w ^ ₁₊ k) ↑) ∎
  where open ≡-Reasoning


instance
  Numℕ' : Number ℕ
  Numℕ' = NL.number 

instance
  NumFin' : Number (Fin p)
  NumFin' = number p

lemma-comm-X-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  X • w ↑ ≈ w ↑ • X

lemma-comm-X-w↑ {n} [ x ]ʷ = sym (axiom comm-X)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-X-w↑ {n} ε = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-X-w↑ {n} (w • w₁) = begin
  X • ((w • w₁) ↑) ≈⟨ refl ⟩
  X • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
  (X • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-X-w↑ w) refl ⟩
  (w ↑ • X) • w₁ ↑ ≈⟨ assoc ⟩
  w ↑ • X • w₁ ↑ ≈⟨ cong refl (lemma-comm-X-w↑ w₁) ⟩
  w ↑ • w₁ ↑ • X ≈⟨ sym assoc ⟩
  ((w • w₁) ↑) • X ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

lemma-comm-Xᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  X ^ k • w ↑ ≈ w ↑ • X ^ k

lemma-comm-Xᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Xᵏ-w↑ {n} ₁ w = lemma-comm-X-w↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Xᵏ-w↑ {n} (₂₊ k) w = begin
  (X • X ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
  X • X ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Xᵏ-w↑ (₁₊ k) w) ⟩
  X • (w ↑) • X ^ ₁₊ k ≈⟨ sym assoc ⟩
  (X • w ↑) • X ^ ₁₊ k ≈⟨ cong (lemma-comm-X-w↑ w) refl ⟩
  (w ↑ • X) • X ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑) • X • X ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-Z-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  Z • w ↑ ≈ w ↑ • Z

lemma-comm-Z-w↑ {n} [ x ]ʷ = sym (axiom comm-Z)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Z-w↑ {n} ε = trans right-unit (sym left-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Z-w↑ {n} (w • w₁) = begin
  Z • ((w • w₁) ↑) ≈⟨ refl ⟩
  Z • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
  (Z • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-Z-w↑ w) refl ⟩
  (w ↑ • Z) • w₁ ↑ ≈⟨ assoc ⟩
  w ↑ • Z • w₁ ↑ ≈⟨ cong refl (lemma-comm-Z-w↑ w₁) ⟩
  w ↑ • w₁ ↑ • Z ≈⟨ sym assoc ⟩
  ((w • w₁) ↑) • Z ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


lemma-comm-Zᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in

  Z ^ k • w ↑ ≈ w ↑ • Z ^ k

lemma-comm-Zᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Zᵏ-w↑ {n} ₁ w = lemma-comm-Z-w↑ w
  where
  open PB ((₂₊ n) QRel,_===_)
lemma-comm-Zᵏ-w↑ {n} (₂₊ k) w = begin
  (Z • Z ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
  Z • Z ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Zᵏ-w↑ (₁₊ k) w) ⟩
  Z • (w ↑) • Z ^ ₁₊ k ≈⟨ sym assoc ⟩
  (Z • w ↑) • Z ^ ₁₊ k ≈⟨ cong (lemma-comm-Z-w↑ w) refl ⟩
  (w ↑ • Z) • Z ^ ₁₊ k ≈⟨ assoc ⟩
  (w ↑) • Z • Z ^ ₁₊ k ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


module XZ-GroupLike where

  private
    variable
      n : ℕ

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} (X-gen) = (X) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (X) ^ p-1 • X ≈ ε
    claim = begin
      (X) ^ p-1 • X ≈⟨ sym (^-+ (X) p-1 1) ⟩
      (X) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (X ^_) ( NP.+-comm p-1 1) ⟩
      (X ^ p) ≈⟨ (axiom order-X) ⟩
      (ε) ∎

  grouplike {₁₊ n} (Z-gen) = (Z) ^ p-1 ,  claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : (Z) ^ p-1 • Z ≈ ε
    claim = begin
      (Z) ^ p-1 • Z ≈⟨ sym (^-+ (Z) p-1 1) ⟩
      (Z) ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (Z ^_) ( NP.+-comm p-1 1) ⟩
      (Z ^ p) ≈⟨ (axiom order-Z) ⟩
      (ε) ∎

  grouplike {₂₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)

-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData where
  private
    variable
      n : ℕ

  -- Commutativity.
  commute : (x y : Gen (₂₊ n)) → let open PB ((₂₊ n) QRel,_===_) in Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  commute {n} Z-gen (y ↥) = just (PB.sym (PB.axiom comm-Z))
  commute {n} (x ↥) Z-gen = just (PB.axiom comm-Z)
  commute {n} X-gen (y ↥) = just (PB.sym (PB.axiom comm-X))
  commute {n} (x ↥) X-gen = just (PB.axiom comm-X)
  
  commute {n@(₁₊ n')} (x ↥) (y ↥) with commute x y
  ... | nothing = nothing
  ... | just eq = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) eq)

  commute {n} _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen (₁₊ n) → ℕ
  ord {n}(X-gen) = 0
  ord {n} (Z-gen) = 1
  ord {₁₊ n} (g ↥) = 2 Nat.+ ord g

  -- Ordering of generators.
  les : Gen (₂₊ n) → Gen (₂₊ n) → Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic (n : ℕ) where
  open CommData
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public



------------------------------------------------------------------------
-- The presentation theorem
--
-- Everything above is the rule set; everything below reads a word as a
-- Pauli vector and shows that reading is an isomorphism.


open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ< ; toℕ<n)
open import Data.Nat.DivMod
  using (_%_ ; _/_ ; m%n<n ; n%n≡0 ; %-distribˡ-+ ; m%n%n≡m%n ; m<n⇒m%n≡m
        ; m≡m%n+[m/n]*n)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)
import Normalization.NormalForm.Setoid as SNF
import Normalization.StarPresentation


open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pI ; pIₙ ; pX ; pZ ; pX₀ ; pZ₀
        ; _+₁_ ; _+ₚ_ ; +ₚ-group
        ; +₁-identityˡ ; +₁-identityʳ
        ; +ₚ-assoc ; +ₚ-comm ; +ₚ-identityˡ ; +ₚ-identityʳ )

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- ℤ/pℤ as the image of ℕ
--
-- mult k is the k-fold sum of ₁; it is the residue of k, so it is the
-- identity on representatives of ℤ/pℤ and vanishes at p.

mult : ℕ → ℤ ₚ
mult ₀      = ₀
mult (₁₊ k) = ₁ + mult k

toℕ-+ : ∀ (a b : ℤ ₚ) → toℕ (a + b) ≡ (toℕ a Nat.+ toℕ b) % p
toℕ-+ a b = toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p)

private
  0%p≡0 : 0 % p ≡ 0
  0%p≡0 = Eq.refl

  mult-% : ∀ k → toℕ (mult k) ≡ k % p
  mult-% ₀      = Eq.sym 0%p≡0
  mult-% (₁₊ k) = begin
    toℕ (₁ + mult k)               ≡⟨ toℕ-+ ₁ (mult k) ⟩
    (1 Nat.+ toℕ (mult k)) % p     ≡⟨ Eq.cong (λ z → (1 Nat.+ z) % p) (mult-% k) ⟩
    (1 Nat.+ k % p) % p            ≡⟨ %-distribˡ-+ 1 (k % p) p ⟩
    (1 % p Nat.+ (k % p) % p) % p  ≡⟨ Eq.cong (λ z → (1 % p Nat.+ z) % p) (m%n%n≡m%n k p) ⟩
    (1 % p Nat.+ k % p) % p        ≡⟨ Eq.sym (%-distribˡ-+ 1 k p) ⟩
    (1 Nat.+ k) % p                ∎
    where open Eq.≡-Reasoning

-- mult undoes toℕ, and kills p.
mult-toℕ : ∀ (a : ℤ ₚ) → mult (toℕ a) ≡ a
mult-toℕ a = toℕ-injective (Eq.trans (mult-% (toℕ a)) (m<n⇒m%n≡m (toℕ<n a)))

mult-p : mult p ≡ ₀
mult-p = toℕ-injective (Eq.trans (mult-% p) (n%n≡0 p))

------------------------------------------------------------------------
-- The semantics
--
-- A generator is the corresponding one-hot Pauli; a word is the sum of
-- its letters.  (This is the extension of ⟦_⟧₀ along the Pauli group,
-- written out so that it can be reasoned about at every width.)

⟦_⟧₀ : Gen n → Pauli n
⟦ X-gen ⟧₀ = pX₀
⟦ Z-gen ⟧₀ = pZ₀
⟦ g ↥ ⟧₀   = pI ∷ ⟦ g ⟧₀

sem : Word (Gen n) → Pauli n
sem [ x ]ʷ  = ⟦ x ⟧₀
sem ε       = pIₙ
sem (w • v) = sem w +ₚ sem v

-- Shifting a word up a wire prefixes the identity.
sem-↑ : ∀ (w : Word (Gen n)) → sem (w ↑) ≡ pI ∷ sem w
sem-↑ [ x ]ʷ  = Eq.refl
sem-↑ ε       = Eq.refl
sem-↑ (w • v) = begin
  sem (w ↑) +ₚ sem (v ↑)      ≡⟨ Eq.cong₂ _+ₚ_ (sem-↑ w) (sem-↑ v) ⟩
  (pI ∷ sem w) +ₚ (pI ∷ sem v) ≡⟨ Eq.cong (_∷ (sem w +ₚ sem v)) (+₁-identityˡ pI) ⟩
  pI ∷ (sem w +ₚ sem v)        ∎
  where open Eq.≡-Reasoning

-- Powers of the two generators on the bottom wire.
sem-X^ : ∀ {n} k → sem (X {n} ^ k) ≡ (mult k , ₀) ∷ pIₙ
sem-X^ ₀      = Eq.refl
sem-X^ ₁      = Eq.cong (λ z → (z , ₀) ∷ pIₙ) (Eq.sym (+-identityʳ ₁))
sem-X^ (₂₊ k) = begin
  pX₀ +ₚ sem (X ^ ₁₊ k)
    ≡⟨ Eq.cong (pX₀ +ₚ_) (sem-X^ (₁₊ k)) ⟩
  ((₁ , ₀) +₁ (mult (₁₊ k) , ₀)) ∷ (pIₙ +ₚ pIₙ)
    ≡⟨ Eq.cong₂ _∷_ (Eq.cong ((₁ + mult (₁₊ k)) ,_) (+-identityˡ ₀))
                    (+ₚ-identityˡ pIₙ) ⟩
  (mult (₂₊ k) , ₀) ∷ pIₙ ∎
  where open Eq.≡-Reasoning

sem-Z^ : ∀ {n} k → sem (Z {n} ^ k) ≡ (₀ , mult k) ∷ pIₙ
sem-Z^ ₀      = Eq.refl
sem-Z^ ₁      = Eq.cong (λ z → (₀ , z) ∷ pIₙ) (Eq.sym (+-identityʳ ₁))
sem-Z^ (₂₊ k) = begin
  pZ₀ +ₚ sem (Z ^ ₁₊ k)
    ≡⟨ Eq.cong (pZ₀ +ₚ_) (sem-Z^ (₁₊ k)) ⟩
  ((₀ , ₁) +₁ (₀ , mult (₁₊ k))) ∷ (pIₙ +ₚ pIₙ)
    ≡⟨ Eq.cong₂ _∷_ (Eq.cong (_, (₁ + mult (₁₊ k))) (+-identityˡ ₀))
                    (+ₚ-identityˡ pIₙ) ⟩
  (₀ , mult (₂₊ k)) ∷ pIₙ ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Soundness

sound-ax : ∀ {n} {w v : Word (Gen n)} → n QRel, w === v → sem w ≡ sem v
sound-ax {₁₊ n} order-X =
  Eq.trans (sem-X^ p) (Eq.cong (λ z → (z , ₀) ∷ pIₙ) mult-p)
sound-ax {₁₊ n} order-Z =
  Eq.trans (sem-Z^ p) (Eq.cong (λ z → (₀ , z) ∷ pIₙ) mult-p)
sound-ax {₁₊ n} comm-Z-X          = +ₚ-comm pZ₀ pX₀
sound-ax {₂₊ n} (comm₁ X-gate g)  = +ₚ-comm (pI ∷ ⟦ g ⟧₀) pX₀
sound-ax {₂₊ n} (comm₁ Z-gate g)  = +ₚ-comm (pI ∷ ⟦ g ⟧₀) pZ₀
sound-ax {₁₊ n} (cong↑ {w = w} {v} ax) =
  Eq.trans (sem-↑ w) (Eq.trans (Eq.cong (pI ∷_) (sound-ax ax)) (Eq.sym (sem-↑ v)))

------------------------------------------------------------------------
-- The normal form
--
-- X^a Z^b on each wire, read off the exponent vector.

inv-nf : Pauli n → Word (Gen n)
inv-nf {₀}    []             = ε
inv-nf {₁₊ n} ((a , b) ∷ ps) = X ^ toℕ a • Z ^ toℕ b • (inv-nf ps) ↑

-- The section law: reading a vector back out of its normal form gives
-- the vector.
sem-inv : ∀ (P : Pauli n) → sem (inv-nf P) ≡ P
sem-inv {₀}    []             = Eq.refl
sem-inv {₁₊ n} ((a , b) ∷ ps) = begin
  sem (X ^ toℕ a) +ₚ (sem (Z ^ toℕ b) +ₚ sem ((inv-nf ps) ↑))
    ≡⟨ Eq.cong₂ _+ₚ_ (sem-X^ (toℕ a))
        (Eq.cong₂ _+ₚ_ (sem-Z^ (toℕ b))
          (Eq.trans (sem-↑ (inv-nf ps)) (Eq.cong (pI ∷_) (sem-inv ps)))) ⟩
  ((mult (toℕ a) , ₀) ∷ pIₙ) +ₚ (((₀ , mult (toℕ b)) ∷ pIₙ) +ₚ (pI ∷ ps))
    ≡⟨ Eq.cong₂ _∷_ head-eq tail-eq ⟩
  (a , b) ∷ ps ∎
  where
  open Eq.≡-Reasoning
  head-eq : (mult (toℕ a) , ₀) +₁ ((₀ , mult (toℕ b)) +₁ pI) ≡ (a , b)
  head-eq = begin
    (mult (toℕ a) , ₀) +₁ ((₀ , mult (toℕ b)) +₁ pI)
      ≡⟨ Eq.cong ((mult (toℕ a) , ₀) +₁_) (+₁-identityʳ (₀ , mult (toℕ b))) ⟩
    (mult (toℕ a) , ₀) +₁ (₀ , mult (toℕ b))
      ≡⟨ Eq.cong₂ _,_ (+-identityʳ (mult (toℕ a))) (+-identityˡ (mult (toℕ b))) ⟩
    (mult (toℕ a) , mult (toℕ b))
      ≡⟨ Eq.cong₂ _,_ (mult-toℕ a) (mult-toℕ b) ⟩
    (a , b) ∎
  tail-eq : pIₙ +ₚ (pIₙ +ₚ ps) ≡ ps
  tail-eq = Eq.trans (+ₚ-identityˡ (pIₙ +ₚ ps)) (+ₚ-identityˡ ps)

------------------------------------------------------------------------
-- The Pauli presentation is commutative
--
-- Every pair of generators commutes — X with Z by comm-Z-X, either with
-- anything on a higher wire by comm-X / comm-Z, and two higher-wire
-- generators by cong↑ — so every pair of words does.

gen-comm : ∀ {n} (x y : Gen n) →
           let open PB (n QRel,_===_) in [ x ]ʷ • [ y ]ʷ ≈ [ y ]ʷ • [ x ]ʷ
gen-comm {₁₊ n} X-gen  X-gen  = PB.refl
gen-comm {₁₊ n} X-gen  Z-gen  = PB.sym (PB.axiom comm-Z-X)
gen-comm {₁₊ n} Z-gen  X-gen  = PB.axiom comm-Z-X
gen-comm {₁₊ n} Z-gen  Z-gen  = PB.refl
gen-comm {₂₊ n} X-gen  (y ↥)  = PB.sym (PB.axiom comm-X)
gen-comm {₂₊ n} (x ↥)  X-gen  = PB.axiom comm-X
gen-comm {₂₊ n} Z-gen  (y ↥)  = PB.sym (PB.axiom comm-Z)
gen-comm {₂₊ n} (x ↥)  Z-gen  = PB.axiom comm-Z
gen-comm {₂₊ n} (x ↥)  (y ↥)  =
  lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) (gen-comm x y)

word-comm : ∀ {n} (u v : Word (Gen n)) →
            let open PB (n QRel,_===_) in u • v ≈ v • u
word-comm {n} [ x ]ʷ [ y ]ʷ = gen-comm x y
word-comm {n} [ x ]ʷ ε      = PB.trans PB.right-unit (PB.sym PB.left-unit)
word-comm {n} [ x ]ʷ (v • w) = begin
  [ x ]ʷ • (v • w)  ≈⟨ sym assoc ⟩
  ([ x ]ʷ • v) • w  ≈⟨ cleft (word-comm [ x ]ʷ v) ⟩
  (v • [ x ]ʷ) • w  ≈⟨ assoc ⟩
  v • ([ x ]ʷ • w)  ≈⟨ cright (word-comm [ x ]ʷ w) ⟩
  v • (w • [ x ]ʷ)  ≈⟨ sym assoc ⟩
  (v • w) • [ x ]ʷ  ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid
word-comm {n} ε v = PB.trans PB.left-unit (PB.sym PB.right-unit)
word-comm {n} (u • u') v = begin
  (u • u') • v  ≈⟨ assoc ⟩
  u • (u' • v)  ≈⟨ cright (word-comm u' v) ⟩
  u • (v • u')  ≈⟨ sym assoc ⟩
  (u • v) • u'  ≈⟨ cleft (word-comm u v) ⟩
  (v • u) • u'  ≈⟨ assoc ⟩
  v • (u • u')  ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid

-- The interchange law of a commutative monoid.
interchange : ∀ {n} (u v u' v' : Word (Gen n)) →
              let open PB (n QRel,_===_) in
              (u • v) • (u' • v') ≈ (u • u') • (v • v')
interchange {n} u v u' v' = begin
  (u • v) • (u' • v')  ≈⟨ assoc ⟩
  u • (v • (u' • v'))  ≈⟨ cright (sym assoc) ⟩
  u • ((v • u') • v')  ≈⟨ cright (cleft (word-comm v u')) ⟩
  u • ((u' • v) • v')  ≈⟨ cright assoc ⟩
  u • (u' • (v • v'))  ≈⟨ sym assoc ⟩
  (u • u') • (v • v')  ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid

------------------------------------------------------------------------
-- Exponents may be taken modulo p

private
  module _ {n : ℕ} where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid

    -- The generic argument: a generator of order p has powers depending
    -- only on the exponent mod p.
    pow-mod : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ k → w ^ k ≈ w ^ (k % p)
    pow-mod w ord k = begin
      w ^ k                             ≡⟨ Eq.cong (w ^_) (m≡m%n+[m/n]*n k p) ⟩
      w ^ (k % p Nat.+ k / p Nat.* p)   ≈⟨ ^-+ w (k % p) (k / p Nat.* p) ⟩
      w ^ (k % p) • w ^ (k / p Nat.* p) ≈⟨ cright (refl' (Eq.cong (w ^_) (NP.*-comm (k / p) p))) ⟩
      w ^ (k % p) • w ^ (p Nat.* (k / p)) ≈⟨ cright (sym (^^ w p (k / p))) ⟩
      w ^ (k % p) • (w ^ p) ^ (k / p)   ≈⟨ cright (^-cong (w ^ p) ε (k / p) ord) ⟩
      w ^ (k % p) • ε ^ (k / p)         ≈⟨ cright (ε^k=ε (k / p)) ⟩
      w ^ (k % p) • ε                   ≈⟨ right-unit ⟩
      w ^ (k % p)                       ∎

    -- Adding exponents on the bottom wire.
    pow-add : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ (a c : ℤ ₚ) →
              w ^ toℕ a • w ^ toℕ c ≈ w ^ toℕ (a + c)
    pow-add w ord a c = begin
      w ^ toℕ a • w ^ toℕ c         ≈⟨ sym (^-+ w (toℕ a) (toℕ c)) ⟩
      w ^ (toℕ a Nat.+ toℕ c)       ≈⟨ pow-mod w ord (toℕ a Nat.+ toℕ c) ⟩
      w ^ ((toℕ a Nat.+ toℕ c) % p) ≡⟨ Eq.cong (w ^_) (Eq.sym (toℕ-+ a c)) ⟩
      w ^ toℕ (a + c)               ∎

    X-add : ∀ (a c : ℤ ₚ) → X {n} ^ toℕ a • X ^ toℕ c ≈ X ^ toℕ (a + c)
    X-add = pow-add X (axiom order-X)

    Z-add : ∀ (a c : ℤ ₚ) → Z {n} ^ toℕ a • Z ^ toℕ c ≈ Z ^ toℕ (a + c)
    Z-add = pow-add Z (axiom order-Z)

------------------------------------------------------------------------
-- The retraction
--
-- inv-nf turns sums into products, so normalising a word returns it.

inv-hom : ∀ {n} (P Q : Pauli n) →
          let open PB (n QRel,_===_) in
          inv-nf (P +ₚ Q) ≈ inv-nf P • inv-nf Q
inv-hom {₀}    []             []             = PB.sym PB.left-unit
inv-hom {₁₊ n} ((a , b) ∷ ps) ((c , d) ∷ qs) = begin
  X ^ toℕ (a + c) • (Z ^ toℕ (b + d) • (inv-nf (ps +ₚ qs)) ↑)
    ≈⟨ cong (sym (X-add a c))
            (cong (sym (Z-add b d))
                  (lemma-cong↑ _ _ (inv-hom ps qs))) ⟩
  (X ^ toℕ a • X ^ toℕ c)
    • ((Z ^ toℕ b • Z ^ toℕ d) • ((inv-nf ps) ↑ • (inv-nf qs) ↑))
    ≈⟨ cright (sym (interchange (Z ^ toℕ b) ((inv-nf ps) ↑)
                                (Z ^ toℕ d) ((inv-nf qs) ↑))) ⟩
  (X ^ toℕ a • X ^ toℕ c)
    • ((Z ^ toℕ b • (inv-nf ps) ↑) • (Z ^ toℕ d • (inv-nf qs) ↑))
    ≈⟨ sym (interchange (X ^ toℕ a) (Z ^ toℕ b • (inv-nf ps) ↑)
                        (X ^ toℕ c) (Z ^ toℕ d • (inv-nf qs) ↑)) ⟩
  (X ^ toℕ a • (Z ^ toℕ b • (inv-nf ps) ↑))
    • (X ^ toℕ c • (Z ^ toℕ d • (inv-nf qs) ↑)) ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

inv-ε : ∀ {n} → let open PB (n QRel,_===_) in inv-nf (pIₙ {n}) ≈ ε
inv-ε {₀}    = PB.refl
inv-ε {₁₊ n} = begin
  ε • (ε • (inv-nf pIₙ) ↑)  ≈⟨ left-unit ⟩
  ε • (inv-nf pIₙ) ↑        ≈⟨ left-unit ⟩
  (inv-nf pIₙ) ↑            ≈⟨ lemma-cong↑ _ _ (inv-ε {n}) ⟩
  ε ↑                       ≈⟨ refl ⟩
  ε                         ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

inv-gen : ∀ {n} (x : Gen n) →
          let open PB (n QRel,_===_) in inv-nf ⟦ x ⟧₀ ≈ [ x ]ʷ
inv-gen {₁₊ n} X-gen = begin
  X ^ 1 • (ε • (inv-nf pIₙ) ↑)  ≈⟨ cright left-unit ⟩
  X • (inv-nf pIₙ) ↑            ≈⟨ cright (lemma-cong↑ _ _ (inv-ε {n})) ⟩
  X • ε                         ≈⟨ right-unit ⟩
  X                             ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
inv-gen {₁₊ n} Z-gen = begin
  ε • (Z ^ 1 • (inv-nf pIₙ) ↑)  ≈⟨ left-unit ⟩
  Z • (inv-nf pIₙ) ↑            ≈⟨ cright (lemma-cong↑ _ _ (inv-ε {n})) ⟩
  Z • ε                         ≈⟨ right-unit ⟩
  Z                             ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
inv-gen {₁₊ n} (g ↥) = begin
  ε • (ε • (inv-nf ⟦ g ⟧₀) ↑)  ≈⟨ left-unit ⟩
  ε • (inv-nf ⟦ g ⟧₀) ↑        ≈⟨ left-unit ⟩
  (inv-nf ⟦ g ⟧₀) ↑            ≈⟨ lemma-cong↑ _ _ (inv-gen g) ⟩
  [ g ]ʷ ↑                     ≈⟨ refl ⟩
  [ g ↥ ]ʷ                     ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

retract : ∀ {n} (w : Word (Gen n)) →
          let open PB (n QRel,_===_) in inv-nf (sem w) ≈ w
retract {n} [ x ]ʷ = inv-gen x
retract {n} ε      = inv-ε
retract {n} (u • v) = begin
  inv-nf (sem u +ₚ sem v)     ≈⟨ inv-hom (sem u) (sem v) ⟩
  inv-nf (sem u) • inv-nf (sem v) ≈⟨ cong (retract u) (retract v) ⟩
  u • v                       ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid

------------------------------------------------------------------------
-- The presentation

module Build (n : ℕ) where

  private
    Γ = n QRel,_===_
    module SP = Normalization.StarPresentation Γ (Eq.setoid (Pauli n))
    module GS = SP.GroupSem (+ₚ-group n) ⟦_⟧₀
    module NF = SNF Γ (Eq.setoid (Pauli n))

    -- The extension of ⟦_⟧₀ along the Pauli group is `sem`.
    sem-agrees : ∀ (w : Word (Gen n)) → GS.⟦ w ⟧ ≡ sem w
    sem-agrees [ x ]ʷ  = Eq.refl
    sem-agrees ε       = Eq.refl
    sem-agrees (u • v) = Eq.cong₂ _+ₚ_ (sem-agrees u) (sem-agrees v)

    nfp : NF.NormalForm
    nfp = record
      { rightInverse = record
          { to        = sem
          ; from      = inv-nf
          ; to-cong   = sound
          ; from-cong = λ { Eq.refl → PB.refl }
          ; inverseʳ  = λ { {w} Eq.refl → retract w }
          }
      }
      where
      sound : ∀ {w v} → PB._≈_ Γ w v → sem w ≡ sem v
      sound PB.refl            = Eq.refl
      sound (PB.sym eq)        = Eq.sym (sound eq)
      sound (PB.trans eq eq')  = Eq.trans (sound eq) (sound eq')
      sound (PB.cong eq eq')   = Eq.cong₂ _+ₚ_ (sound eq) (sound eq')
      sound (PB.assoc {w} {v} {u}) = +ₚ-assoc (sem w) (sem v) (sem u)
      sound (PB.left-unit {v})     = +ₚ-identityˡ (sem v)
      sound (PB.right-unit {v})    = +ₚ-identityʳ (sem v)
      sound (PB.axiom ax)      = sound-ax ax

    unfp : NF.UniqueNormalForm (Group.setoid (+ₚ-group n)) GS.⟦_⟧ nfp
    unfp = record
      { unique = λ { {P} {Q} eq →
          Eq.trans (Eq.sym (sem-inv P))
            (Eq.trans (Eq.trans (Eq.sym (sem-agrees (inv-nf P)))
                        (Eq.trans eq (sem-agrees (inv-nf Q))))
              (sem-inv Q)) }
      }

    sound-⟦⟧ : ∀ {w v} → Γ w v → GS.⟦ w ⟧ ≡ GS.⟦ v ⟧
    sound-⟦⟧ {w} {v} ax =
      Eq.trans (sem-agrees w) (Eq.trans (sound-ax ax) (Eq.sym (sem-agrees v)))

    module GSP = GS.GetSubPresentation
                   sound-⟦⟧ XZ-GroupLike.grouplike nfp unfp

    -- The congruence of the extension (GroupSem re-exports only the
    -- subpresentation, so take it from Extend directly).
    open import Normalization.StarInterp Γ using (module Extend)
    module E  = Extend (Group.monoid (+ₚ-group n)) ⟦_⟧₀
    module EC = E.Cong sound-⟦⟧

  subpres : Γ IsSubPresentationOf (+ₚ-group n)
  subpres = GSP.groupSubPres

  -- ⟦_⟧ is onto: every Pauli is the reading of its own normal form.
  surj : ∀ (P : Pauli n) → GS.⟦ inv-nf P ⟧ ≡ P
  surj P = Eq.trans (sem-agrees (inv-nf P)) (sem-inv P)

  presentation : Γ IsPresentationOf (+ₚ-group n)
  presentation =
    isPresentationOf subpres
      (λ P → inv-nf P , λ eq → Eq.trans (EC.fʷ-cong eq) (surj P))

  private
    module ISO = GroupMorphisms.IsGroupIsomorphism
                   (_IsPresentationOf_.iso presentation)

  -- Soundness and completeness, in the form the conjugation action
  -- needs: two words are equal in the presentation exactly when they
  -- read as the same Pauli.
  sound : ∀ {w v : Word (Gen n)} → PB._≈_ Γ w v → sem w ≡ sem v
  sound {w} {v} eq =
    Eq.trans (Eq.sym (sem-agrees w)) (Eq.trans (EC.fʷ-cong eq) (sem-agrees v))

  complete : ∀ {w v : Word (Gen n)} → sem w ≡ sem v → PB._≈_ Γ w v
  complete {w} {v} eq =
    ISO.injective
      (Eq.trans (sem-agrees w) (Eq.trans eq (Eq.sym (sem-agrees v))))

------------------------------------------------------------------------
-- The Pauli rules present (ℤ/pℤ × ℤ/pℤ)ⁿ

presentation : ∀ {n} → (n QRel,_===_) IsPresentationOf (+ₚ-group n)
presentation {n} = Build.presentation n
