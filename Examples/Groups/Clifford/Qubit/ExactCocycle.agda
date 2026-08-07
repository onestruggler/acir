------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group,
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ Clifford n ─→ 1,
--
-- reduced to one missing function.
--
-- ForStdlib.Algebra.Construct.CentralExtension builds this extension from
-- a normalised 2-cocycle c : Clifford n → Clifford n → ℤ/8.  A cocycle is
-- not something one writes down by a formula: it is the multiplication
-- defect of a chosen set-theoretic section of Exact n ↠ Clifford n, so
-- writing one means choosing, for every Clifford operator taken modulo
-- the global scalar, a preferred exact lift.  The datum behind that
-- choice is the ω-exponent of a word,
--
--     Ω : Word (Gen n) → ℤ/8,
--
-- and this module shows that Ω is the *whole* of what is missing: from Ω
-- and the five laws below, `cocycleOf` derives the cocycle — normalisation
-- and the cocycle identity included — and `Exact` derives the extension.
--
-- Ω is not ≈ᶜ-invariant, and cannot be: `action-blind` at the end proves
-- that any ≈ᶜ-invariant Ω sends ω to ₀, hence fails the specification
-- `Pins-ω`.  That is the precise sense in which the P4-action discards the
-- scalar, and the reason Ω must come from a faithful model of the exact
-- Clifford group rather than from `cact`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.ExactCocycle where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_)

open import Notations
open import Word.Base using (Word ; ε ; _•_)
open import Zp.ModularArithmetic
  using ( ℤ ; _+_ ; -_ ; +-assoc ; +-comm ; +-identityˡ ; +-identityʳ
        ; +-inverseʳ ; +-0-abelianGroup)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.CentralExtension
  using (Cocycle ; centralExtension)

open import Examples.Groups.Clifford.Qubit.CliffordGroup
  using (p-2 ; p-prime ; _≈ᶜ_ ; Clifford-group)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime using (ω)
open import Examples.Groups.Clifford.Qubit.Selinger.Action using (cact-ω)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The scalars ⟨ω⟩ ≅ ℤ/8
--
-- Written additively in the exponent of ω.  (+-0-abelianGroup m has
-- carrier ℤ (₂₊ m), so order 8 is m = 6; scalar-order-8 pins it.)

Scalar : Set
Scalar = ℤ 8

Scalar-abelian : AbelianGroup 0ℓ 0ℓ
Scalar-abelian = +-0-abelianGroup 6

Scalar-group : Group 0ℓ 0ℓ
Scalar-group = AbelianGroup.group Scalar-abelian

private
  scalar-order-8 : Group.Carrier Scalar-group ≡ Scalar
  scalar-order-8 = Eq.refl

------------------------------------------------------------------------
-- Additive algebra in ℤ/8
--
-- Everything below is abelian-group bookkeeping; nothing about ℤ/8 in
-- particular is used beyond the group laws.

private

  swap-add : (s x y : Scalar) → (s + x) + y ≡ (s + y) + x
  swap-add s x y =
    Eq.trans (+-assoc s x y)
      (Eq.trans (Eq.cong (s +_) (+-comm x y)) (Eq.sym (+-assoc s y x)))

  -- Swap the outer two of three summands.
  swap-outer : (x y z : Scalar) → (x + y) + z ≡ (z + y) + x
  swap-outer x y z = begin
    (x + y) + z   ≡⟨ swap-add x y z ⟩
    (x + z) + y   ≡⟨ Eq.cong (_+ y) (+-comm x z) ⟩
    (z + x) + y   ≡⟨ swap-add z x y ⟩
    (z + y) + x   ∎
    where open Eq.≡-Reasoning

  cancelʳ : (x y z : Scalar) → x + z ≡ y + z → x ≡ y
  cancelʳ x y z eq = begin
    x                 ≡⟨ Eq.sym (+-identityʳ x) ⟩
    x + ₀             ≡⟨ Eq.cong (x +_) (Eq.sym (+-inverseʳ z)) ⟩
    x + (z + - z)     ≡⟨ Eq.sym (+-assoc x z (- z)) ⟩
    (x + z) + - z     ≡⟨ Eq.cong (_+ - z) eq ⟩
    (y + z) + - z     ≡⟨ +-assoc y z (- z) ⟩
    y + (z + - z)     ≡⟨ Eq.cong (y +_) (+-inverseʳ z) ⟩
    y + ₀             ≡⟨ +-identityʳ y ⟩
    y                 ∎
    where open Eq.≡-Reasoning

  cancelˡ : (z x y : Scalar) → z + x ≡ z + y → x ≡ y
  cancelˡ z x y eq =
    cancelʳ x y z (Eq.trans (+-comm x z) (Eq.trans eq (+-comm z y)))

  -- y + (x - y) ≡ x: what makes the derived defect fit back together.
  recover : (x y : Scalar) → y + (x + - y) ≡ x
  recover x y = begin
    y + (x + - y)   ≡⟨ Eq.sym (+-assoc y x (- y)) ⟩
    (y + x) + - y   ≡⟨ Eq.cong (_+ - y) (+-comm y x) ⟩
    (x + y) + - y   ≡⟨ +-assoc x y (- y) ⟩
    x + (y + - y)   ≡⟨ Eq.cong (x +_) (+-inverseʳ y) ⟩
    x + ₀           ≡⟨ +-identityʳ x ⟩
    x               ∎
    where open Eq.≡-Reasoning

  -- The two rearrangements the cocycle identity needs (the additive
  -- twins of CentralExtension's shuffleˡ / shuffleʳ).
  shuffleˡ : (p q u r v : Scalar) →
             (((p + q) + u) + r) + v ≡ ((p + q) + r) + (u + v)
  shuffleˡ p q u r v = begin
    (((p + q) + u) + r) + v   ≡⟨ Eq.cong (_+ v) (swap-add (p + q) u r) ⟩
    (((p + q) + r) + u) + v   ≡⟨ +-assoc ((p + q) + r) u v ⟩
    ((p + q) + r) + (u + v)   ∎
    where open Eq.≡-Reasoning

  shuffleʳ : (p q r u v : Scalar) →
             (p + ((q + r) + u)) + v ≡ ((p + q) + r) + (u + v)
  shuffleʳ p q r u v = begin
    (p + ((q + r) + u)) + v   ≡⟨ Eq.cong (_+ v) (Eq.sym (+-assoc p (q + r) u)) ⟩
    ((p + (q + r)) + u) + v   ≡⟨ Eq.cong (λ □ → (□ + u) + v) (Eq.sym (+-assoc p q r)) ⟩
    (((p + q) + r) + u) + v   ≡⟨ +-assoc ((p + q) + r) u v ⟩
    ((p + q) + r) + (u + v)   ∎
    where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The missing datum
--
-- Ω w is the power of ω that the word w carries, measured against a
-- chosen exact lift of each element of Clifford n.  The laws say: the
-- chosen lift of the identity is the identity (Ω-ε), and Ω is blind to
-- the monoid laws of words (Ω-εˡ, Ω-εʳ, Ω-assoc) — both because a word
-- and its rebracketing denote the *same* exact operator.  The two shift
-- laws say that the multiplication defect
--
--     Ω (w • v) − Ω w − Ω v
--
-- depends only on the ≈ᶜ-classes of w and v, which is what lets it be a
-- cocycle on Clifford n even though Ω itself is not ≈ᶜ-invariant.

record ScalarExponent (n : ℕ) : Set where
  field
    Ω        : Word (Gen n) → Scalar
    Ω-ε      : Ω ε ≡ ₀
    Ω-εˡ     : (w : Word (Gen n)) → Ω (ε • w) ≡ Ω w
    Ω-εʳ     : (w : Word (Gen n)) → Ω (w • ε) ≡ Ω w
    Ω-assoc  : (w v u : Word (Gen n)) → Ω ((w • v) • u) ≡ Ω (w • (v • u))
    Ω-shiftˡ : {w w' : Word (Gen n)} → w ≈ᶜ w' →
               (v : Word (Gen n)) → Ω (w • v) + Ω w' ≡ Ω (w' • v) + Ω w
    Ω-shiftʳ : {v v' : Word (Gen n)} → v ≈ᶜ v' →
               (w : Word (Gen n)) → Ω (w • v) + Ω v' ≡ Ω (w • v') + Ω v

  ----------------------------------------------------------------------
  -- The cocycle it determines

  -- The defect incurred when the chosen lifts of w and v are multiplied.
  c : Word (Gen n) → Word (Gen n) → Scalar
  c w v = Ω (w • v) + - (Ω w + Ω v)

  -- Its defining property, with the subtraction cleared away.  Every
  -- proof below uses only this, never the definition of c.
  Ω-• : (w v : Word (Gen n)) → Ω (w • v) ≡ (Ω w + Ω v) + c w v
  Ω-• w v = Eq.sym (recover (Ω (w • v)) (Ω w + Ω v))

  -- Normalisation: the unit lifts to the unit.
  c-εˡ : (x : Word (Gen n)) → c ε x ≡ ₀
  c-εˡ x = cancelˡ (Ω ε + Ω x) (c ε x) ₀ (begin
    (Ω ε + Ω x) + c ε x   ≡⟨ Eq.sym (Ω-• ε x) ⟩
    Ω (ε • x)             ≡⟨ Ω-εˡ x ⟩
    Ω x                   ≡⟨ Eq.sym (+-identityˡ (Ω x)) ⟩
    ₀ + Ω x               ≡⟨ Eq.cong (_+ Ω x) (Eq.sym Ω-ε) ⟩
    Ω ε + Ω x             ≡⟨ Eq.sym (+-identityʳ (Ω ε + Ω x)) ⟩
    (Ω ε + Ω x) + ₀       ∎)
    where open Eq.≡-Reasoning

  c-εʳ : (x : Word (Gen n)) → c x ε ≡ ₀
  c-εʳ x = cancelˡ (Ω x + Ω ε) (c x ε) ₀ (begin
    (Ω x + Ω ε) + c x ε   ≡⟨ Eq.sym (Ω-• x ε) ⟩
    Ω (x • ε)             ≡⟨ Ω-εʳ x ⟩
    Ω x                   ≡⟨ Eq.sym (+-identityʳ (Ω x)) ⟩
    Ω x + ₀               ≡⟨ Eq.cong (Ω x +_) (Eq.sym Ω-ε) ⟩
    Ω x + Ω ε             ≡⟨ Eq.sym (+-identityʳ (Ω x + Ω ε)) ⟩
    (Ω x + Ω ε) + ₀       ∎)
    where open Eq.≡-Reasoning

  -- The defect only sees the ≈ᶜ-classes: one argument at a time.
  c-congˡ : {w w' : Word (Gen n)} → w ≈ᶜ w' →
            (v : Word (Gen n)) → c w v ≡ c w' v
  c-congˡ {w} {w'} e v = cancelˡ pre (c w v) (c w' v) (begin
    pre + c w v
      ≡⟨ Eq.sym (swap-add (Ω w + Ω v) (c w v) (Ω w')) ⟩
    ((Ω w + Ω v) + c w v) + Ω w'
      ≡⟨ Eq.cong (_+ Ω w') (Eq.sym (Ω-• w v)) ⟩
    Ω (w • v) + Ω w'
      ≡⟨ Ω-shiftˡ e v ⟩
    Ω (w' • v) + Ω w
      ≡⟨ Eq.cong (_+ Ω w) (Ω-• w' v) ⟩
    ((Ω w' + Ω v) + c w' v) + Ω w
      ≡⟨ swap-add (Ω w' + Ω v) (c w' v) (Ω w) ⟩
    ((Ω w' + Ω v) + Ω w) + c w' v
      ≡⟨ Eq.cong (_+ c w' v) (Eq.sym (swap-outer (Ω w) (Ω v) (Ω w'))) ⟩
    pre + c w' v
      ∎)
    where
    open Eq.≡-Reasoning
    pre = (Ω w + Ω v) + Ω w'

  c-congʳ : {v v' : Word (Gen n)} → v ≈ᶜ v' →
            (w : Word (Gen n)) → c w v ≡ c w v'
  c-congʳ {v} {v'} e w = cancelˡ pre (c w v) (c w v') (begin
    pre + c w v
      ≡⟨ Eq.sym (swap-add (Ω w + Ω v) (c w v) (Ω v')) ⟩
    ((Ω w + Ω v) + c w v) + Ω v'
      ≡⟨ Eq.cong (_+ Ω v') (Eq.sym (Ω-• w v)) ⟩
    Ω (w • v) + Ω v'
      ≡⟨ Ω-shiftʳ e w ⟩
    Ω (w • v') + Ω v
      ≡⟨ Eq.cong (_+ Ω v) (Ω-• w v') ⟩
    ((Ω w + Ω v') + c w v') + Ω v
      ≡⟨ swap-add (Ω w + Ω v') (c w v') (Ω v) ⟩
    ((Ω w + Ω v') + Ω v) + c w v'
      ≡⟨ Eq.cong (_+ c w v') (Eq.sym (swap-add (Ω w) (Ω v) (Ω v'))) ⟩
    pre + c w v'
      ∎)
    where
    open Eq.≡-Reasoning
    pre = (Ω w + Ω v) + Ω v'

  c-cong : {x x' y y' : Word (Gen n)} → x ≈ᶜ x' → y ≈ᶜ y' → c x y ≡ c x' y'
  c-cong {x' = x'} {y = y} ex ey = Eq.trans (c-congˡ ex y) (c-congʳ ey x')

  -- The cocycle identity.  Both sides of the associativity of Ω, once the
  -- Ω-summands are shuffled out of the way, are exactly the two halves.
  cocycle-id : (x y z : Word (Gen n)) →
               c x y + c (x • y) z ≡ c y z + c x (y • z)
  cocycle-id x y z =
    cancelˡ ((Ω x + Ω y) + Ω z) (c x y + c (x • y) z) (c y z + c x (y • z))
      (begin
        ((Ω x + Ω y) + Ω z) + (c x y + c (x • y) z)
          ≡⟨ Eq.sym (shuffleˡ (Ω x) (Ω y) (c x y) (Ω z) (c (x • y) z)) ⟩
        (((Ω x + Ω y) + c x y) + Ω z) + c (x • y) z
          ≡⟨ Eq.cong (λ □ → (□ + Ω z) + c (x • y) z) (Eq.sym (Ω-• x y)) ⟩
        (Ω (x • y) + Ω z) + c (x • y) z
          ≡⟨ Eq.sym (Ω-• (x • y) z) ⟩
        Ω ((x • y) • z)
          ≡⟨ Ω-assoc x y z ⟩
        Ω (x • (y • z))
          ≡⟨ Ω-• x (y • z) ⟩
        (Ω x + Ω (y • z)) + c x (y • z)
          ≡⟨ Eq.cong (λ □ → (Ω x + □) + c x (y • z)) (Ω-• y z) ⟩
        (Ω x + ((Ω y + Ω z) + c y z)) + c x (y • z)
          ≡⟨ shuffleʳ (Ω x) (Ω y) (Ω z) (c y z) (c x (y • z)) ⟩
        ((Ω x + Ω y) + Ω z) + (c y z + c x (y • z))
          ∎)
    where open Eq.≡-Reasoning

  cocycleOf : Cocycle Scalar-abelian (Clifford-group n)
  cocycleOf = record
    { c       = c
    ; c-cong  = c-cong
    ; c-εˡ    = c-εˡ
    ; c-εʳ    = c-εʳ
    ; cocycle = cocycle-id
    }

------------------------------------------------------------------------
-- The scalar layer
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ Clifford n ─→ 1

Exact : ScalarExponent n → Extension Scalar-group (Clifford-group n)
Exact {n} σ =
  centralExtension Scalar-abelian (Clifford-group n)
                   (ScalarExponent.cocycleOf σ)

------------------------------------------------------------------------
-- The specification, and why the action cannot meet it
--
-- ω = (SH)³ must carry exponent 1, or the ⟨ω⟩ layer is not of order 8:
-- Exact n would be a proper quotient of the exact Clifford group.

Pins-ω : ScalarExponent (₁₊ n) → Set
Pins-ω {n} σ = ScalarExponent.Ω σ (ω {n}) ≡ ₁

-- Conjugation by a scalar is trivial (Selinger.Action.cact-ω), so ω and ε
-- are the same element of Clifford n.
ω≈ᶜε : ω {n} ≈ᶜ ε
ω≈ᶜε = cact-ω

-- Hence no ≈ᶜ-invariant Ω can pin the scalar: it must send ω to Ω ε = ₀.
-- Ω is exactly the datum `cact` discards, so it has to come from a
-- faithful model of the exact Clifford group — Selinger's exact normal
-- form (Qubit.Selinger.NormalForm, ExactNF n = NF n × Fin 8, uniqueness
-- still WIP) or matrices over ℤ[1/√2, i].
action-blind : (Ω : Word (Gen (₁₊ n)) → Scalar) →
               ({w v : Word (Gen (₁₊ n))} → w ≈ᶜ v → Ω w ≡ Ω v) →
               Ω ε ≡ ₀ → ¬ (Ω (ω {n}) ≡ ₁)
action-blind Ω Ω-inv Ω-ε pin
  with Eq.trans (Eq.sym pin) (Eq.trans (Ω-inv ω≈ᶜε) Ω-ε)
... | ()
