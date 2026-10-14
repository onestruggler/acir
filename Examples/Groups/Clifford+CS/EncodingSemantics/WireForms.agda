------------------------------------------------------------------------
-- Presentations of groups
--
-- The operators of the gates at a wire, as functions of bitstrings
--
-- A generator is a gate placed on a wire (Encoding.view); its
-- operator, built in Interpretation by embedding a stored matrix and
-- shifting, is here written out on bitstrings: γ times the gate.  The
-- scalar is γ i times the identity; S on wire p is γ times the
-- diagonal with i where bit p is set; K on wire p is [[1 , 1] ,
-- [1 , −1]] on the bits at p when the other bits agree; CS on wires p
-- and p + 1 is γ times the diagonal with i where both bits are set.
-- These are the forms the encoding's products are compared with.
--
-- After Real-Clifford+CH.Auxiliary.WireForms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.WireForms (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Nat using (zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ᵍ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqᵇ ; eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ ; removeℕ)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diag using (diag)
open import Examples.Groups.Clifford+CS.Encoding m using (View ; scalar ; one ; two ; view)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- The entries of the gate matrices, and δ on bits

-- γ K = [[1 , 1] , [1 , −1]].
kval : Bool → Bool → 𝔽
kval true true = -1#
kval _    _    = 1#

δb-∷ : ∀ a b (x y : Bits k) → δb (a ∷ x) (b ∷ y) ≡ δ₁ a b * δb x y
δb-∷ true  true  x y = Eq.sym (*-identityˡ _)
δb-∷ false false x y = Eq.sym (*-identityˡ _)
δb-∷ true  false x y = Eq.sym (*-zeroˡ _)
δb-∷ false true  x y = Eq.sym (*-zeroˡ _)

δb-eqB : (x y : Bits k) → δb x y ≡ (if eqB x y then 1# else 0#)
δb-eqB []          []          = Eq.refl
δb-eqB (true ∷ x)  (true ∷ y)  = δb-eqB x y
δb-eqB (false ∷ x) (false ∷ y) = δb-eqB x y
δb-eqB (true ∷ x)  (false ∷ y) = Eq.refl
δb-eqB (false ∷ x) (true ∷ y)  = Eq.refl

-- γ i is γ times i.
γⅈ≡ : γⅈ ≡ γ * ⅈ
γⅈ≡ = Eq.refl

------------------------------------------------------------------------
-- The forms

-- The phase of S on wire p, and of CS on wires p and p + 1.
sph csph : ℕ → Bits k → 𝔽
sph p x  = if lookupℕ p x then ⅈ else 1#
csph p x = if lookupℕ p x ∧ lookupℕ (suc p) x then ⅈ else 1#

-- γ K on wire p: the K entry of the bits on p, when the other bits
-- agree.
kWire : ℕ → Op (suc k)
kWire p x y =
  if eqB (removeℕ p x) (removeℕ p y) then kval (lookupℕ p x) (lookupℕ p y) else 0#

form : View → Op (suc k)
form (scalar I-gate) = scal γⅈ
form (one p S-gate)  = γ · diag (sph p)
form (one p K-gate)  = kWire p
form (two p CS-gate) = γ · diag (csph p)

------------------------------------------------------------------------
-- Shifting a form up a wire

shift : View → View
shift (scalar h) = scalar h
shift (one p h)  = one (suc p) h
shift (two p h)  = two (suc p) h

view-↥ : (g : Gen k) → view (g ↥) ≡ shift (view g)
view-↥ g with view g
... | scalar h = Eq.refl
... | one p h  = Eq.refl
... | two p h  = Eq.refl

private
  -- The one-wire identity factor.
  δ₁-Id : ∀ a b → Idₒ {1} (a ∷ []) (b ∷ []) ≡ δ₁ a b
  δ₁-Id true  true  = Eq.refl
  δ₁-Id false false = Eq.refl
  δ₁-Id true  false = Eq.refl
  δ₁-Id false true  = Eq.refl

  ∧-if : ∀ a b (c′ : Bool) (u : 𝔽) →
         (if eqᵇ a b ∧ c′ then u else 0#) ≡ δ₁ a b * (if c′ then u else 0#)
  ∧-if true  true  c′ u = Eq.sym (*-identityˡ _)
  ∧-if false false c′ u = Eq.sym (*-identityˡ _)
  ∧-if true  false c′ u = Eq.sym (*-zeroˡ _)
  ∧-if false true  c′ u = Eq.sym (*-zeroˡ _)

  -- d * (s * (z * e)) regrouped as s * (z * (d * e)).
  shuffle : ∀ (d s z e : 𝔽) → d * (s * (z * e)) ≡ s * (z * (d * e))
  shuffle d s z e = begin
    d * (s * (z * e))   ≡⟨ *-comm d _ ⟩
    (s * (z * e)) * d   ≡⟨ *-assoc s (z * e) d ⟩
    s * ((z * e) * d)   ≡⟨ Eq.cong (s *_) (*-assoc z e d) ⟩
    s * (z * (e * d))   ≡⟨ Eq.cong (λ v → s * (z * v)) (*-comm e d) ⟩
    s * (z * (d * e))   ∎
    where open Eq.≡-Reasoning

kWire-suc : ∀ p a b (x y : Bits (suc k)) →
            kWire (suc p) (a ∷ x) (b ∷ y) ≡ δ₁ a b * kWire p x y
kWire-suc p a b (c ∷ x) (d ∷ y) = ∧-if a b _ _

-- A shifted form is the identity on the new wire times the form.
up-form : (v : View) → up {suc k} (form v) ≐ form (shift v)
up-form (scalar I-gate) = up-scal γⅈ
up-form (one p K-gate) (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* kWire p x y) (δ₁-Id a b)) (Eq.sym (kWire-suc p a b x y))
up-form (one p S-gate) (a ∷ x) (b ∷ y) = begin
  Idₒ (a ∷ []) (b ∷ []) * (γ * (sph p x * δb x y))
    ≡⟨ Eq.cong (_* (γ * (sph p x * δb x y))) (δ₁-Id a b) ⟩
  δ₁ a b * (γ * (sph p x * δb x y))
    ≡⟨ shuffle (δ₁ a b) γ (sph p x) (δb x y) ⟩
  γ * (sph p x * (δ₁ a b * δb x y))
    ≡⟨ Eq.cong (λ v → γ * (sph p x * v)) (Eq.sym (δb-∷ a b x y)) ⟩
  γ * (sph p x * δb (a ∷ x) (b ∷ y)) ∎
  where open Eq.≡-Reasoning
up-form (two p CS-gate) (a ∷ x) (b ∷ y) = begin
  Idₒ (a ∷ []) (b ∷ []) * (γ * (csph p x * δb x y))
    ≡⟨ Eq.cong (_* (γ * (csph p x * δb x y))) (δ₁-Id a b) ⟩
  δ₁ a b * (γ * (csph p x * δb x y))
    ≡⟨ shuffle (δ₁ a b) γ (csph p x) (δb x y) ⟩
  γ * (csph p x * (δ₁ a b * δb x y))
    ≡⟨ Eq.cong (λ v → γ * (csph p x * v)) (Eq.sym (δb-∷ a b x y)) ⟩
  γ * (csph p x * δb (a ∷ x) (b ∷ y)) ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The operator of a generator is the form of its view

private
  -- The entries of the stored gate matrices, case by case.
  kM-ix : ∀ a b → ix kM (a ∷ []) (b ∷ []) ≡ kval a b
  kM-ix true  true  = Eq.refl
  kM-ix true  false = Eq.refl
  kM-ix false true  = Eq.refl
  kM-ix false false = Eq.refl

  -- The form of K at wire 0.
  kWire-0 : ∀ a b (x y : Bits k) → kWire 0 (a ∷ x) (b ∷ y) ≡ kval a b * δb x y
  kWire-0 a b x y with eqB x y in eq
  ... | true  = Eq.sym (Eq.trans (Eq.cong (kval a b *_) (Eq.trans (δb-eqB x y) (Eq.cong (λ c → if c then 1# else 0#) eq))) (*-identityʳ _))
  ... | false = Eq.sym (Eq.trans (Eq.cong (kval a b *_) (Eq.trans (δb-eqB x y) (Eq.cong (λ c → if c then 1# else 0#) eq))) (*-zeroʳ _))

  -- The three shapes of a diagonal entry: the phase i, no phase, and
  -- off the diagonal.
  ent-i : ∀ (d : 𝔽) → γⅈ * d ≡ γ * (ⅈ * d)
  ent-i d = *-assoc γ ⅈ d

  ent-1 : ∀ (d : 𝔽) → γ * d ≡ γ * (1# * d)
  ent-1 d = Eq.cong (γ *_) (Eq.sym (*-identityˡ d))

  ent-0 : ∀ (p d : 𝔽) → 0# * d ≡ γ * (p * 0#)
  ent-0 p d = Eq.trans (*-zeroˡ d) (Eq.sym (Eq.trans (Eq.cong (γ *_) (*-zeroʳ p)) (*-zeroʳ γ)))

gen-form : (g : Gen (suc k)) → ⟦ g ⟧ᵍ ≐ form (view g)
gen-form (gate₀ I-gate) = ≐-refl (scal γⅈ)
gen-form K-gen (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* δb x y) (kM-ix a b)) (Eq.sym (kWire-0 a b x y))
gen-form S-gen (true ∷ x)  (true ∷ y)  = ent-i (δb x y)
gen-form S-gen (false ∷ x) (false ∷ y) = ent-1 (δb x y)
gen-form S-gen (true ∷ x)  (false ∷ y) = ent-0 ⅈ (δb x y)
gen-form S-gen (false ∷ x) (true ∷ y)  = ent-0 1# (δb x y)
gen-form CS-gen (true ∷ true ∷ x)   (true ∷ true ∷ y)   = ent-i (δb x y)
gen-form CS-gen (true ∷ false ∷ x)  (true ∷ false ∷ y)  = ent-1 (δb x y)
gen-form CS-gen (false ∷ true ∷ x)  (false ∷ true ∷ y)  = ent-1 (δb x y)
gen-form CS-gen (false ∷ false ∷ x) (false ∷ false ∷ y) = ent-1 (δb x y)
gen-form CS-gen (true ∷ true ∷ x)   (true ∷ false ∷ y)  = ent-0 ⅈ (δb x y)
gen-form CS-gen (true ∷ true ∷ x)   (false ∷ true ∷ y)  = ent-0 ⅈ (δb x y)
gen-form CS-gen (true ∷ true ∷ x)   (false ∷ false ∷ y) = ent-0 ⅈ (δb x y)
gen-form CS-gen (true ∷ false ∷ x)  (true ∷ true ∷ y)   = ent-0 1# (δb x y)
gen-form CS-gen (true ∷ false ∷ x)  (false ∷ true ∷ y)  = ent-0 1# (δb x y)
gen-form CS-gen (true ∷ false ∷ x)  (false ∷ false ∷ y) = ent-0 1# (δb x y)
gen-form CS-gen (false ∷ true ∷ x)  (true ∷ true ∷ y)   = ent-0 1# (δb x y)
gen-form CS-gen (false ∷ true ∷ x)  (true ∷ false ∷ y)  = ent-0 1# (δb x y)
gen-form CS-gen (false ∷ true ∷ x)  (false ∷ false ∷ y) = ent-0 1# (δb x y)
gen-form CS-gen (false ∷ false ∷ x) (true ∷ true ∷ y)   = ent-0 1# (δb x y)
gen-form CS-gen (false ∷ false ∷ x) (true ∷ false ∷ y)  = ent-0 1# (δb x y)
gen-form CS-gen (false ∷ false ∷ x) (false ∷ true ∷ y)  = ent-0 1# (δb x y)
gen-form {zero}   (gate₀ I-gate ↥) = up-scal γⅈ
gen-form {suc k′} (g ↥) =
  ≐-trans (up-cong (gen-form g))
    (≐-trans (up-form (view g))
      (Eq.subst (λ v → form (shift (view g)) ≐ form v) (Eq.sym (view-↥ g)) (≐-refl _)))
