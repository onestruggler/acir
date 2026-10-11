------------------------------------------------------------------------
-- Presentations of groups
--
-- The operators of the gates at a wire, as functions of bitstrings
--
-- A generator of Gen n is a gate placed on a wire (Encoding.view);
-- its operator, built in Interpretation by embedding a stored matrix
-- and shifting, is here written out on bitstrings: Z on wire p is
-- √2 times the diagonal sign of bit p, H on wire p is the Hadamard
-- entry of the bits on p when the other bits agree, and likewise for
-- CZ and CH on wires p and p + 1.  These are the forms the encoding's
-- products are compared with.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.WireForms where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ᵍ)
open import Examples.Groups.Real-Clifford+CH.Soundness.Operators using (diag)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqᵇ ; eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Encoding using (View ; one ; two ; view)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The entries of the gate matrices, and δ on bits

-- √2 H = [[1 , 1] , [1 , −1]].
hval : Bool → Bool → 𝔽
hval true true = -1#
hval _    _    = 1#

δb-∷ : ∀ a b (x y : Bits n) → δb (a ∷ x) (b ∷ y) ≡ δ₁ a b * δb x y
δb-∷ true  true  x y = Eq.sym (*-identityˡ _)
δb-∷ false false x y = Eq.sym (*-identityˡ _)
δb-∷ true  false x y = Eq.sym (*-zeroˡ _)
δb-∷ false true  x y = Eq.sym (*-zeroˡ _)

δb-eqB : (x y : Bits n) → δb x y ≡ (if eqB x y then 1# else 0#)
δb-eqB []          []          = Eq.refl
δb-eqB (true ∷ x)  (true ∷ y)  = δb-eqB x y
δb-eqB (false ∷ x) (false ∷ y) = δb-eqB x y
δb-eqB (true ∷ x)  (false ∷ y) = Eq.refl
δb-eqB (false ∷ x) (true ∷ y)  = Eq.refl

------------------------------------------------------------------------
-- The forms

-- The sign of Z on wire p, and of CZ on wires p and p + 1.
zsgn czsgn : ℕ → Bits n → 𝔽
zsgn p x  = if lookupℕ p x then -1# else 1#
czsgn p x = if lookupℕ p x ∧ lookupℕ (suc p) x then -1# else 1#

-- √2 H on wire p: the Hadamard entry of the bits on p, when the other
-- bits agree.
hadWire : ℕ → Op (suc n)
hadWire p x y =
  if eqB (removeℕ p x) (removeℕ p y) then hval (lookupℕ p x) (lookupℕ p y) else 0#

-- √2 CH on wires p (target) and p + 1 (control).
chWire : ℕ → Op (suc n)
chWire p x y =
  if eqB (removeℕ p x) (removeℕ p y)
  then (if lookupℕ (suc p) x then hval (lookupℕ p x) (lookupℕ p y)
        else √2 * δ₁ (lookupℕ p x) (lookupℕ p y))
  else 0#

form : View (suc n) → Op (suc n)
form (one p H-gate)  = hadWire p
form (one p Z-gate)  = √2 · diag (zsgn p)
form (two p CZ-gate) = √2 · diag (czsgn p)
form (two p CH-gate) = chWire p

------------------------------------------------------------------------
-- Shifting a form up a wire

shift : View n → View (suc n)
shift (one p h) = one (suc p) h
shift (two p h) = two (suc p) h

view-↥ : (g : Gen n) → view (g ↥) ≡ shift (view g)
view-↥ g with view g
... | one p h = Eq.refl
... | two p h = Eq.refl

private
  -- The one-wire identity factor.
  δ₁-Id : ∀ a b → Idₒ {1} (a ∷ []) (b ∷ []) ≡ δ₁ a b
  δ₁-Id true  true  = Eq.refl
  δ₁-Id false false = Eq.refl
  δ₁-Id true  false = Eq.refl
  δ₁-Id false true  = Eq.refl

  -- if on a product: (if c then u else 0) = d * (if c then v else 0)
  -- when u = d * v.
  if-* : ∀ c d u v → u ≡ d * v → (if c then u else 0#) ≡ d * (if c then v else 0#)
  if-* true  d u v e = e
  if-* false d u v e = Eq.sym (*-zeroʳ d)

  ∧-if : ∀ a b (c′ : Bool) (u : 𝔽) →
         (if eqᵇ a b ∧ c′ then u else 0#) ≡ δ₁ a b * (if c′ then u else 0#)
  ∧-if true  true  c′ u = Eq.sym (*-identityˡ _)
  ∧-if false false c′ u = Eq.sym (*-identityˡ _)
  ∧-if true  false c′ u = Eq.sym (*-zeroˡ _)
  ∧-if false true  c′ u = Eq.sym (*-zeroˡ _)

hadWire-suc : ∀ p a b (x y : Bits (suc n)) →
              hadWire (suc p) (a ∷ x) (b ∷ y) ≡ δ₁ a b * hadWire p x y
hadWire-suc p a b (c ∷ x) (d ∷ y) = ∧-if a b _ _

chWire-suc : ∀ p a b (x y : Bits (suc n)) →
             chWire (suc p) (a ∷ x) (b ∷ y) ≡ δ₁ a b * chWire p x y
chWire-suc p a b (c ∷ x) (d ∷ y) = ∧-if a b _ _

zsgn-suc : ∀ p a (x : Bits n) → zsgn (suc p) (a ∷ x) ≡ zsgn p x
zsgn-suc p a x = Eq.refl

czsgn-suc : ∀ p a (x : Bits n) → czsgn (suc p) (a ∷ x) ≡ czsgn p x
czsgn-suc p a x = Eq.refl

-- A shifted form is the identity on the new wire times the form.
up-form : (v : View (suc n)) → up (form v) ≐ form (shift v)
up-form (one p H-gate) (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* hadWire p x y) (δ₁-Id a b)) (Eq.sym (hadWire-suc p a b x y))
up-form (two p CH-gate) (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* chWire p x y) (δ₁-Id a b)) (Eq.sym (chWire-suc p a b x y))
up-form (one p Z-gate) (a ∷ x) (b ∷ y) = begin
  Idₒ (a ∷ []) (b ∷ []) * (√2 * (zsgn p x * δb x y))
    ≡⟨ Eq.cong (_* (√2 * (zsgn p x * δb x y))) (δ₁-Id a b) ⟩
  δ₁ a b * (√2 * (zsgn p x * δb x y))
    ≡⟨ shuffle (δ₁ a b) √2 (zsgn p x) (δb x y) ⟩
  √2 * (zsgn p x * (δ₁ a b * δb x y))
    ≡⟨ Eq.cong (λ v → √2 * (zsgn p x * v)) (Eq.sym (δb-∷ a b x y)) ⟩
  √2 * (zsgn p x * δb (a ∷ x) (b ∷ y)) ∎
  where
  open Eq.≡-Reasoning
  shuffle : ∀ d s z e → d * (s * (z * e)) ≡ s * (z * (d * e))
  shuffle d s z e = begin
    d * (s * (z * e))   ≡⟨ *-comm d _ ⟩
    (s * (z * e)) * d   ≡⟨ *-assoc s (z * e) d ⟩
    s * ((z * e) * d)   ≡⟨ Eq.cong (s *_) (*-assoc z e d) ⟩
    s * (z * (e * d))   ≡⟨ Eq.cong (λ v → s * (z * v)) (*-comm e d) ⟩
    s * (z * (d * e))   ∎
up-form (two p CZ-gate) (a ∷ x) (b ∷ y) = begin
  Idₒ (a ∷ []) (b ∷ []) * (√2 * (czsgn p x * δb x y))
    ≡⟨ Eq.cong (_* (√2 * (czsgn p x * δb x y))) (δ₁-Id a b) ⟩
  δ₁ a b * (√2 * (czsgn p x * δb x y))
    ≡⟨ shuffle (δ₁ a b) √2 (czsgn p x) (δb x y) ⟩
  √2 * (czsgn p x * (δ₁ a b * δb x y))
    ≡⟨ Eq.cong (λ v → √2 * (czsgn p x * v)) (Eq.sym (δb-∷ a b x y)) ⟩
  √2 * (czsgn p x * δb (a ∷ x) (b ∷ y)) ∎
  where
  open Eq.≡-Reasoning
  shuffle : ∀ d s z e → d * (s * (z * e)) ≡ s * (z * (d * e))
  shuffle d s z e = begin
    d * (s * (z * e))   ≡⟨ *-comm d _ ⟩
    (s * (z * e)) * d   ≡⟨ *-assoc s (z * e) d ⟩
    s * ((z * e) * d)   ≡⟨ Eq.cong (s *_) (*-assoc z e d) ⟩
    s * (z * (e * d))   ≡⟨ Eq.cong (λ v → s * (z * v)) (*-comm e d) ⟩
    s * (z * (d * e))   ∎

------------------------------------------------------------------------
-- The operator of a generator is the form of its view

private
  -- The entries of the stored gate matrices, case by case (the
  -- semantics keeps the entry functions private, so each case is one
  -- evaluation).
  hM-ix : ∀ a b → ix hM (a ∷ []) (b ∷ []) ≡ hval a b
  hM-ix true true = Eq.refl
  hM-ix true false = Eq.refl
  hM-ix false true = Eq.refl
  hM-ix false false = Eq.refl

  zM-ix : ∀ a b → ix zM (a ∷ []) (b ∷ []) ≡ √2 * (zsgn {1} 0 (a ∷ []) * δ₁ a b)
  zM-ix true true = Eq.refl
  zM-ix true false = Eq.refl
  zM-ix false true = Eq.refl
  zM-ix false false = Eq.refl

  czM-ix : ∀ a a′ b b′ → ix czM (a ∷ a′ ∷ []) (b ∷ b′ ∷ []) ≡
           √2 * (czsgn {2} 0 (a ∷ a′ ∷ []) * δb (a ∷ a′ ∷ []) (b ∷ b′ ∷ []))
  czM-ix true true true true = Eq.refl
  czM-ix true true true false = Eq.refl
  czM-ix true true false true = Eq.refl
  czM-ix true true false false = Eq.refl
  czM-ix true false true true = Eq.refl
  czM-ix true false true false = Eq.refl
  czM-ix true false false true = Eq.refl
  czM-ix true false false false = Eq.refl
  czM-ix false true true true = Eq.refl
  czM-ix false true true false = Eq.refl
  czM-ix false true false true = Eq.refl
  czM-ix false true false false = Eq.refl
  czM-ix false false true true = Eq.refl
  czM-ix false false true false = Eq.refl
  czM-ix false false false true = Eq.refl
  czM-ix false false false false = Eq.refl

  chM-ix : ∀ a a′ b b′ → ix chM (a ∷ a′ ∷ []) (b ∷ b′ ∷ []) ≡
           (if eqᵇ a′ b′ then (if a′ then hval a b else √2 * δ₁ a b) else 0#)
  chM-ix true true true true = Eq.refl
  chM-ix true true true false = Eq.refl
  chM-ix true true false true = Eq.refl
  chM-ix true true false false = Eq.refl
  chM-ix true false true true = Eq.refl
  chM-ix true false true false = Eq.refl
  chM-ix true false false true = Eq.refl
  chM-ix true false false false = Eq.refl
  chM-ix false true true true = Eq.refl
  chM-ix false true true false = Eq.refl
  chM-ix false true false true = Eq.refl
  chM-ix false true false false = Eq.refl
  chM-ix false false true true = Eq.refl
  chM-ix false false true false = Eq.refl
  chM-ix false false false true = Eq.refl
  chM-ix false false false false = Eq.refl

  -- The forms at wire 0.
  hadWire-0 : ∀ a b (x y : Bits n) → hadWire 0 (a ∷ x) (b ∷ y) ≡ hval a b * δb x y
  hadWire-0 a b x y with eqB x y in eq
  ... | true  = Eq.sym (Eq.trans (Eq.cong (hval a b *_) (Eq.trans (δb-eqB x y) (Eq.cong (λ c → if c then 1# else 0#) eq))) (*-identityʳ _))
  ... | false = Eq.sym (Eq.trans (Eq.cong (hval a b *_) (Eq.trans (δb-eqB x y) (Eq.cong (λ c → if c then 1# else 0#) eq))) (*-zeroʳ _))

  chWire-0 : ∀ a a′ b b′ (x y : Bits n) → chWire 0 (a ∷ a′ ∷ x) (b ∷ b′ ∷ y) ≡
             (if eqᵇ a′ b′ then (if a′ then hval a b else √2 * δ₁ a b) else 0#) * δb x y
  chWire-0 a a′ b b′ x y with eqᵇ a′ b′ | eqB x y in eq
  ... | true  | true  = Eq.sym (Eq.trans (Eq.cong (_ *_) (Eq.trans (δb-eqB x y) (Eq.cong (λ c → if c then 1# else 0#) eq))) (*-identityʳ _))
  ... | true  | false = Eq.sym (Eq.trans (Eq.cong (_ *_) (Eq.trans (δb-eqB x y) (Eq.cong (λ c → if c then 1# else 0#) eq))) (*-zeroʳ _))
  ... | false | _     = Eq.sym (*-zeroˡ _)

  -- Regrouping √2 * (s * δ) * δ′.
  regroup : ∀ (s d d′ : 𝔽) → (√2 * (s * d)) * d′ ≡ √2 * (s * (d * d′))
  regroup s d d′ = Eq.trans (*-assoc √2 (s * d) d′) (Eq.cong (√2 *_) (*-assoc s d d′))

gen-form : (g : Gen (suc n)) → ⟦ g ⟧ᵍ ≐ form (view g)
gen-form (gate₀ ())
gen-form H-gen (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* δb x y) (hM-ix a b)) (Eq.sym (hadWire-0 a b x y))
gen-form Z-gen (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* δb x y) (zM-ix a b))
    (Eq.trans (regroup (zsgn 0 (a ∷ [])) (δ₁ a b) (δb x y))
      (Eq.cong (λ v → √2 * (zsgn 0 (a ∷ x) * v)) (Eq.sym (δb-∷ a b x y))))
gen-form CZ-gen (a ∷ a′ ∷ x) (b ∷ b′ ∷ y) =
  Eq.trans (Eq.cong (_* δb x y) (czM-ix a a′ b b′))
    (Eq.trans (regroup (czsgn 0 (a ∷ a′ ∷ [])) (δb (a ∷ a′ ∷ []) (b ∷ b′ ∷ [])) (δb x y))
      (Eq.cong (λ v → √2 * (czsgn 0 (a ∷ a′ ∷ x) * v)) (Eq.sym (δb-split a a′ b b′ x y))))
  where
  δb-split : ∀ a a′ b b′ (x y : Bits n) → δb (a ∷ a′ ∷ x) (b ∷ b′ ∷ y) ≡ δb (a ∷ a′ ∷ []) (b ∷ b′ ∷ []) * δb x y
  δb-split a a′ b b′ x y = begin
    δb (a ∷ a′ ∷ x) (b ∷ b′ ∷ y)
      ≡⟨ δb-∷ a b (a′ ∷ x) (b′ ∷ y) ⟩
    δ₁ a b * δb (a′ ∷ x) (b′ ∷ y)
      ≡⟨ Eq.cong (δ₁ a b *_) (δb-∷ a′ b′ x y) ⟩
    δ₁ a b * (δ₁ a′ b′ * δb x y)
      ≡⟨ Eq.sym (*-assoc (δ₁ a b) (δ₁ a′ b′) (δb x y)) ⟩
    (δ₁ a b * δ₁ a′ b′) * δb x y
      ≡⟨ Eq.cong (_* δb x y) (Eq.sym (Eq.trans (δb-∷ a b (a′ ∷ []) (b′ ∷ [])) (Eq.cong (δ₁ a b *_) (Eq.trans (δb-∷ a′ b′ [] []) (*-identityʳ _))))) ⟩
    δb (a ∷ a′ ∷ []) (b ∷ b′ ∷ []) * δb x y ∎
    where open Eq.≡-Reasoning
gen-form CH-gen (a ∷ a′ ∷ x) (b ∷ b′ ∷ y) =
  Eq.trans (Eq.cong (_* δb x y) (chM-ix a a′ b b′)) (Eq.sym (chWire-0 a a′ b b′ x y))
gen-form {zero}   (gate₀ () ↥)
gen-form {suc n′} (g ↥) =
  ≐-trans (up-cong (gen-form g))
    (≐-trans (up-form (view g))
      (Eq.subst (λ v → form (shift (view g)) ≐ form v) (Eq.sym (view-↥ g)) (≐-refl _)))
