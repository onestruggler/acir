------------------------------------------------------------------------
-- Presentations of groups
--
-- A register of ancillas prepared in |0⟩
--
-- PathSum.Ancilla prepares one qubit in |0⟩: ξ ≋[ i ]₀ ζ compares ξ
-- and ζ on the inputs with x_i = 0, and set0 i ξ reads that input as
-- the constant 0.  The hidden shift algorithm of Amy's section 5.2
-- prepares whole registers in |0⟩ -- every qubit in figure 3(a), the
-- data register in figure 3(b) -- and its specifications, |0⟩ ↦ |s⟩
-- and |0⟩|s⟩ ↦ |s⟩|s⟩, concern only those inputs.  Here the prepared
-- qubits are the ones a mask c : Fin n → Bool marks, and
--
--    ξ ≋⟨ c ⟩₀ ζ  ⇔  ∀ x z, x_i = 0 for every marked i →
--                    the entries of ξ and ζ from x to z agree
--                    (after normalisation).
--
-- set0ᶜ c ξ substitutes 0 for every marked input in the polynomials,
-- which is how the paper computes the path-sum of a circuit with
-- constant inputs.  At every input it has ξ's column at that input with
-- the marked bits cleared (amp-set0ᶜ), so an equivalence proved of it
-- holds of ξ on the prepared inputs (set0ᶜ-≋), and conversely when ζ
-- does not read the marked inputs (≋⟨⟩₀-set0ᶜ).  Marking a single wire
-- gives back PathSum.Ancilla's relation (≋[]₀⇔≋⟨only⟩₀).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ancilla.Register (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

import Data.Fin.Properties as Fin

open import PathSum.Ancilla M₀ using (_≋[_]₀_)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Compose.Properties M₀ using (hits-outBit)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using (_≐_; Σᴮ-cong; scale; scale-map)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_; hits-≗³)
open import PathSum.Polynomial using (Poly; Var; x[_]; y[_]; 0ᴾ; μ; eval)
open import PathSum.Polynomial.Bind using (bind; eval-bind; odd)
open import PathSum.Polynomial.Product using (eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using (valᵛ; eval-cong)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Prepared inputs

-- The inputs whose marked bits are all 0.

Prepared : (Fin n → Bool) → Assign n → Set
Prepared c x = ∀ i → c i ≡ true → x i ≡ false

-- Clearing the marked bits prepares any input, and changes nothing in
-- a prepared one.

mask : (Fin n → Bool) → Assign n → Assign n
mask c x i = if c i then false else x i

mask-prepared : (c : Fin n → Bool) (x : Assign n) → Prepared c (mask c x)
mask-prepared c x i ci = cong (λ b → if b then false else x i) ci

mask-id : (c : Fin n → Bool) (x : Assign n) → Prepared c x →
          ∀ i → mask c x i ≡ x i
mask-id c x p i = go (c i) refl
  where
  go : ∀ b → c i ≡ b → (if c i then false else x i) ≡ x i
  go true  e = trans (cong (λ b → if b then false else x i) e) (sym (p i e))
  go false e = cong (λ b → if b then false else x i) e


------------------------------------------------------------------------
-- Setting the marked inputs to 0

zeroᶜ : (Fin n → Bool) → Var n m → Poly n m
zeroᶜ c x[ i ] = if c i then 0ᴾ else μ x[ i ]
zeroᶜ c y[ j ] = μ y[ j ]

set0ᶜ : (Fin n → Bool) → PathSum n k m → PathSum n k m
set0ᶜ c ξ = ⟨ bind (phase ξ) (zeroᶜ c) , (λ w → bind (out ξ w) (zeroᶜ c)) ⟩

-- Its polynomials take, at x, the values the original ones take at x
-- with the marked bits cleared.

eval-set0ᶜ : (c : Fin n → Bool) (P : Poly n m) (x : Assign n) (y : Assign m) →
             eval (bind P (zeroᶜ c)) x y ≡ eval P (mask c x) y
eval-set0ᶜ c P x y = eval-bind P (zeroᶜ c) x y (mask c x) y value
  where
  pick : ∀ i b → eval (if b then 0ᴾ else μ x[ i ]) x y ≡
                 [ (if b then false else x i) ]ᶻ
  pick i true  = eval-0ᴾ x y
  pick i false = eval-μᴾ x[ i ] x y

  value : ∀ v → eval (zeroᶜ c v) x y ≡ [ valᵛ v (mask c x) y ]ᶻ
  value x[ i ] = pick i (c i)
  value y[ j ] = eval-μᴾ y[ j ] x y

-- So are its amplitudes.

amp-set0ᶜ : (c : Fin n → Bool) (ξ : PathSum n k m) (x z : Assign n) →
            amp (set0ᶜ c ξ) x z ≐ amp ξ (mask c x) z
amp-set0ᶜ c ξ x z = Σᴮ-cong (λ y → if-cong
  (hits-outBit (set0ᶜ c ξ) ξ x (mask c x) y y z
               (λ w → cong odd (eval-set0ᶜ c (out ξ w) x y)))
  (zpow-≡ (eval-set0ᶜ c (phase ξ) x y)))

-- Amplitudes read the input only through its values.

amp-input : (ξ : PathSum n k m) {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
            ∀ z → amp ξ x z ≐ amp ξ x′ z
amp-input ξ {x} {x′} h z = Σᴮ-cong (λ y → if-cong
  (hits-≗³ ξ {x} {x′} {y} {y} {z} {z} h (λ _ → refl) (λ _ → refl))
  (zpow-≡ (eval-cong (phase ξ) {x} {x′} {y} {y} h (λ _ → refl))))


------------------------------------------------------------------------
-- Equivalence on the prepared inputs

infix 4 _≋⟨_⟩₀_

_≋⟨_⟩₀_ : PathSum n k m → (Fin n → Bool) → PathSum n k′ m′ → Set
_≋⟨_⟩₀_ {k = k} {k′ = k′} ξ c ζ =
  ∀ x z → Prepared c x → scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)

-- Full equivalence implies it.

≋⇒≋⟨⟩₀ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} (c : Fin n → Bool) →
         ξ ≋ ζ → ξ ≋⟨ c ⟩₀ ζ
≋⇒≋⟨⟩₀ c eq x z _ = eq x z

-- What is proved of the path-sum with the register set to 0 holds of
-- the path-sum on prepared inputs.

set0ᶜ-≋ : (c : Fin n → Bool) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
          set0ᶜ c ξ ≋ ζ → ξ ≋⟨ c ⟩₀ ζ
set0ᶜ-≋ {k′ = k′} c ξ ζ eq x z p j = trans
  (scale-map k′ (λ l → trans (amp-input ξ (λ i → sym (mask-id c x p i)) z l)
                             (sym (amp-set0ᶜ c ξ x z l))) j)
  (eq x z j)

-- And conversely, against a ζ that does not read the marked inputs.

≋⟨⟩₀-set0ᶜ : (c : Fin n → Bool) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
             ξ ≋⟨ c ⟩₀ ζ → (∀ x z → amp ζ (mask c x) z ≐ amp ζ x z) →
             set0ᶜ c ξ ≋ ζ
≋⟨⟩₀-set0ᶜ {k = k} {k′ = k′} c ξ ζ eq h x z j = trans
  (scale-map k′ (amp-set0ᶜ c ξ x z) j)
  (trans (eq (mask c x) z (mask-prepared c x) j) (scale-map k (h x z) j))


------------------------------------------------------------------------
-- One ancilla

-- The mask of the single wire i.

only : Fin n → (Fin n → Bool)
only i j = ⌊ j Fin.≟ i ⌋

private
  only-self : (i : Fin n) → only i i ≡ true
  only-self i with i Fin.≟ i
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  only-eq : (i j : Fin n) → only i j ≡ true → j ≡ i
  only-eq i j e with j Fin.≟ i
  ... | yes p = p
  ... | no  _ = contradiction e λ ()

≋[]₀⇔≋⟨only⟩₀ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} (i : Fin n) →
                (ξ ≋[ i ]₀ ζ) ⇔ (ξ ≋⟨ only i ⟩₀ ζ)
≋[]₀⇔≋⟨only⟩₀ i = mk⇔
  (λ h x z p → h x z (p i (only-self i)))
  (λ h x z x₀ → h x z (λ j e → subst (λ t → x t ≡ false)
                                      (sym (only-eq i j e)) x₀))
